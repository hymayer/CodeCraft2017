
#include "../include/gurobi_c++.h"

#include <iostream>
#include <sstream>

#define GUROBI_VERSION  70
#define GUROBI_LATEST_VERSION  70

#define VISUAL_STUDIO_VERSION  2015

#pragma comment(lib, "../lib/gurobi_c++md2015")
#pragma comment(lib, "../lib/gurobi70")

using namespace std;

namespace cdn {

    template<class TYPE>
    string ToStr(TYPE i)
    {
        stringstream s;
        s << i;
        return s.str();
    }

    struct Instance
    {
        Instance(const string& strFile)
            : nodes(0)
            , edges(0)
            , consumers(0)
            , server_cost(0)
            , capacity(NULL)
            , cost(NULL)
            , node_cost(NULL)
            , server_req(NULL)
            , server_conn(NULL)
            , connect_consumer(NULL)
            , connect_consumer_req(NULL)
            , linked_edges(NULL)
            , server_level_num(0)
        {
            ifstream infile(strFile.c_str());

            if (infile.is_open())
            {
                string strLine;

                // line 1
                getline(infile, strLine, '\n');
                size_t iPos = strLine.find(' ');
                nodes = atoi(strLine.substr(0, iPos).c_str());
                size_t iPos1 = strLine.find(' ', iPos + 1);
                edges = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                consumers = atoi(strLine.substr(iPos1 + 1).c_str());

                // line 2 -- empty
                getline(infile, strLine, '\n');

                int ser_seq, ser_cap, ser_cost;
                getline(infile, strLine, '\n');
                while (strLine != "\n")
                {
                    iPos = strLine.find(' ');
                    if (iPos == string::npos)break;
                    ser_seq = atoi(strLine.substr(0, iPos).c_str());
                    iPos1 = strLine.find(' ', iPos + 1);
                    ser_cap = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                    ser_cost = atoi(strLine.substr(iPos1 + 1).c_str());
                    mvec_server_type.push_back(make_pair(ser_cap, ser_cost));

                    //cout << ser_seq << " " << ser_cap << " " << ser_cost << endl;
                    getline(infile, strLine, '\n');
                }

                server_level_num = (int)mvec_server_type.size();

                if (AllocMemory() != 0)
                {
                    assert(false);
                }

                int node_seq_, node_cost_;
                for (int i = 0; i < nodes; i++)
                {
                    getline(infile, strLine, '\n');
                    iPos = strLine.find(' ');
                    node_seq_ = atoi(strLine.substr(0, iPos).c_str());
                    node_cost_ = atoi(strLine.substr(iPos + 1).c_str());
                    node_cost[node_seq_] = node_cost_;

                    //cout << node_seq_ << " " << node_cost_ << endl;
                }

                // line -- empty
                getline(infile, strLine, '\n');

                // network
                int start, stop, band, cost_;
                size_t iPos2;
                for (int i = 0; i < edges; i++)
                {
                    getline(infile, strLine, '\n');
                    iPos = strLine.find(' ');
                    start = atoi(strLine.substr(0, iPos).c_str());
                    iPos1 = strLine.find(' ', iPos + 1);
                    stop = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                    iPos2 = strLine.find(' ', iPos1 + 1);
                    band = atoi(strLine.substr(iPos1 + 1, iPos2).c_str());
                    cost_ = atoi(strLine.substr(iPos2 + 1).c_str());

                    capacity[start][stop] = capacity[stop][start] = band;
                    cost[start][stop] = cost[stop][start] = cost_;

                    linked_edges[start]++;
                    linked_edges[stop]++;

                    //cout << start << " " << stop << " " << band << " " << cost_ << endl;
                }

                // empty line
                getline(infile, strLine, '\n');
                //assert(strLine == "");

                // consumer network
                int consid, cons_c, req;

                for (int i = 0; i < consumers; i++)
                {
                    getline(infile, strLine, '\n');
                    iPos = strLine.find(' ');
                    consid = atoi(strLine.substr(0, iPos).c_str());
                    iPos1 = strLine.find(' ', iPos + 1);
                    cons_c = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                    req = atoi(strLine.substr(iPos1 + 1).c_str());

                    server_conn[consid] = cons_c;
                    server_req[consid] = req;
                    connect_consumer[cons_c] = consid;
                    connect_consumer_req[cons_c] = req;

                    //cout << consid << " " << cons_c << " " << req << endl;
                }

                infile.close();

                // 构造转化问题
                addReqEdges();
                addSourceEdges();

                // 汇点到源点的带宽
                capacity[nodes + 1 + server_level_num][nodes] = INT_MAX;
            }
            else
            {
                assert(false);
            }
        }

        ~Instance()
        {
            FreeMemory();
        }

        int AllocMemory()
        {
            server_req = new int[consumers];
            server_conn = new int[consumers];

            capacity = new int*[nodes + 2 + server_level_num];
            cost = new int*[nodes + 2 + server_level_num];

            node_cost = new int[nodes];
            connect_consumer = new int[nodes];
            connect_consumer_req = new int[nodes];
            linked_edges = new int[nodes];

            if (server_req == NULL || server_conn == NULL || capacity == NULL ||
                cost == NULL || node_cost == NULL || connect_consumer == NULL || linked_edges == NULL)
            {
                return -1;
            }

            for (int i = 0; i < nodes + 2 + server_level_num; i++)
            {
                capacity[i] = new int[nodes + 2 + server_level_num];
                cost[i] = new int[nodes + 2 + server_level_num];
                if (capacity[i] == NULL || cost[i] == NULL)
                {
                    return -1;
                }

                for (int j = 0; j < nodes + 2 + server_level_num; j++)
                {
                    capacity[i][j] = 0;
                    cost[i][j] = 0;
                }
            }

            for (int i = 0; i < nodes; i++)
            {
                node_cost[i] = 0;
                connect_consumer[i] = -1;
                connect_consumer_req[i] = 0;
                linked_edges[i] = 0;
            }

            for (int i = 0; i < consumers; i++)
            {
                server_conn[i] = 0;
                server_req[i] = 0;
            }

            return 0;
        }

        void FreeMemory()
        {
            if (server_req != NULL)
            {
                delete[] server_req;
                server_req = NULL;
            }

            if (server_conn != NULL)
            {
                delete[] server_conn;
                server_conn = NULL;
            }

            if (capacity != NULL)
            {
                for (int i = 0; i < nodes + 2 + server_level_num; ++i)
                {
                    delete[] capacity[i];
                    capacity[i] = NULL;
                }
                capacity = NULL;
            }

            if (cost != NULL)
            {
                for (int i = 0; i < nodes + 2 + server_level_num; ++i)
                {
                    delete[] cost[i];
                    cost[i] = NULL;
                }
                cost = NULL;
            }

            if (node_cost != NULL)
            {
                delete[] node_cost;
                node_cost = NULL;
            }

            if (connect_consumer != NULL)
            {
                delete[] connect_consumer;
                connect_consumer = NULL;
            }

            if (connect_consumer_req != NULL)
            {
                delete[] connect_consumer_req;
                connect_consumer_req = NULL;
            }

            if (linked_edges != NULL)
            {
                delete[] linked_edges;
                linked_edges = NULL;
            }
        }

        // nodes代表超级源, nodes+1代表中继, nodes+2代办超级汇
        void addReqEdges()
        {
            for (int i=0; i<consumers; ++i)
            {
                int cur_conn = server_conn[i];

                capacity[cur_conn][nodes + server_level_num + 1] = server_req[i];
            }
        }

        void addSourceEdges()
        {
            // 对每个中继,使其和源点相连,和其他网络结点相连
            for (int i = 0; i < server_level_num; ++i)
            {
                // 和源结点
                capacity[nodes][nodes + 1 + i] = INT_MAX;

                // 和其他网络结点（非源非汇）
                for (int j = 0; j < nodes; ++j)
                {
                    capacity[nodes + 1 + i][j] = mvec_server_type[i].first;
                    cost[nodes + 1 + i][j] = mvec_server_type[i].second;
                }
            }
        }

        int nodes;
        int edges;
        int consumers;
        int server_cost;

        int ** capacity;
        int ** cost;

        int * node_cost;

        // 数组长度为消费节点的个数
        int * server_req;            // 消费结点带宽需求,数组下标为消费结点ID
        int * server_conn;           // 消费结点连接网络结点的映射,数组下标为消费结点ID

                                     // 数组长度为网络节点的个数
        int * connect_consumer;      // 和消费节点相连的网络节点
        int * connect_consumer_req;  // 和消费节点相连的网络节点的带宽需求
        int * linked_edges;          // 每个网络结点相连的边数

        int server_level_num;
        vector<pair<int, int> > mvec_server_type;
    };

	int call_gurobi(Instance* ins, const string& strOutput)
	{
		try
		{
			GRBEnv env = GRBEnv();
			GRBModel model = GRBModel(env);

			int nNodes = ins->nodes;

            // 链路流量
			GRBVar **var_flow = NULL;

            // 中继结点到网络结点的边,值为1表示网络结点选择中继结点代表的档次为服务器
            GRBVar **var_build_server = NULL;

            var_flow = new GRBVar*[nNodes + 2 + ins->server_level_num];
            for (int i = 0; i < nNodes + 2 + ins->server_level_num; i++)
            {
                var_flow[i] = new GRBVar[nNodes + 2 + ins->server_level_num];
            }

            var_build_server = new GRBVar*[nNodes];
            for (int i = 0; i < nNodes; ++i)
            {
                var_build_server[i] = new GRBVar[ins->server_level_num];
            }

			for (int i = 0; i < nNodes + 2 + ins->server_level_num; ++i)
			{
				for (int j = 0; j < nNodes + 2 + ins->server_level_num; ++j)
				{
					var_flow[i][j] = model.addVar(0.0, GRB_INFINITY, 0.0, GRB_INTEGER, "flow_" + ToStr(i) + "_" + ToStr(j));
				}
			}

            for (int i = 0; i < nNodes; ++i)
            {
                for (int j = 0; j < ins->server_level_num; ++j)
                {
                    var_build_server[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY, "used_" + ToStr(i) + "_" + ToStr(j));
                }
            }

            //model.update();
			model.update();

            // 消费需求约束
            for (int i = 0; i < ins->consumers; ++i)
            {
                int cur_conn = ins->server_conn[i]; // 和消费结点相连的网络结点
                int cur_req = ins->server_req[i];  // 当前消费结点的需求

                GRBLinExpr req_expr = var_flow[cur_conn][ins->nodes + 1 + ins->server_level_num];//当前网络结点到汇的流量
                model.addConstr(req_expr >= cur_req, "req_" + ToStr(i));
            }

            // 带宽容量约束
            for (int i = 0; i < nNodes + 2 + ins->server_level_num; ++i)
            {
                for (int j = 0; j < nNodes + 2 + ins->server_level_num; ++j)
                {
                    model.addConstr(var_flow[i][j] <= ins->capacity[i][j], "xy_" + ToStr(i) + "_" + ToStr(j));
                }
            }

            // 节点流量平衡约束
            for (int i = 0; i < nNodes + 2 + ins->server_level_num; ++i)
            {
                GRBLinExpr flow_in_expr = 0;
                GRBLinExpr flow_out_expr = 0;
                for (int j = 0; j < nNodes + 2 + ins->server_level_num; ++j)
                {
                    flow_in_expr += var_flow[j][i];
                    flow_out_expr += var_flow[i][j];
                }

                model.addConstr(flow_in_expr == flow_out_expr, "bal_" + ToStr(i));
            }

            // 选择档次约束
            for (int i = 0; i < nNodes; ++i)
            {
                GRBLinExpr server_type_expr = 0;
                for (int j = 0; j < ins->server_level_num; ++j)
                {
                    server_type_expr += var_build_server[i][j];
                    model.addConstr(var_flow[nNodes + 1 + j][i] <= var_build_server[i][j]* 100000000, "select_ser_" + ToStr(i)+"_"+ToStr(j));
                }
                model.addConstr(server_type_expr <= 1, "select_ser_"+ToStr(i));
            }

            // 成本
            GRBLinExpr cost_ = 0;
            GRBLinExpr server_cost_ = 0;
            for (int i = 0; i < nNodes; ++i)
            {
                // 服务器建设成本
                for (int j = 0; j < ins->server_level_num; ++j)
                {
                    server_cost_ += var_build_server[i][j] * (ins->cost[nNodes + 1 + j][i] + ins->node_cost[i]);
                }

                // 链路流量成本
                for (int j = 0; j < nNodes; ++j)
                {
                    cost_ += var_flow[i][j] * ins->cost[i][j];
                }
            }
            cost_ += server_cost_;

            model.setObjective(cost_, GRB_MINIMIZE);

			// Optimize model
			model.optimize();
			int status = model.get(GRB_IntAttr_Status);

			// Output result
            ofstream out_file;
            out_file.open(strOutput.c_str());
            if (out_file.is_open())
            {
                for (int i = 0; i < nNodes; ++i)
                {
                    for (int j = 0; j < ins->server_level_num; ++j)
                    {
                        double choose = var_build_server[i][j].get(GRB_DoubleAttr_X);
                        if (choose > 0.0)
                        {
                            out_file << i << " " << j << "\n";
                        }
                    }
                }

                out_file << "\n";
                out_file << model.get(GRB_DoubleAttr_ObjVal) << "\n";
                out_file << "\n";

                for (int i=0; i<nNodes; ++i)
                {
                    for (int j=0; j<nNodes; ++j)
                    {
                        double flow_ = var_flow[i][j].get(GRB_DoubleAttr_X);
                        if (flow_ > 0.0)
                        {
                            out_file << i << " " << j << " " << flow_ << "\n";
                        }
                    }
                }

                out_file.close();
            }
            //cout << z.get(GRB_StringAttr_VarName) << " "
            //    << z.get(GRB_DoubleAttr_X) << endl;

			cout << "Obj: " << model.get(GRB_DoubleAttr_ObjVal) << endl;
		}
		catch (GRBException e)
		{
			cout << "Error code = " << e.getErrorCode() << endl;
			cout << e.getMessage() << endl;
		}
		catch (...)
		{
			cout << "Exception during optimization" << endl;
		}

		return 0;
	}
} // namespace cdn

int main(int argc, char* argv[])
{
    if (argc < 1)
    {
        cout << "Usage: " << argv[0] << " inst_file " << endl;
        return 0;
    }

    string strResult = "../testcases/Round3/Intermediate/case2.txt"; // argv[1];
    string strOutput = "r3_i2_gurobi_result.txt";

    cdn::Instance* ins = new cdn::Instance(strResult);
    if (ins == NULL)
    {
        return -1;
    }
 
    call_gurobi(ins, strOutput);

    return 0;
}