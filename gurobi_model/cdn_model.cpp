
#include "../include/gurobi_c++.h"

#include <iostream>
#include <fstream>
#include <sstream>
#include <cassert>
#include <climits>

#include <vector>
#include <set>

using namespace std;

#pragma comment(lib,"../lib/gurobi65.lib")
#pragma comment(lib,"../lib/gurobi_c++md2010.lib")

string ToStr(int i) {
    stringstream s;
    s << i;
    return s.str();
}

struct Instance {
    Instance(const string& strFile)
        : nodes(0)
        , edges(0)
        , consumers(0)
        , server_cost(0)
        , graph(NULL)
        , cost(NULL)
        , server_req(NULL)
        , server_conn(NULL)
        , connect_consumer(NULL)
        , connect_consumer_req(NULL)
        , linked_edges(NULL)
    {
        ifstream infile(strFile);

        if (infile.is_open())
        {
            string strLine;

            // line 1
            getline(infile, strLine, '\n');
            size_t iPos = strLine.find(' ');
            nodes = stoi(strLine.substr(0, iPos));
            size_t iPos1 = strLine.find(' ', iPos + 1);
            edges = stoi(strLine.substr(iPos + 1, iPos1));
            consumers = stoi(strLine.substr(iPos1 + 1));

            if (AllocMemory() != 0)
            {
                assert(false);
            }

            // line 2 -- empty
            getline(infile, strLine, '\n');

            // line 3
            getline(infile, strLine, '\n');
            server_cost = stoi(strLine);

            // line 4 -- empty
            getline(infile, strLine, '\n');

            // network
            int start, stop, band, cost_;
            size_t iPos2;
            for (int i = 0; i < edges; i++)
            {
                getline(infile, strLine, '\n');
                iPos = strLine.find(' ');
                start = stoi(strLine.substr(0, iPos));
                iPos1 = strLine.find(' ', iPos + 1);
                stop = stoi(strLine.substr(iPos + 1, iPos1));
                iPos2 = strLine.find(' ', iPos1 + 1);
                band = stoi(strLine.substr(iPos1 + 1, iPos2));
                cost_ = stoi(strLine.substr(iPos2 + 1));

                graph[start][stop] = graph[stop][start] = band;
                cost[start][stop] = cost[stop][start] = cost_;

                linked_edges[start]++;
                linked_edges[stop]++;

                //cout << start << " " << stop << " " << band << " " << cost << endl;
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
                consid = stoi(strLine.substr(0, iPos));
                iPos1 = strLine.find(' ', iPos + 1);
                cons_c = stoi(strLine.substr(iPos + 1, iPos1));
                req = stoi(strLine.substr(iPos1 + 1));

                server_conn[consid] = cons_c;
                server_req[consid] = req;
                connect_consumer[cons_c] = 1;
                connect_consumer_req[cons_c] = req;

                //cout << consid << " " << cons_c << " " << req << endl;
            }

            infile.close();
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

        graph = new int*[nodes + 2];
        cost = new int*[nodes + 2];

        connect_consumer = new int[nodes];
        connect_consumer_req = new int[nodes];
        linked_edges = new int[nodes];

        if (server_req == NULL || server_conn == NULL || graph == NULL || cost == NULL || connect_consumer == NULL || linked_edges == NULL)
        {
            return -1;
        }

        for (int i = 0; i < nodes + 2; i++)
        {
            graph[i] = new int[nodes + 2];
            cost[i] = new int[nodes + 2];
            if (graph[i] == NULL || cost[i] == NULL)
            {
                return -1;
            }

            for (int j = 0; j < nodes + 2; j++)
            {
                graph[i][j] = 0;
                cost[i][j] = 0;
            }
        }

        for (int i = 0; i < nodes; ++i)
        {
            connect_consumer[i] = 0;
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

        if (graph != NULL)
        {
            for (int i = 0; i < nodes + 2; ++i)
            {
                delete[] graph[i];
                graph[i] = NULL;
            }
            graph = NULL;
        }

        if (cost != NULL)
        {
            for (int i = 0; i < nodes + 2; ++i)
            {
                delete[] cost[i];
                cost[i] = NULL;
            }
            cost = NULL;
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

    void AddST()
    {
        for (int i=0; i<nodes; ++i)
        {
            graph[nodes][i] = INT_MAX;
            graph[i][nodes] = 0;
            cost[nodes][i] = server_cost;
            cost[i][nodes] = 0;
        }

        for (int i=0; i<consumers; ++i)
        {
            int cur_conn = server_conn[i];
            graph[cur_conn][nodes+1] = INT_MAX;
            cost[cur_conn][nodes+1] = 0;
            graph[nodes+1][cur_conn] = 0;
            cost[nodes+1][cur_conn] = 0;
        }
    }

    int nodes;
    int edges;
    int consumers;
    int server_cost;
    int ** graph;
    int ** cost;
    int * server_req;
    int * server_conn;

    int * connect_consumer;
    int * connect_consumer_req;

    int * linked_edges; // 相连的边数
};

int main(int argc, char* argv)
{

    try
    {
        if (argc < 1)
        {
            cout << "Usage: inst file " << endl;
            return 0;
        }

        string strInstFile = "example.txt";//argv[1];

        Instance* ins = new Instance(strInstFile);
        ins->AddST();

        GRBEnv env = GRBEnv();
        GRBModel model = GRBModel(env);

        int nNodes = ins->nodes;

        GRBVar **varsxy = NULL;
        GRBVar *var_y = NULL;

        varsxy = new GRBVar*[nNodes + 2];
        for (int i = 0; i <nNodes + 2; i++)
            varsxy[i] = new GRBVar[nNodes + 2];

        var_y = new GRBVar[nNodes];

        // var: x_ij, y_i
        for (int i = 0; i < nNodes + 2; ++i)
        {
            for (int j = 0; j < nNodes + 2; ++j)
            {
                varsxy[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_INTEGER, "x_" + ToStr(i) + "_y_" + ToStr(j));
            }
        }

        for (int i = 0; i < nNodes; ++i)
        {
            var_y[i] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY, "y_" + ToStr(i));
            varsxy[nNodes][i] = model.addVar(0.0, 1.0, 0.0, GRB_INTEGER, "s_x_" + ToStr(i));
            varsxy[i][nNodes] = model.addVar(0.0, 1.0, 0.0, GRB_INTEGER, "x_s_" + ToStr(i));
        }

        for (int i = 0; i < ins->consumers; ++i)
        {
            int cur_conn = ins->server_conn[i];
            varsxy[nNodes+1][cur_conn] = model.addVar(0.0, 1.0, 0.0, GRB_INTEGER, "s_x_" + ToStr(i));
            varsxy[cur_conn][nNodes+1] = model.addVar(0.0, 1.0, 0.0, GRB_INTEGER, "x_s_" + ToStr(i));
        }

        GRBVar z = model.addVar(0.0, GRB_INFINITY, 1.0, GRB_INTEGER, "z");

        model.update();
        model.update();

        model.setObjective(1.0 * z, GRB_MINIMIZE);

        GRBLinExpr yexpr = 0;
        for (int i = 0; i < nNodes; ++i)
        {
            GRBLinExpr tempexpr = varsxy[nNodes][i];
            yexpr += (1-var_y[i]) * ins->server_cost;
        }
        GRBLinExpr xyexpr = 0;
        for (int i = 0; i < nNodes; ++i)
        {
            for (int j = 0; j < nNodes; ++j)
            {
                xyexpr += varsxy[i][j] * ins->cost[i][j];
            }
        }

        yexpr += xyexpr;
        model.addConstr(yexpr == z, "z = x + sum_y");

        // 平衡约束
        for (int i = 0; i < nNodes; ++i)
        {
            GRBLinExpr xijexpr = 0;
            GRBLinExpr xjiexpr = 0;

            for (int j = 0; j < nNodes; ++j)
            {
                xijexpr += varsxy[i][j];
                xjiexpr += varsxy[j][i];
            }
            model.addConstr(xjiexpr == xijexpr, "xy_==yx_");
        }

        // 需求约束
        for (int i = 0; i < ins->consumers; ++i)
        {
            int cur_conn = ins->server_conn[i];
            GRBLinExpr disexpr = 0;
            
            disexpr = varsxy[cur_conn][nNodes+1];

            model.addConstr(disexpr >= ins->server_req[i], "f_" + ToStr(i));
        }

        // 带宽约束
        for (int i = 0; i < nNodes; ++i)
        {
            GRBLinExpr xijexpr = 0;

            for (int j = 0; j < nNodes; ++j)
            {

                xijexpr += varsxy[i][j];
                model.addConstr(xijexpr <= ins->graph[i][j], "xy_<=flow");
            }
        }

        // 服务器选择约束

        // Optimize model
        model.optimize();
        int status = model.get(GRB_IntAttr_Status);

        // Output result
        //cout << z.get(GRB_StringAttr_VarName) << " "
        //    << z.get(GRB_DoubleAttr_X) << endl;

        cout << "Obj: " << model.get(GRB_DoubleAttr_ObjVal) << endl;

        delete ins;
        ins = NULL;
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