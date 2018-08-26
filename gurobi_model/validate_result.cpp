
#include <ctime>
#include <set>
#include <queue>
#include <vector>
#include <climits>
#include <cassert>

#include <sstream>
#include <fstream>
#include <iostream>

#include <algorithm>

using namespace std;

typedef vector<double> RealVector;
typedef vector<bool> BoolVector;
typedef vector<int> IntVector;

typedef queue<int> IntQueue;

#ifndef LIMIT_CPU_TIME
#define LIMIT_CPU_TIME 85
#endif

#ifndef FIXED_TABU_LEN
#define FIXED_TABU_LEN 50
#endif

#define INVALID_NODE -1

//#define OUTPUT_STD_INFO
//#define OUTPUT_LOG_FILE

#ifdef OUTPUT_STD_INFO
#define OUTPUT_INFO(n) n
#else
#define OUTPUT_INFO(n)  
#endif

typedef enum
{
    CDN_OK = 0,
    CDN_ERROR,
    CDN_FIND_SERVER,
    CDN_FIND_SERVER_FAILED,
    CDN_LACK_FLOW,
    CDN_FIND_LACK_FLOW,
    CDN_NEED_DELETE_SERVER,
    CDN_SELECT_NONE,
    CDN_TIME_OUT
} cdnStatus;

typedef enum
{
    CRM_INST_MODE = 0,
    CRM_INIT_MODE,
    CRM_RUNNING_MODE,
    CRM_FINAL_MODE
} cdnRunningMode;

typedef enum
{
    CST_RANDOM = 0,
    CST_SERVER_LINKS,
    CST_TABU,
} cdnSearchType;

template<class TYPE>
string ToStr(TYPE i)
{
    stringstream s;
    s << i;
    return s.str();
}

struct Edge 
{
    Edge(int f, int t, int cap, int flow, int cost)
        : from(f)
        , to(t)
        , cap(cap)
        , flow(flow)
        , cost(cost)
    {}

    int from, to, cap, flow, cost;
};

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

            if (AllocMemory() != 0)
            {
                assert(false);
            }

            mvec_G.resize(nodes + 2);
            mvec_G_backup.resize(nodes + 2);

            // line 2 -- empty
            getline(infile, strLine, '\n');
            
            int ser_seq, ser_cap, ser_cost;
            getline(infile, strLine, '\n');
            while (strLine != "\n")
            {
                iPos = strLine.find(' ');
                if(iPos==string::npos)break;
                ser_seq = atoi(strLine.substr(0, iPos).c_str());
                iPos1 = strLine.find(' ', iPos + 1);
                ser_cap = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                ser_cost = atoi(strLine.substr(iPos1 + 1).c_str());
                mvec_server_type.push_back(make_pair(ser_cap, ser_cost));
                
                //cout << ser_seq << " " << ser_cap << " " << ser_cost << endl;
                getline(infile, strLine, '\n');
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

                addEdge(start, stop, band, cost_);

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

        capacity = new int*[nodes + 2];
        flow = new int *[nodes + 2];
        cost = new int*[nodes + 2];
        inc_cost = new int*[nodes + 2];
        bfs_node = new int*[nodes + 2];

        node_cost = new int[nodes];
        connect_consumer = new int[nodes];
        connect_consumer_req = new int[nodes];
        linked_edges = new int[nodes];

        if (server_req == NULL || server_conn == NULL || capacity == NULL ||
            flow == NULL || bfs_node == NULL || cost == NULL || inc_cost == NULL ||
            node_cost == NULL || connect_consumer == NULL || linked_edges == NULL)
        {
            return -1;
        }

        for (int i = 0; i < nodes + 2; i++)
        {
            capacity[i] = new int[nodes + 2];
            flow[i] = new int[nodes + 2];
            bfs_node[i] = new int[nodes + 2];
            cost[i] = new int[nodes + 2];
            inc_cost[i] = new int[nodes + 2];
            if (capacity[i] == NULL || flow[i] == NULL ||
                bfs_node[i] == NULL || cost[i] == NULL || inc_cost[i] == NULL)
            {
                return -1;
            }

            for (int j = 0; j < nodes + 2; j++)
            {
                capacity[i][j] = 0;
                flow[i][j] = 0;
                bfs_node[i][j] = 0;
                cost[i][j] = 0;
                inc_cost[i][j] = 0;
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
            for (int i = 0; i < nodes + 2; ++i)
            {
                delete[] capacity[i];
                capacity[i] = NULL;
            }
            capacity = NULL;
        }

        if (flow != NULL)
        {
            for (int i = 0; i < nodes + 2; ++i)
            {
                delete[] flow[i];
                flow[i] = NULL;
            }
            flow = NULL;
        }

        if (bfs_node != NULL)
        {
            for (int i = 0; i < nodes + 2; ++i)
            {
                delete[] bfs_node[i];
                bfs_node[i] = NULL;
            }
            flow = NULL;
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

        if (inc_cost != NULL)
        {
            for (int i = 0; i < nodes + 2; ++i)
            {
                delete[] inc_cost[i];
                inc_cost[i] = NULL;
            }
            inc_cost = NULL;
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

    void ResetFlow()
    {
        for (int i = 0; i < nodes; ++i)
        {
            for (int j = 0; j < nodes + 2; ++j)
            {
                flow[i][j] = 0;
            }
        }
    }

    void addEdge(int from, int to, int cap, int cost) 
    {
        int nsize;

        mvec_edges_backup.push_back(Edge(from, to, cap, 0, cost));  //正向边
        mvec_edges_backup.push_back(Edge(to, from, 0, 0, -cost));   //正向边对应的虚边
        nsize = (int)mvec_edges_backup.size();
        mvec_G_backup[from].push_back(nsize - 2);
        mvec_G_backup[to].push_back(nsize - 1);

        mvec_edges_backup.push_back(Edge(from, to, 0, 0, -cost));   //反向边
        mvec_edges_backup.push_back(Edge(to, from, cap, 0, cost));
        nsize = (int)mvec_edges_backup.size();
        mvec_G_backup[from].push_back(nsize - 2);
        mvec_G_backup[to].push_back(nsize - 1);
    }

    void addExtra(const IntVector& vec_servers, const IntVector& vec_level) 
    {   
        mvec_G.assign(mvec_G_backup.begin(), mvec_G_backup.end());
        mvec_edges.assign(mvec_edges_backup.begin(), mvec_edges_backup.end());

        //对消费点
        int t = nodes + 1;
        int nsize;
        for (int i = 0; i < consumers; i++) {
            mvec_edges.push_back(Edge(server_conn[i], t, server_req[i], 0, 0));
            mvec_edges.push_back(Edge(t, server_conn[i], 0, 0, 0));
            nsize = (int)mvec_edges.size();
            mvec_G[server_conn[i]].push_back(nsize - 2);
            mvec_G[t].push_back(nsize - 1);
        }

        //对服务点
        int s = nodes;
        for (size_t i = 0; i < vec_servers.size(); i++) {
            int upbound = mvec_server_type[vec_level[i]].first;
            mvec_edges.push_back(Edge(s, vec_servers[i], upbound, 0, 0));
            mvec_edges.push_back(Edge(vec_servers[i], s, 0, 0, 0));
            nsize = (int)mvec_edges.size();
            mvec_G[s].push_back(nsize - 2);
            mvec_G[vec_servers[i]].push_back(nsize - 1);
        }
    }

    int nodes;
    int edges;
    int consumers;
    int server_cost;

    int ** capacity;
    int ** flow;
    int ** bfs_node;  // 网络节点广度遍历时由近到远的节点集合
    int ** cost;
    int ** inc_cost;

    int * node_cost;

    // 数组长度为消费节点的个数
    int * server_req;            // 消费结点带宽需求,数组下标为消费结点ID
    int * server_conn;           // 消费结点连接网络结点的映射,数组下标为消费结点ID

    // 数组长度为网络节点的个数
    int * connect_consumer;      // 和消费节点相连的网络节点
    int * connect_consumer_req;  // 和消费节点相连的网络节点的带宽需求
    int * linked_edges;          // 每个网络结点相连的边数

    vector<pair<int, int> > mvec_server_type;

    vector<IntVector> mvec_G;
    vector<IntVector> mvec_G_backup;
    vector<Edge> mvec_edges;
    vector<Edge> mvec_edges_backup;
};

struct Solution
{
    Solution(Instance* ins)
        : ins(ins)
        , server_num(0)
        , best_cost(INT_MAX)
        , best_num_server(0)
        , mvec2_cur_sol(ins->nodes, false)
        , mvec2_nodes_ser_level(ins->nodes, -1)
    {
        inq = new bool[ins->nodes + 2];   //是否在队列中
        d = new int[ins->nodes + 2];      //相对距离
        pre = new int[ins->nodes + 2];    //弧
        a = new int[ins->nodes + 2];      //增量

        BfsTransEveryNode();
    }

    ~Solution()
    {

        delete[] inq;
        inq = NULL;
        delete[] d;
        d = NULL;
        delete[] pre;
        pre = NULL;
        delete[] a;
        a = NULL;
    }

    bool shortest_mincost(int s, int t, int& flow, int& cost, bool* inq, int*d, int* a, int* pre) 
    {
        for (int i = 0; i < ins->nodes + 2; i++) 
        {
            d[i] = INT_MAX;
            inq[i] = false;
        }

        d[s] = 0;
        a[s] = INT_MAX;
        pre[s] = 0;
        inq[s] = true;

        queue<int> Q;
        Q.push(s);

        while (!Q.empty()) 
        {
            int u = Q.front();
            Q.pop();
            inq[u] = false;
            for (size_t i = 0; i < ins->mvec_G[u].size(); i++) 
            {
                Edge& e = ins->mvec_edges[ins->mvec_G[u][i]];

                if (e.cap > e.flow && d[e.to] > d[u] + e.cost) 
                {
                    d[e.to] = d[u] + e.cost;
                    pre[e.to] = ins->mvec_G[u][i];
                    a[e.to] = min(a[u], e.cap - e.flow);
                    if (!inq[e.to]) 
                    {
                        Q.push(e.to);
                        inq[e.to] = true;
                    }
                }
            } //end for i
        } // end while

        if (d[t] == INT_MAX) 
        {
            return false;
        }

        flow += a[t];
        cost += d[t] * a[t];

        for (int u = t; u != s; u = ins->mvec_edges[pre[u]].from) 
        {
            ins->mvec_edges[pre[u]].flow += a[t];
            ins->mvec_edges[pre[u] ^ 1].flow -= a[t];
        }

        return true;
    }

    cdnStatus FindAllFlow_MinCost()
    {
        cdnStatus ret = CDN_OK;

        if (mvec2_servers.empty())
        {
            return CDN_ERROR;
        }

        // 连边
        ins->addExtra(mvec2_servers, mvec2_server_level);

        do 
        {
            int flow = 0;
            int cost = 0;
            while (shortest_mincost(ins->nodes, ins->nodes + 1, flow, cost, inq, d, a, pre));

            // is solution valid?
            // 只需判断到达消费节点的流量是否满足,链路带宽上限由算法保证
            for (int i = 0; i < ins->consumers; i++) {
                int cur_conn = ins->server_conn[i];
                int nsize = (int)ins->mvec_G[cur_conn].size();
                for (int j = nsize - 1; j >= 0; --j)
                {
                    Edge& eg = ins->mvec_edges[ins->mvec_G[cur_conn][j]];
                    if (eg.to == (ins->nodes+1) && eg.flow > 0)
                    {
                        if (eg.flow < ins->server_req[i])
                        {
                            return CDN_FIND_SERVER_FAILED;
                        } 
                        else
                        {
                            break;
                        }
                    }
                }
            }

            int cur_cost = 0;
            for (size_t i = 0; i < ins->nodes; ++i)
            {
                if (mvec2_cur_sol[i])
                {
                    cur_cost += ins->mvec_server_type[mvec2_nodes_ser_level[i]].second;
                    cur_cost += ins->node_cost[i];
                }
            }

            if (cur_cost + cost < best_cost)
            {
                for (int i = 0; i < ins->nodes + 2; ++i)
                {
                    for (int j = 0; j < ins->nodes + 2; ++j)
                    {
                        ins->inc_cost[i][j] = 0; // 记录最优流量
                    }
                }

                best_cost = cur_cost + cost;
                best_num_server = server_num;

                cout << "best cost: " << best_cost << endl;

                for (size_t i = 0; i < ins->mvec_edges.size(); ++i)
                {
                    Edge& eg = ins->mvec_edges[i];
                    if (eg.flow > 0)
                    {
                        ins->inc_cost[eg.from][eg.to] = eg.flow;
                        ins->flow[eg.from][eg.to] = eg.flow;
                    }
                }

                mvec2_servers_best.assign(mvec2_servers.begin(), mvec2_servers.end());
                mvec2_sol_best.assign(mvec2_cur_sol.begin(), mvec2_cur_sol.end());
                mvec2_G_best.assign(ins->mvec_G.begin(), ins->mvec_G.end());
                mvec2_edges_best.assign(ins->mvec_edges.begin(), ins->mvec_edges.end());
            }
        } while (false);

        return ret;
    }

    bool bfs3(int** Graph, int** rGraph, int s, int t, IntVector& parent)
    {
        BoolVector visited(ins->nodes + 2, false);
        queue <int> q;

        q.push(s);
        visited[s] = true;
        parent[s] = -1;

        while (!q.empty())
        {
            int u = q.front();
            q.pop();
            for (int v = 0; v < ins->nodes + 2; v++)
            {
                if (visited[v] == false && rGraph[u][v] > 0 && Graph[u][v] > 0)
                {
                    q.push(v);
                    parent[v] = u;
                    visited[v] = true;
                }
            }
        }

        return (visited[t] == true);
    }

    int fordFulkerson3(int** Graph, int** rGraph, int s, int t)
    {
        int u, v;

        IntVector parent(ins->nodes + 2, 0);
        int max_flow = 0;
        while (bfs3(Graph, rGraph, s, t, parent))
        {
            int path_flow = INT_MAX;
            IntVector vec_path;

            for (v = t; v != s; v = parent[v])
            {
                u = parent[v];
                path_flow = min(path_flow, rGraph[u][v]);
            }

            vec_path.push_back(path_flow);
            vec_path.push_back(ins->connect_consumer[parent[t]]);
            vec_path.push_back(-1);

            for (v = t; v != s; v = parent[v])
            {
                u = parent[v];
                if (u != ins->nodes)
                {
                    vec_path.push_back(u);
                }
                rGraph[u][v] -= path_flow;
                rGraph[v][u] += path_flow;
            }
            max_flow += path_flow;
            reverse(vec_path.begin(), vec_path.end());
            vec_path.push_back(mvec2_nodes_ser_level[vec_path[0]]);

            mvec_cur_paths.push_back(vec_path);
        }
        return max_flow;
    }

    void SetServers(const IntVector& vec_servers, const IntVector& vec_level)
    {
        mvec2_servers.assign(vec_servers.begin(), vec_servers.end());
        mvec2_server_level.assign(vec_level.begin(), vec_level.end());
        for (size_t i=0; i<vec_servers.size(); ++i)
        {
            mvec2_cur_sol[vec_servers[i]] = true;
            mvec2_nodes_ser_level[vec_servers[i]] = vec_level[i];
        }
        server_num = (int)vec_servers.size();
    }

    void GetResult(string& result)
    {
        if (best_cost == INT_MAX)
        {
            result = "NA\n";
        }
        else
        {
            result = "";
            result += ToStr(mvec_cur_paths.size());
            result += "\n\n";
            for (size_t i = 0; i < mvec_cur_paths.size(); ++i)
            {
                IntVector& vec_path = mvec_cur_paths[i];
                for (size_t j = 0; j < vec_path.size(); ++j)
                {
                    if (vec_path[j] >= 0)
                    {
                        result += ToStr(vec_path[j]);
                        if (j < vec_path.size() - 1)
                        {
                            result += " ";
                        }
                    }
                }

                if (i < mvec_cur_paths.size() - 1)
                {
                    result += "\n";
                }
            }
        }
    }

    void OutputLinkedEdges(const string& strfile)
    {
        ofstream output;
        output.open(strfile.c_str());
        if (output.is_open())
        {
            // 输出服务器类别及成本
            output << "servers\n";
            for (size_t i=0; i<ins->mvec_server_type.size(); ++i)
            {
                output << i << " " << ins->mvec_server_type[i].first << " " << ins->mvec_server_type[i].second << "\n";
            }
            output << "\n";
            
            // 输出连接边信息
            for (int i = 0; i < ins->nodes; ++i)
            {
                int len = ins->linked_edges[i];
                output << i;
                if (ins->connect_consumer[i] > -1)
                {
                    output << "(" << ins->node_cost[i] << ",S," << ins->connect_consumer[i] << "-" << ins->connect_consumer_req[i] << ")";
                }
                else
                {
                    output << "(" << ins->node_cost[i] << ")";
                }
                output << ": ";
                for (int j = 1; j <= len; ++j)
                {
                    output << ins->bfs_node[i][j] << "(";
                    if (ins->connect_consumer[ins->bfs_node[i][j]] > -1)
                    {
                        output << "S,";
                    }

                    output << ins->capacity[i][ins->bfs_node[i][j]]
                        << "," << ins->cost[i][ins->bfs_node[i][j]] << "," << ins->node_cost[ins->bfs_node[i][j]] << ") ";
                }
                output << "\n";
            }
            output.close();
        }
    }

    cdnStatus BFS(int start)
    {
        int index = 0;
        BoolVector vec_visited(ins->nodes, false);
        IntQueue q_node;
        q_node.push(start); // start是虚拟节点
        ins->bfs_node[start][index++] = start;
        vec_visited[start] = true;

        while (!q_node.empty())
        {
            int cur = q_node.front();
            q_node.pop();

            for (int i = 0; i < ins->nodes; ++i)
            {
                if (vec_visited[i] == false && ins->capacity[cur][i] > 0)
                {
                    q_node.push(i);
                    ins->bfs_node[start][index++] = i;
                    vec_visited[i] = true;
                }
            }
        }

        return CDN_OK;
    }

    cdnStatus BfsTransEveryNode()
    {
        cdnStatus ret = CDN_OK;

        for (int i = 0; i < ins->nodes; ++i)
        {
            BFS(i);
        }

        return ret;
    }

    cdnStatus Run(const IntVector& vecServers, const IntVector& vecLevel)
    {
        cdnStatus ret = CDN_OK;

        SetServers(vecServers, vecLevel);

        ins->addExtra(vecServers, vecLevel);

        ret = FindAllFlow_MinCost();

#if 0
        ofstream out_file;
        out_file.open("validator_result.txt");
        if (out_file.is_open())
        {
            for (int i = 0; i < ins->nodes; ++i)
            {
                for (int j = 0; j < ins->nodes; ++j)
                {
                    if (ins->inc_cost[i][j] > 0)
                    {
                        out_file << i << " " << j << " " << ins->inc_cost[i][j] << "\n";
                    }
                }
            }

            out_file.close();
        }
#endif

        mvec_cur_paths.clear();
        fordFulkerson3(ins->inc_cost, ins->inc_cost, ins->nodes, ins->nodes + 1);

        return CDN_OK;
    }

    cdnStatus ReadAndValidator(const string& strFile)
    {
        cdnStatus ret = CDN_OK;

        IntVector vec_ser_level(ins->nodes, -1);

        IntVector vec_server_;
        IntVector vec_level_;

        int all_cost = 0;

        int** flow_S = new int*[ins->nodes + 2];
        for (int i = 0; i < ins->nodes + 2; ++i)
        {
            flow_S[i] = new int[ins->nodes + 2];
            for (int j = 0; j < ins->nodes + 2; ++j)
            {
                flow_S[i][j] = 0;
            }
        }

        ifstream in_file;
        in_file.open(strFile.c_str());
        if (in_file.is_open())
        {
            string strLine;

            // line 1
            int ser_, level_;
            size_t iPos;
            getline(in_file, strLine, '\n');
            while (true)
            {
                iPos = strLine.find(' ');
                if (iPos == string::npos)break;

                ser_ = atoi(strLine.substr(0, iPos).c_str());
                level_ = atoi(strLine.substr(iPos + 1).c_str());

                if (vec_ser_level[ser_] == -1)
                {
                    vec_ser_level[ser_] = level_;

                    vec_server_.push_back(ser_);
                    vec_level_.push_back(level_);
                }
                else
                {
                    cout << ser_ << " - " << level_ << "\n";
                }

                getline(in_file, strLine, '\n');
            }

            SetServers(vec_server_, vec_level_);

            getline(in_file, strLine, '\n');
            all_cost = atoi(strLine.c_str());

            // empty line
            getline(in_file, strLine, '\n');

            int node1, node2, flow_;
            getline(in_file, strLine, '\n');
            while (true)
            {
                iPos = strLine.find(' ');
                if (iPos == string::npos)break;

                node1 = atoi(strLine.substr(0, iPos).c_str());
                size_t iPos1 = strLine.find(' ', iPos + 1);
                node2 = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                flow_ = atoi(strLine.substr(iPos1 + 1).c_str());

                flow_S[node1][node2] = flow_;

                getline(in_file, strLine, '\n');
            }

            in_file.close();
        }

        // validate
        int isvalid = true;
        IntVector vec_cons_flow(ins->nodes, 0);
        int real_cost = 0;
        for (int i = 0; i < ins->nodes; ++i)
        {
            for (int j = 0; j < ins->nodes; ++j)
            {
                if (flow_S[i][j] > ins->capacity[i][j])
                {
                    cout << "edge[" << i << "][" << j << "] exceed flow\n";
                    isvalid = false;
                }

                if (flow_S[i][j] > 0)
                {
                    real_cost += flow_S[i][j] * ins->cost[i][j];

                    // 是否和消费节点相连
                    if (ins->connect_consumer[j] > -1)
                    {
                        vec_cons_flow[j] += flow_S[i][j];
                    }
                }
            }
        }

        for (size_t i=0; i<vec_cons_flow.size(); ++i)
        {
            if (ins->connect_consumer[i] > -1)
            {
                if (vec_cons_flow[i] < ins->connect_consumer_req[i])
                {
                    if (mvec2_cur_sol[i])
                    {
                        int ser_cap = ins->mvec_server_type[mvec2_nodes_ser_level[i]].first;
                        int flow_out_ = 0;
                        int flow_in_ = 0;
                        for (int k = 0; k < ins->nodes; ++k)
                        {
                            flow_out_ += flow_S[i][k];
                            flow_in_ += flow_S[k][i];
                        }
                        if (ser_cap+flow_in_-flow_out_<ins->connect_consumer_req[i])
                        {
                            // 可以提供的减去已经流出去的,剩余流量如果不足于提供相连的服务器则非法
                            cout << "node[" << i << "], consumer[" << ins->connect_consumer[i] << "] lack flow ";
                            cout << ins->connect_consumer_req[i] - vec_cons_flow[i] << "\n";
                            isvalid = false;
                        }
                    }
                    else
                    {
                        cout << "node[" << i << "], consumer[" << ins->connect_consumer[i] << "] lack flow ";
                        cout << ins->connect_consumer_req[i] - vec_cons_flow[i] << "\n";
                        isvalid = false;
                    }
                }
            }
        }

        for (size_t i=0; i<mvec2_servers.size(); ++i)
        {
            real_cost += ins->node_cost[mvec2_servers[i]];
            real_cost += ins->mvec_server_type[mvec2_nodes_ser_level[mvec2_servers[i]]].second;
        }

        if (isvalid)
        {
            cout << "Cost:" << real_cost << ", Solution OK!\n";
        }
        else
        {
            cout << "Invalid Solution!\n";
        }

        // finalize
        if (flow_S != NULL)
        {
            for (int i = 0; i < ins->nodes + 2; ++i)
            {
                delete[] flow_S[i];
                flow_S[i] = NULL;
            }
            flow_S = NULL;
        }

        return ret;
    }

    cdnStatus GenerateGurobiResult(const string& strFile)
    {
        cdnStatus ret = CDN_OK;

        IntVector vec_ser_level(ins->nodes, -1);

        IntVector vec_server_;
        IntVector vec_level_;

        int all_cost = 0;

        int** flow_S = new int*[ins->nodes + 2];
        for (int i = 0; i < ins->nodes + 2; ++i)
        {
            flow_S[i] = new int[ins->nodes + 2];
            for (int j = 0; j < ins->nodes + 2; ++j)
            {
                flow_S[i][j] = 0;
            }
        }

        int** res_flow_S = new int*[ins->nodes + 2];
        for (int i = 0; i < ins->nodes + 2; ++i)
        {
            res_flow_S[i] = new int[ins->nodes + 2];
            for (int j = 0; j < ins->nodes + 2; ++j)
            {
                res_flow_S[i][j] = 0;
            }
        }

        ifstream in_file;
        in_file.open(strFile.c_str());
        if (in_file.is_open())
        {
            string strLine;

            // line 1
            int ser_, level_;
            size_t iPos;
            getline(in_file, strLine, '\n');
            while (true)
            {
                iPos = strLine.find(' ');
                if (iPos == string::npos)break;

                ser_ = atoi(strLine.substr(0, iPos).c_str());
                level_ = atoi(strLine.substr(iPos + 1).c_str());
                
                if (vec_ser_level[ser_] == -1)
                {
                    vec_ser_level[ser_] = level_;

                    vec_server_.push_back(ser_);
                    vec_level_.push_back(level_);
                }
                else
                {
                    cout << ser_ << " - " << level_ << "\n";
                }

                getline(in_file, strLine, '\n');
            }

            SetServers(vec_server_, vec_level_);

            getline(in_file, strLine, '\n');
            all_cost = atoi(strLine.c_str());

            // empty line
            getline(in_file, strLine, '\n');

            int node1, node2, flow_;
            getline(in_file, strLine, '\n');
            while (true)
            {
                iPos = strLine.find(' ');
                if (iPos == string::npos)break;

                node1 = atoi(strLine.substr(0, iPos).c_str());
                size_t iPos1 = strLine.find(' ', iPos + 1);
                node2 = atoi(strLine.substr(iPos + 1, iPos1).c_str());
                flow_ = atoi(strLine.substr(iPos1 + 1).c_str());

                flow_S[node1][node2] = flow_;
                res_flow_S[node1][node2] = flow_;

                getline(in_file, strLine, '\n');
            }

            in_file.close();
        }

        for (size_t i = 0; i < vec_server_.size(); ++i)
        {
            int cur_ser = vec_server_[i];

            flow_S[ins->nodes][cur_ser] = ins->mvec_server_type[vec_level_[i]].first;
            res_flow_S[ins->nodes][cur_ser] = ins->mvec_server_type[vec_level_[i]].first;
        }

        for (int i=0; i<ins->consumers; ++i)
        {
            int cur_conn = ins->server_conn[i];
            int cur_req = ins->server_req[i];
            
            flow_S[cur_conn][ins->nodes + 1] = cur_req;
            res_flow_S[cur_conn][ins->nodes + 1] = cur_req;
        }

        mvec_cur_paths.clear();
        fordFulkerson3(flow_S, res_flow_S, ins->nodes, ins->nodes + 1);

        // finalize
        if (flow_S != NULL)
        {
            for (int i = 0; i < ins->nodes + 2; ++i)
            {
                delete[] flow_S[i];
                flow_S[i] = NULL;
            }
            flow_S = NULL;
        }

        if (res_flow_S != NULL)
        {
            for (int i = 0; i < ins->nodes + 2; ++i)
            {
                delete[] res_flow_S[i];
                res_flow_S[i] = NULL;
            }
            res_flow_S = NULL;
        }

        return ret;
    }

    int server_num;
    int best_cost;
    int best_num_server;

    bool* inq;
    int* d;
    int* a;
    int* pre;

    Instance* ins;

    IntVector mvec2_servers;
    IntVector mvec2_server_level;
    BoolVector mvec2_cur_sol;

    IntVector mvec2_nodes_ser_level;

    IntVector mvec2_servers_best;
    BoolVector mvec2_sol_best;
    vector<IntVector> mvec2_G_best;
    vector<Edge> mvec2_edges_best;

    vector<IntVector> mvec_cur_paths;
};

struct LinkE
{
    int index;
    int links;

    LinkE(int i, int l)
        : index(i)
        , links(l)
    {
        // nothing to do
    }

    /*LinkE(const LinkE& obj)
    {
    index = obj.index;
    links = obj.links;
    }*/
};

struct Result {
    Result(const string& strFile)
        : m_cost(0)
        , m_paths(0)
    {
        ifstream in_file;
        in_file.open(strFile.c_str());
        if (in_file.is_open())
        {
            string strLine;

            // line 1
            getline(in_file, strLine, '\n');
            m_paths = atoi(strLine.c_str());

            // empty line
            getline(in_file, strLine, '\n');

            for (int i = 0; i < m_paths; ++i)
            {
                getline(in_file, strLine, '\n');
                string strtmep = strLine;
                vector<int> vec_path;
                size_t last_pos = 0;
                size_t new_pos = 0;
                int first = true;
                while (new_pos = strtmep.find(' '))
                {
                    string str_cur;
                    if (new_pos == string::npos)
                    {
                        str_cur = strtmep;
                    }
                    else
                    {
                        str_cur = strtmep.substr(last_pos, new_pos);
                    }

                    int num = atoi(str_cur.c_str());
                    if (first)
                    {
                        m_Servers.insert(num);
                        first = false;
                    }
                    vec_path.push_back(num);
                    strtmep = strtmep.substr(new_pos + 1);
                    //last_pos = new_pos + 1;
                    if (new_pos == string::npos)
                    {
                        break;
                    }
                }
                m_vec_paths.push_back(vec_path);
            }

            in_file.close();
        }
    }

    ~Result() {}

    int Cost()
    {
        return m_cost;
    }

    size_t Servers()
    {
        return m_Servers.size();
    }

    typedef vector<int> IntVector;

    bool IsSolutionValid(Instance* ins)
    {
        IntVector vec_cons_flow(ins->consumers, 0);
        IntVector vec_cons_cost(ins->consumers, 0);

        m_vec_server_type.clear();
        m_vec_server_type.resize(ins->nodes, -1);

        bool isvalid = true;

        int** cur_flow = new int*[ins->nodes];
        for (int i = 0; i < ins->nodes; ++i)
        {
            cur_flow[i] = new int[ins->nodes];
            for (int j = 0; j < ins->nodes; ++j)
            {
                cur_flow[i][j] = 0;
            }
        }

        // 解析路径
        for (size_t i = 0; i < m_vec_paths.size(); ++i)
        {
            IntVector& vec_path = m_vec_paths[i];

            size_t nsize = vec_path.size();
            int server_ = vec_path[0];
            int cons_ = vec_path[nsize - 3];
            int flow_ = vec_path[nsize - 2];
            int ser_type = vec_path[nsize - 1];

            if (m_vec_server_type[server_] < 0)
            {
                m_vec_server_type[server_] = ser_type;
            }
            else
            {
                if (m_vec_server_type[server_] != ser_type)
                {
                    isvalid = false;
                    cout << "server " << server_ << " has different types\n";
                }
            }

            if (nsize == 4)
            {
                //vec_cons_cost[cons_] = ins->server_cost;
            }
            else
            {
                for (size_t j = 0; j < nsize - 2; ++j)
                {
                    if (j == nsize - 4)
                    {
                        break;
                    }
                    vec_cons_cost[cons_] += ins->cost[vec_path[j]][vec_path[j + 1]] * flow_;
                    cur_flow[vec_path[j]][vec_path[j + 1]] += flow_;
                }
            }

            vec_cons_flow[cons_] += flow_;
        }

        // 判断每条边是否超流
        for (int i = 0; i < ins->nodes; ++i)
        {
            for (int j = 0; j < ins->nodes; ++j)
            {
                if (cur_flow[i][j] > ins->capacity[i][j])
                {
                    isvalid = false;
                    cout << "edge[" << i << "][" << j << "] flow exceed!\n";
                }
            }
        }

        // 判断消费节点流量是否满足
        for (int i = 0; i < ins->consumers; ++i)
        {
            m_cost += vec_cons_cost[i];

            if (vec_cons_flow[i] < ins->server_req[i])
            {
                isvalid = false;
                cout << "consumer[" << i << "] lack flow!\n";
            }
        }

        for (size_t i = 0; i < m_vec_server_type.size(); ++i)
        {
            if (m_vec_server_type[i] > -1)
            {
                m_cost += ins->node_cost[i];
                m_cost += ins->mvec_server_type[m_vec_server_type[i]].second;
            }
        }

        for (int j = 0; j < ins->nodes; ++j)
        {
            delete[] cur_flow[j];
            cur_flow[j] = NULL;
        }
        cur_flow = NULL;

        return isvalid;
    }

    bool PrintServers(const string& strOuptput)
    {
        ofstream out_file;
        out_file.open(strOuptput.c_str());
        if (out_file.is_open())
        {
            for (size_t i = 0; i < m_vec_server_type.size(); ++i)
            {
                if (m_vec_server_type[i] > -1)
                {
                    out_file << i << " " << m_vec_server_type[i] << "\n";
                }
            }

            out_file << "\n";
            out_file << "S: " << m_Servers .size() << ", Cost: " << m_cost << "\n";

            out_file.close();
        }
        
        return true;
    }

    void OutputFlowAndCost(Instance* ins, const string& filename)
    {
        IntVector vec_cons_flow(ins->consumers, 0);
        IntVector vec_cons_cost(ins->consumers, 0);

        IntVector vec_node_flow(ins->nodes, 0);
        IntVector vec_node_cost(ins->nodes, 0);

        IntVector vec_server_flow(ins->nodes, 0);
        //IntVector vec_server_cost(ins->nodes, 0);

        int** cur_flow = new int*[ins->nodes];
        for (int i = 0; i < ins->nodes; ++i)
        {
            cur_flow[i] = new int[ins->nodes];
            for (int j = 0; j < ins->nodes; ++j)
            {
                cur_flow[i][j] = 0;
            }
        }

        // 解析路径
        for (size_t i = 0; i < m_vec_paths.size(); ++i)
        {
            IntVector& vec_path = m_vec_paths[i];

            size_t nsize = vec_path.size();

            int cons_ = vec_path[nsize - 3];
            int flow_ = vec_path[nsize - 2];
            int ser_type = vec_path[nsize - 1];

            int server_ = vec_path[0];

            vec_server_flow[server_] += flow_;

            if (nsize == 4)
            {
                //vec_cons_cost[cons_] = ins->server_cost;
            }
            else
            {
                for (size_t j = 0; j < nsize - 2; ++j)
                {
                    if (j == nsize - 4)
                    {
                        break;
                    }
                    vec_cons_cost[cons_] += ins->cost[vec_path[j]][vec_path[j + 1]] * flow_;
                    cur_flow[vec_path[j]][vec_path[j + 1]] += flow_;

                    vec_node_flow[vec_path[j + 1]] += flow_;
                    vec_node_cost[vec_path[j + 1]] += ins->cost[vec_path[j]][vec_path[j + 1]] * flow_;
                }
            }

            vec_cons_flow[cons_] += flow_;
        }

        vector<LinkE> vec_flows;
        vector<LinkE> vec_costs;
        vector<LinkE> vec_server_flows;

        for (int i = 0; i<ins->nodes; ++i)
        {
            vec_flows.push_back(LinkE(i, vec_node_flow[i]));
            vec_costs.push_back(LinkE(i, vec_node_cost[i]));
            vec_server_flows.push_back(LinkE(i, vec_server_flow[i]));
        }

        sort(vec_flows.begin(), vec_flows.end(), cmp);
        sort(vec_costs.begin(), vec_costs.end(), cmp);
        sort(vec_server_flows.begin(), vec_server_flows.end(), cmp);

        ofstream out_file;
        out_file.open(filename.c_str());
        if (out_file.is_open())
        {
            out_file << "flow:\n";

            for (size_t i = 0; i<vec_flows.size(); ++i)
            {
                if (m_Servers.count(vec_flows[i].index) == 0)
                {
                    out_file << vec_flows[i].index << ": " << vec_flows[i].links << "\n";
                }
            }

            for (size_t i = 0; i<vec_server_flows.size(); ++i)
            {
                if (m_Servers.count(vec_server_flows[i].index) > 0)
                {
                    int req_ = ins->connect_consumer_req[vec_server_flows[i].index];

                    out_file << "S-" << vec_server_flows[i].index << ": " << vec_server_flows[i].links
                        << "-" << req_ << "=" << (vec_server_flows[i].links - req_) << "\n";
                }
            }

            /*out_file << "\ncost:\n";

            for (size_t i=0; i < vec_costs.size(); ++i)
            {
            if (m_Servers.count(vec_costs[i].index) > 0)
            {
            out_file << "S-";
            }
            out_file << vec_costs[i].index << ": " << vec_costs[i].links << "\n";
            }*/

            out_file.close();
        }

        for (int j = 0; j < ins->nodes; ++j)
        {
            delete[] cur_flow[j];
            cur_flow[j] = NULL;
        }
        cur_flow = NULL;
    }

    static bool cmp(const LinkE& a, const LinkE& b)
    {
        return a.links > b.links;
    }

    int m_cost;
    int m_paths;

    set<int> m_Servers;
    IntVector m_vec_server_type;
    vector<vector<int> > m_vec_paths;
};

int main(int argc, char* argv[])
{
    if (argc < 4) {
        cout << "Usage: " << argv[0] << " inst_file, result_file, op_type " << endl;
        return -1;
    }

    string instFile = argv[1];
    Instance* ins = new Instance(instFile);
    Solution* sol = new Solution(ins);

    int op_type = atoi(argv[argc-1]);
    switch (op_type)
    {
    case 0:  // 使用最优解生成调用最小费用流生成路径文件
    {
        int op_sers[] = { 3,7,14,36,69,103,125,129,155 };
        int op_level[] = { 5,3,4,3,4,3,3,3,5 };
        IntVector vec_sers(op_sers, op_sers + 9);
        IntVector vec_level(op_level, op_level + 9);

        cdnStatus st = CDN_OK;

        st = sol->Run(vec_sers, vec_level);

        string strResult;
        sol->GetResult(strResult);
        string strOutput = argv[2];
        ofstream output;
        output.open(strOutput.c_str());
        if (output.is_open())
        {
            output << strResult;
            output.close();
        }

        break;
    } 
    case 1: // 为测例生成其相邻连接边的情形
    {
        sol->OutputLinkedEdges(argv[2]);
        break;
    }
    case 2: // 验证gurobi生成的result.txt中的解是否合法
    {
        string strFile = argv[2];
        sol->ReadAndValidator(strFile);
        break;
    }
    case 3:  // 使用gurobi生成的result.txt生成最优路径
    {
        if (argc < 4) {
            cout << "Usage: " << argv[0] << " inst_file, gurobi_result, result_file " << endl;
            return -1;
        }
    
        string strFile = argv[2];
        sol->GenerateGurobiResult(strFile);

        sol->best_cost = 0;

        string strResult;
        sol->GetResult(strResult);
        string strOutput = argv[3];
        ofstream output;
        output.open(strOutput.c_str());
        if (output.is_open())
        {
            output << strResult;
            output.close();
        }

        break;
    }
    case 4:  // 使用路径解文件,生成服务器及其档次文件
    {
        string strResultName = argv[2];
        Result* res = new Result(strResultName);

        bool bValid = res->IsSolutionValid(ins);

        string strServerFile = argv[3];
        res->PrintServers(strServerFile);

        delete res;

        break;
    }
    case 5:  // 使用路径解文件,验证解是否合法
    {
        string strResultName = argv[2];
        Result* res = new Result(strResultName);

        bool bValid = res->IsSolutionValid(ins);
        if (bValid)
        {
            cout << "instance " << strResultName << " OK!\n";
            cout << "servers: " << res->Servers() << ", cost: " << res->Cost() << "\n\n";
        }
        else
        {
            cout << "instance " << strResultName << " invalid solution!\n\n";
        }

        delete res;

        break;
    }
    case 6:  // 使用路径解文件,输出流经每个结点的流量
    {
        string strResultName = argv[2];
        Result* res = new Result(strResultName);

        string strFlowFileName = argv[3];
        res->OutputFlowAndCost(ins, strFlowFileName);

        delete res;

        break;
    }
    default:
        cout << "error, invalid op_type\n";
        break;
    }

    delete sol;
    delete ins;
    
    return 0;
}
