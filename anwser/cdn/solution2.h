#ifndef CDN_SOLUTION2_H
#define CDN_SOLUTION2_H

#include "solution.h"
#include <set>

//#define OUTPUT_DEBUG_FILE

#define OLD_UPDATE_FLOW

//#include <map>

#ifndef OLD_UPDATE_FLOW
int dist[1200];
int path[1200];

struct cmp_
{
    bool operator()(const int& a, const int& b)const
    {
        return dist[a] < dist[b] || (dist[a] == dist[b] && a < b);
    }
};

set<int, cmp_> h;
#endif

namespace cdn{

    struct Solution2 : public Solution
    {
        Solution2(Instance* ins)
            : Solution(ins)
            , mvec2_cur_sol(ins->nodes, false)
            , mvec2_set_server(ins->nodes, false)
            , mvec2_has_deleted(ins->nodes, false)
            , mvec2_has_added(ins->nodes, false)
            , mvec2_set_server_fix(ins->nodes, false)
            , mvec2_lack_flow(ins->consumers, true)
            , mvec2_cons_cost(ins->nodes, 0)
            , mvec2_cons_flow(ins->nodes, 0)
        {
            // 初始最优解
            best_cost = ins->consumers * ins->server_cost;
            mvec_best_paths.clear();
            IntVector vec_path;
            for (int i = 0; i < ins->consumers; ++i)
            {
                vec_path.clear();
                vec_path.push_back(ins->server_conn[i]);
                vec_path.push_back(ins->connect_consumer[ins->server_conn[i]]);
                vec_path.push_back(ins->connect_consumer_req[ins->server_conn[i]]);

                mvec_best_paths.push_back(vec_path);
            }

            mvec2_servers.reserve(ins->consumers + 1);
            mvec2_vec_cost.reserve(ins->consumers + 1);
            m_time_b = clock();

            double time_int = LIMIT_CPU_TIME * CLOCKS_PER_SEC;
            m_time_end = (double)m_time_b + time_int;

            inq = new bool[ins->nodes + 2];   //是否在队列中
            d = new int[ins->nodes + 2];      //相对距离
            pre = new int[ins->nodes + 2];    //弧
            a = new int[ins->nodes + 2];      //增量

            flow_S = new int*[ins->nodes + 2];
            m_search_list = new int*[ins->nodes + 2];
            for (int i=0; i<ins->nodes+2; ++i)
            {
                flow_S[i] = new int[ins->nodes + 2];
                m_search_list[i] = new int[ins->nodes + 2];
                for (int j=0; j<ins->nodes+2; ++j)
                {
                    flow_S[i][j] = 0;
                    m_search_list[i][j] = 0;
                }
            }
        }

        ~Solution2()
        {
            delete[] inq;
            inq = NULL;
            delete[] d;
            d = NULL;
            delete[] pre;
            pre = NULL;
            delete[] a;
            a = NULL;

            if (flow_S != NULL)
            {
                for (int i = 0; i < ins->nodes + 2; ++i)
                {
                    delete[] flow_S[i];
                    flow_S[i] = NULL;
                }
                flow_S = NULL;
            }

            if (m_search_list != NULL)
            {
                for (int i = 0; i < ins->nodes + 2; ++i)
                {
                    delete[] m_search_list[i];
                    m_search_list[i] = NULL;
                }
                m_search_list = NULL;
            }
        }

        cdnStatus LocalSearch2()
        {
            if (!ins)
            {
                return CDN_ERROR;
            }

            srand((unsigned int)time(NULL));

            //clock_t time_b = clock();
            //double time_int = LIMIT_CPU_TIME * CLOCKS_PER_SEC;
            //double time_end = (double)time_b + time_int;

            cdnStatus ret = CDN_OK;
            int cur_iter = 1;

            int server_num_r = min((int)mvec_server_candates.size(), ins->consumers);
            int server_num_l = 1;

            server_num = (server_num_l + server_num_r) / 2;

            int search_times = 0;

            m_running_mode = CRM_INST_MODE;

            do
            {
                if (server_num < server_num_l)
                {
                    search_times++;
                    if (search_times > 2)
                    {
                        break;
                    }

                    server_num = best_num_server != 0 ? best_num_server : server_num_r;
                }

                OUTPUT_INFO(cout << "server number:" << server_num << "\n";)

                    if (m_running_mode > CRM_INST_MODE)
                    {
                        ResetSolution();
                    }

                ret = InitSolution();
                if (ret == CDN_FIND_SERVER_FAILED)
                {
                    server_num_l = server_num + 1;
                    continue;
                }

                OUTPUT_INFO(cout << "Find init solution!\n";)

                    m_running_mode = CRM_RUNNING_MODE;

                ret = FindCurOptimal(cur_iter);
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }

                server_num--;
            } while (true);

            OUTPUT_INFO(cout << "best server number: " << best_num_server << "\n";)
                OUTPUT_INFO(cout << "best cost: " << best_cost << "\n";)

                return ret;
        }

        cdnStatus AddOneServer3(int update_node, int flow_need, int* new_server_pos)
        {
            cdnStatus ret = CDN_OK;

            IntVector vec_parent(ins->nodes, 0);
            IntVector vec_pos;

            ret = FindLackFlowPath(update_node, flow_need, &vec_parent, &vec_pos);

            *new_server_pos = vec_pos[rand() % vec_pos.size()];
            if (mvec2_cur_sol[*new_server_pos])
            {
                OUTPUT_INFO(cout << "error happened, in AddOneServer3.\n";)
            }

            mvec2_servers.push_back(*new_server_pos);
            mvec2_cur_sol[*new_server_pos] = true;
            server_num++;

            return ret;
        }

        cdnStatus UpdateFlowPath3(int update_node, int new_server, bool init_sol = true)
        {
            cdnStatus ret = CDN_OK;

            for (int i = 0; i < ins->consumers; ++i)
            {
                int cur_cons = mvec_con_req[i].index; // 当前消费结点
                int cur_nodes = ins->server_conn[cur_cons];  // 和当前消费结点挂接的网络结点
                int cur_flow_need = mvec_con_req[i].links - mvec2_cons_flow[cur_nodes];  // 当前消费结点的带宽需求
                int cur_all_flow_need = mvec_con_req[i].links;

                bool can_not_find = false;

                if (!mvec2_cur_sol[cur_nodes] && cur_flow_need > 0)
                {
                    // 尽可能的满足流量,存在暂时不能满足而等待新增服务点来满足的情况
#ifdef OLD_UPDATE_FLOW
                    IntVector vec_parent(ins->nodes, 0);
#endif
                    int flow_sum = 0;
                    int flow_lack = 0;
                    int flow_cost = mvec2_cons_cost[cur_nodes];
                    int flow_ = mvec2_cons_flow[cur_nodes];
                    while (true)
                    {
                        if (flow_sum == cur_flow_need)
                        {
                            mvec2_lack_flow[cur_cons] = false;
                            break;
                        }
#ifndef OLD_UPDATE_FLOW

                        // begin
                        int find_ser = INVALID_NODE;
                        bool ret_i = DijkstraPath(cur_nodes, &find_ser, ins->nodes);
                        if (ret_i)
                        {
                            assert(find_ser != INVALID_NODE);

                            // 路径记录在path数组之中
                            int u, v = find_ser;
                            int find_flow = INT_MAX;
                            IntVector vec_path;
                            vec_path.push_back(v);
                            while ((u = path[v]) != -1)
                            {
                                find_flow = min(find_flow, ins->capacity[v][u] - ins->flow[v][u]);

                                if (u == find_ser)
                                {
                                    break;
                                }

                                vec_path.push_back(u);

                                v = u;
                            }

                            flow_ += find_flow;
                            if (flow_ <= cur_all_flow_need)
                            {
                                flow_cost += dist[find_ser] * find_flow;
                            }
                            else
                            {
                                flow_cost += dist[find_ser] *
                                    (cur_all_flow_need - flow_ + find_flow);
                            }

                            if (flow_cost >= ins->server_cost && init_sol)
                            {
                                // 退出,需要为该结点添加服务器
                                //OUTPUT_INFO(cout << "node cost:" << flow_cost << "\n";)
                                break;
                            }
                            else
                            {

                            }

                            flow_lack = 0;
                            int flow_add_true = 0;
                            ret = AddFlow4(cur_nodes, cur_flow_need, flow_sum,
                                &flow_lack, &flow_add_true, find_flow, vec_path, mvec_cur_paths);
                            mvec2_cons_cost[cur_nodes] += flow_add_true * dist[find_ser];
                            mvec2_cons_flow[cur_nodes] += flow_add_true;
                            if (ret == CDN_LACK_FLOW)
                            {
                                // 遍历补全剩余的流量
                            }
                            else if (ret == CDN_OK)
                            {
                                //break;
                            }
                        }
                        else
                        {
                            ret = CDN_FIND_SERVER_FAILED;
                            can_not_find = true;
                            break;
                        }

                        // end
#else
                        vector<FlowPath> vec_flow_path;
                        ret = BfsTraversal3(cur_nodes, 0, &vec_parent, &vec_flow_path);
                        if (ret == CDN_OK)
                        {
                            sort(vec_flow_path.begin(), vec_flow_path.end(), cmp_sl);

                            flow_ += vec_flow_path[0].flow;
                            if (flow_ <= cur_all_flow_need)
                            {
                                flow_cost += vec_flow_path[0].cost * vec_flow_path[0].flow;
                            }
                            else
                            {
                                flow_cost += vec_flow_path[0].cost * 
                                    (cur_all_flow_need - flow_ + vec_flow_path[0].flow);
                            }
                            
                            if (flow_cost >= ins->server_cost && init_sol)
                            {
                                // 退出,需要为该结点添加服务器
                                //OUTPUT_INFO(cout << "node cost:" << flow_cost << "\n";)
                                break;
                            }
                            else
                            {

                            }

                            flow_lack = 0;
                            int flow_add_true = 0;
                            ret = AddFlow3(cur_nodes, cur_flow_need, flow_sum,
                                &flow_lack, &flow_add_true, vec_flow_path, mvec_cur_paths);
                            mvec2_cons_cost[cur_nodes] += flow_add_true * vec_flow_path[0].cost;
                            mvec2_cons_flow[cur_nodes] += flow_add_true;
                            if (ret == CDN_LACK_FLOW)
                            {
                                // 遍历补全剩余的流量
                            }
                            else if (ret == CDN_OK)
                            {
                                //break;
                            }
                        }
                        else if (ret == CDN_FIND_SERVER_FAILED)
                        {
                            can_not_find = true;
                            break;
                        }
#endif
                    }

                    if (can_not_find && !init_sol)
                    {
                        break;
                    }
                }
                else
                {
                    // 不能continue;
                    if (mvec2_cur_sol[cur_nodes] && update_node == cur_nodes)
                    {
                        // 添加路径
                        IntVector vec_path;
                        vec_path.push_back(cur_nodes);
                        vec_path.push_back(-1);
                        vec_path.push_back(cur_cons);
                        vec_path.push_back(cur_all_flow_need);
                        mvec_cur_paths.push_back(vec_path);

                        mvec2_lack_flow[cur_cons] = false;
                    }
                }

                if (update_node == cur_nodes) // 从前往后更新
                {
                    break;
                }
            }

            return ret;
        }

        cdnStatus AddFlow3(int consumer, int flow_needed, int& flow_sum,
            int* flow_lack, int* flow_add_true, vector<FlowPath>& vec_flow_path, vector<IntVector>& vec_paths)
        {
            cdnStatus ret = CDN_OK;
            bool b_complete_add_flow = false;

            assert(vec_flow_path.size() > 0);

            // 每次更新一条路
            FlowPath& flow_path = vec_flow_path[0];
            IntVector& vec_path = flow_path.paths;

            int cur_add_flow = flow_path.flow;
            if (flow_sum + flow_path.flow > flow_needed)
            {
                cur_add_flow = flow_needed - flow_sum;
                b_complete_add_flow = true;
            }

            //mvec_server_nodes[flow_path.server]++;

            flow_sum += cur_add_flow;

            *flow_add_true = cur_add_flow;

            IntVector vec_res_path(vec_path);
            vec_res_path.push_back(-1);
            vec_res_path.push_back(ins->connect_consumer[consumer]);
            vec_res_path.push_back(cur_add_flow);

            vec_paths.push_back(vec_res_path);

            // 更新路上的流量
            for (size_t j = 0; j < vec_path.size() - 1; ++j)
            {
                ins->flow[vec_path[j]][vec_path[j + 1]] += cur_add_flow;
            }

            if (!b_complete_add_flow)
            {
                *flow_lack = flow_needed - flow_sum;
                return CDN_LACK_FLOW;
            }

            return ret;
        }

        cdnStatus AddFlow4(int consumer, int flow_needed, int& flow_sum,
            int* flow_lack, int* flow_add_true, int find_flow, IntVector& vec_flow_path, vector<IntVector>& vec_paths)
        {
            cdnStatus ret = CDN_OK;
            bool b_complete_add_flow = false;

            assert(vec_flow_path.size() > 0);

            // 每次更新一条路
            IntVector& vec_path = vec_flow_path;

            int cur_add_flow = find_flow;
            if (flow_sum + find_flow > flow_needed)
            {
                cur_add_flow = flow_needed - flow_sum;
                b_complete_add_flow = true;
            }

            //mvec_server_nodes[flow_path.server]++;

            flow_sum += cur_add_flow;

            *flow_add_true = cur_add_flow;

            IntVector vec_res_path(vec_path);
            vec_res_path.push_back(-1);
            vec_res_path.push_back(ins->connect_consumer[consumer]);
            vec_res_path.push_back(cur_add_flow);

            vec_paths.push_back(vec_res_path);

            // 更新路上的流量
            for (size_t j = 0; j < vec_path.size() - 1; ++j)
            {
                ins->flow[vec_path[j]][vec_path[j + 1]] += cur_add_flow;
            }

            if (!b_complete_add_flow)
            {
                *flow_lack = flow_needed - flow_sum;
                return CDN_LACK_FLOW;
            }

            return ret;
        }

        cdnStatus RemoveFlow3(vector<IntVector>& vec_paths)
        {
            cdnStatus ret = CDN_OK;

            if (vec_paths.empty())
            {
                return ret;
            }

            size_t n_paths = vec_paths.size();

            for (size_t i = 0; i < n_paths; ++i)
            {
                IntVector& vec_flow_path = vec_paths[i];
                size_t n_flow_path = vec_flow_path.size();

                // 更新路上的流量
                for (size_t j = 0; j < vec_flow_path.size() - 1; ++j)
                {
                    if (vec_flow_path[j + 1] == -1)
                    {
                        break;
                    }
                    ins->flow[vec_flow_path[j]][vec_flow_path[j + 1]] -= vec_flow_path[n_flow_path-1];
                }
            }

            return ret;
        }

        bool FindFlowPath3(int cur_node, int flow_needed, int least_cost, bool* must_set_server, int mode = CDC_LESSER)
        {
            bool ret = false;

            if (server_num == 0)
            {
                ret = false; // 选服务器结点
                return ret;
            }
            else
            {
                vector<IntVector> vec_paths;
#ifdef OLD_UPDATE_FLOW
                IntVector vec_parent(ins->nodes, 0);
#endif
                int flow_sum = 0;
                int flow_lack = 0;
                int flow_cost = 0;
                int flow_ = 0;

                cdnStatus st = CDN_OK;

                while (true)
                {
                    if (flow_sum == flow_needed)
                    {
                        ret = true;
                        break;
                    }

#ifndef OLD_UPDATE_FLOW
                    // begin
                    int find_ser = INVALID_NODE;
                    bool ret_i = DijkstraPath(cur_node, &find_ser, ins->nodes);
                    if (ret_i)
                    {
                        assert(find_ser != INVALID_NODE);
                        if (mode == CDC_EQUAL)
                        {
                            if (dist[find_ser] > least_cost)
                            {
                                // 退出,需要为该结点添加服务器
                                ret = false;
                                break;
                            }
                        }

                        // 路径记录在path数组之中
                        int u, v = find_ser;
                        int find_flow = INT_MAX;
                        IntVector vec_path;
                        vec_path.push_back(v);
                        while ((u = path[v]) != -1)
                        {
                            find_flow = min(find_flow, ins->capacity[v][u] - ins->flow[v][u]);

                            if (u == find_ser)
                            {
                                break;
                            }

                            vec_path.push_back(u);

                            v = u;
                        }

                        flow_lack = 0;
                        int flow_add_true = 0;
                        st = AddFlow4(cur_node, flow_needed, flow_sum,
                            &flow_lack, &flow_add_true, find_flow, vec_path, vec_paths);
                        if (st == CDN_LACK_FLOW)
                        {
                            // 遍历补全剩余的流量
                        }
                        else if (st == CDN_OK)
                        {
                            //break;
                        }

                        flow_ += find_flow;
                        if (flow_ <= flow_needed)
                        {
                            flow_cost += dist[find_ser] * find_flow;
                        }
                        else
                        {
                            flow_cost += dist[find_ser] *
                                (flow_needed - flow_ + find_flow);
                        }


                        if (flow_cost >= ins->server_cost)
                        {
                            // 退出,需要为该结点添加服务器
                            ret = false;
                            break;
                        }
                        else
                        {

                        }
                    }
                    else
                    {
                        st = CDN_FIND_SERVER_FAILED;
                        ret = false;
                        break;
                    }

                    // end
#else
                    vector<FlowPath> vec_flow_path;
                    st = BfsTraversal3(cur_node, least_cost, &vec_parent, &vec_flow_path);
                    if (st == CDN_OK)
                    {
                        sort(vec_flow_path.begin(), vec_flow_path.end(), cmp_sl);

                        if (mode == CDC_EQUAL)
                        {
                            if (vec_flow_path[0].cost > least_cost)
                            {
                                // 退出,需要为该结点添加服务器
                                ret = false;
                                *must_set_server = true;
                                break;
                            }
                        }

                        int flow_add_truly = 0;
                        cdnStatus st = AddFlow3(cur_node, flow_needed, flow_sum,
                            &flow_lack, &flow_add_truly, vec_flow_path, vec_paths);
                        if (st == CDN_LACK_FLOW)
                        {
                            // 遍历补全剩余的流量
                        }
                        else if (st == CDN_OK)
                        {
                            //break;
                        }

                        //flow_sum += vec_flow_path[0].flow;

                        flow_ += vec_flow_path[0].flow;
                        if (flow_ <= flow_needed)
                        {
                            flow_cost += vec_flow_path[0].cost * vec_flow_path[0].flow;
                        }
                        else
                        {
                            flow_cost += vec_flow_path[0].cost * 
                                (flow_needed - flow_ + vec_flow_path[0].flow);
                        }

                        
                        if (flow_cost >= ins->server_cost)
                        {
                            // 退出,需要为该结点添加服务器
                            ret = false;
                            break;
                        }
                        else
                        {

                        }
                    }
                    else if (st == CDN_FIND_SERVER_FAILED)
                    {
                        ret = false;
                        break;
                    }

#endif
                }
               
                RemoveFlow3(vec_paths);
            }

            return ret;
        }

        cdnStatus FindLackFlowPath(int start, int least_flow, IntVector* pvec_parent,
            IntVector* pvec_flow_path)
        {
            // 遍历消费节点,直至找到服务器点,否则认为当前选择失败
            BoolVector vec_visited(ins->nodes, false);
            IntQueue q_node;
            q_node.push(start); // start是虚拟节点
            pvec_parent->at(start) = -1;

            while (!q_node.empty())
            {
                int cur = q_node.front();
                q_node.pop();

                // 以消费节点为中心进行广度优先遍历,获取最近的服务节点
                pvec_flow_path->push_back(cur);
                if (pvec_flow_path->size() > 10)
                {
                    // 从最近的10个节点里面选
                    break;
                }

                for (int i = 0; i < ins->nodes; ++i)
                {
                    // 因为是从消费结点到服务结点反向遍历,因此是ins->capacity[i][cur]
                    if (vec_visited[i] == false && (ins->capacity[i][cur] - ins->flow[i][cur]) >= least_flow)//(ins->capacity[cur][i]-ins->flow[cur][i])>0)
                    {
                        q_node.push(i);
                        (*pvec_parent)[i] = cur;
                        vec_visited[i] = true;
                    }
                }
            }

            if (pvec_flow_path->empty())
            {
                return CDN_FIND_SERVER_FAILED;
            }

            return CDN_OK;
        }

        cdnStatus FindAllFlow()
        {
            cdnStatus ret = CDN_OK;

            for (int i = 0; i < ins->consumers; ++i)
            {
                int cur_cons = mvec_con_req[i].index; // 当前消费结点
                int cur_nodes = ins->server_conn[cur_cons];  // 和当前消费结点挂接的网络结点

                ret = UpdateFlowPath3(cur_nodes, INVALID_NODE);
            }

            return ret;
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

        bool bfs3(int** rGraph, int s, int t, IntVector& parent)
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
                    if (visited[v] == false && rGraph[u][v] > 0)
                    {
                        q.push(v);
                        parent[v] = u;
                        visited[v] = true;
                    }
                }
            }

            return (visited[t] == true);
        }

        int fordFulkerson3(int** rGraph, int s, int t)
        {
            int u, v;

            IntVector parent(ins->nodes + 2, 0);
            int max_flow = 0;
            while (bfs3(rGraph, s, t, parent))
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
                
                mvec_cur_paths.push_back(vec_path);
            }
            return max_flow;
        }

        cdnStatus FindAllFlow_MinCost()
        {
            cdnStatus ret = CDN_OK;

            // 连边
            ins->addExtra(mvec2_servers);

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

                if (server_num * ins->server_cost + cost < best_cost)
                {
                    for (int i = 0; i < ins->nodes + 2; ++i)
                    {
                        for (int j = 0; j < ins->nodes + 2; ++j)
                        {
                            ins->inc_cost[i][j] = 0; // 记录最优流量
                        }
                    }

                    best_cost = server_num * ins->server_cost + cost;
                    best_num_server = server_num;

                    OUTPUT_INFO(cout << "best cost: " << best_cost << ",  " << server_num << endl;)

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
                    //mvec2_G_best.assign(ins->mvec_G.begin(), ins->mvec_G.end());
                    //mvec2_edges_best.assign(ins->mvec_edges.begin(), ins->mvec_edges.end());
                }
            } while (false);

            return ret;
        }

        bool IsFlowSatisfied(int cur_cons_node, int cur_flow_need, int* add_server, bool* must_set_server)
        {
            int adj_conn_cons = 0;
            int adj_adj_conn_cons = 0;
            int adj_server_num = 0; // 相邻的节点已经是服务器的个数

            int min_cost = INT_MAX;

            bool flow_satisfied = false;
            int least_cost = ins->server_cost / cur_flow_need;

            //map<int, pair<int, int> > map_adj_flow_cost;
            vector<pair<int, int> > vec_flow_cost;
            IntVector vec_min_cost_nodes;

            // opt:只针对流量需求大的结点
            for (int j = 0; j < ins->linked_edges[cur_cons_node]; ++j)
            {
                int adj_node = ins->bfs_node[cur_cons_node][j + 1];

                // 相邻顶点的邻边集合
                for (int k = 0; k < ins->linked_edges[adj_node]; ++k)
                {
                    int adj_adj_node = ins->bfs_node[adj_node][k + 1];
                    if (ins->connect_consumer[adj_adj_node] > -1) // 相邻的节点的邻边挂着消费节点
                    {
                        adj_adj_conn_cons++;
                    }
                }

                //map_adj_flow_cost[adj_node] = make_pair(ins->capacity[cur_cons_node][adj_node],
                //    ins->cost[cur_cons_node][adj_node]);
                vec_flow_cost.push_back(make_pair(ins->capacity[cur_cons_node][adj_node], 
                    ins->cost[cur_cons_node][adj_node]));

                if (ins->connect_consumer[adj_node] > -1) // 相邻的节点挂着消费节点
                {
                    adj_conn_cons++;
                }

                if (mvec2_cur_sol[adj_node])
                {
                    adj_server_num++;
                }

                if (ins->cost[cur_cons_node][adj_node] < min_cost)
                {
                    min_cost = ins->cost[cur_cons_node][adj_node];
                    vec_min_cost_nodes.push_back(adj_node);
                }
            }

            // 如果第一个点相邻的结点挂着消费点,则取当前点为服务点,
            // 否则,在流量满足的情况下选择其相邻的边多的结点
            // 当前靠近消费节点的网络节点,如果其相邻的节点挂着消费节点,则放置在该网络节点

            if (min_cost > least_cost)
            {
                // 选择当前结点
                *add_server = cur_cons_node;
                flow_satisfied = true;
                *must_set_server = true;
            }
            else if (min_cost == least_cost)
            {
                // 首先找路,不能满足则在其附近添加服务点
                bool b_need_add = FindFlowPath3(cur_cons_node, cur_flow_need, least_cost, must_set_server, CDC_EQUAL);
                if (b_need_add)
                {
                    flow_satisfied = true;
                    return flow_satisfied;
                }

                // 只能选当前或相邻的顶点 考虑flow是否满足需求 找路确定
                int min_cost_edge = 0;
                int min_cost_node = 0;
                for (int j = 0; j < ins->linked_edges[cur_cons_node]; ++j)
                {
                    int adj_node = ins->bfs_node[cur_cons_node][j + 1];

                    if (ins->cost[cur_cons_node][adj_node] == min_cost)
                    {
                        // TODO:选流量带宽最大的（目前选择连接的边最多的）
                        if (ins->linked_edges[adj_node] > min_cost_edge)
                        {
                            min_cost_edge = ins->linked_edges[adj_node];
                            min_cost_node = adj_node;
                        }
                    }
                }

                // 流量满足则选择边多的,否则选当前点
                // 模糊判断流量是否满足
                sort(vec_flow_cost.begin(), vec_flow_cost.end(), cmp_p);
                int flow_supply = 0;
                int flow_cost = 0;
                bool b_flow_satisfied = false;
                for (size_t i = 0; i < vec_flow_cost.size(); ++i)
                {
                    flow_supply += vec_flow_cost[i].first; 
                    
                    if (flow_supply >= cur_flow_need)
                    {
                        flow_cost += (vec_flow_cost[i].first - flow_supply + cur_flow_need) 
                            * (vec_flow_cost[i].second + 1);

                        b_flow_satisfied = flow_cost >= ins->server_cost ? false : true;
                        break;
                    }

                    flow_cost += vec_flow_cost[i].first * vec_flow_cost[i].second;
                }

                *add_server = adj_conn_cons > 0 ? cur_cons_node  : 
                        (b_flow_satisfied ? min_cost_node : cur_cons_node);
                flow_satisfied = !b_flow_satisfied;
            }
            else
            {
                assert(min_cost < least_cost);
                // 找路--- [找到-找不到-流量够不够]

                bool b_need_add = FindFlowPath3(cur_cons_node, cur_flow_need, least_cost, must_set_server);
                if (b_need_add)
                {
                    flow_satisfied = true;
                    return flow_satisfied;
                }

                // 当前结点相邻的结点挂接着消费结点
                // 只能选当前或相邻的顶点 考虑flow是否满足需求 找路确定
                int min_cost_edge = 0;
                int min_cost_node = 0;
                //IntVector vec_cand_min_cost;
                for (int j = 0; j < ins->linked_edges[cur_cons_node]; ++j)
                {
                    int adj_node = ins->bfs_node[cur_cons_node][j + 1];

                    if (ins->cost[cur_cons_node][adj_node] == min_cost)
                    {
                        // TODO:选流量带宽最大的（目前选择连接的边最多的）
                        if (ins->linked_edges[adj_node] > min_cost_edge)
                        {
                            min_cost_edge = ins->linked_edges[adj_node];
                            min_cost_node = adj_node;
                            //vec_cand_min_cost.push_back(adj_node);
                        }
                    }
                }

                // 流量满足则选择边多的,否则选当前点
                // 模糊判断流量是否满足
                sort(vec_flow_cost.begin(), vec_flow_cost.end(), cmp_p);
                int flow_supply = 0;
                int flow_cost = 0;
                bool b_flow_satisfied = false;
                for (size_t i = 0; i < vec_flow_cost.size(); ++i)
                {
                    flow_supply += vec_flow_cost[i].first;

                    if (flow_supply >= cur_flow_need)
                    {
                        flow_cost += (vec_flow_cost[i].first - flow_supply + cur_flow_need)
                            * (vec_flow_cost[i].second + 1);

                        b_flow_satisfied = flow_cost >= ins->server_cost ? false : true;
                        break;
                    }

                    flow_cost += vec_flow_cost[i].first * vec_flow_cost[i].second;
                }

                if (b_flow_satisfied && adj_server_num>=adj_conn_cons)
                {
                    if (rand()%2 == 0)
                    {
                        flow_satisfied = true;
                        return flow_satisfied;
                    }
                }

                *add_server = adj_conn_cons > 0 ? cur_cons_node :
                    (b_flow_satisfied ? min_cost_node : cur_cons_node);
                flow_satisfied = b_flow_satisfied;
            }

            return flow_satisfied;
        }

        cdnStatus BfsTraversal3(int start, int least_cost, IntVector* pvec_parent,
            vector<FlowPath>* pvec_flow_path)
        {
            if (mvec2_cur_sol[start])
            {
                IntVector vec_path;
                vec_path.push_back(start);
                pvec_flow_path->push_back(FlowPath(start, start, 0, 0, INT_MAX, vec_path));
                return CDN_OK;
            }

            // 遍历消费节点,直至找到服务器点,否则认为当前选择失败
            BoolVector vec_visited(ins->nodes, false);
            IntQueue q_node;
            q_node.push(start); // start是虚拟节点
            pvec_parent->at(start) = -1;

            while (!q_node.empty())
            {
                int cur = q_node.front();
                q_node.pop();

                // 以消费节点为中心进行广度优先遍历,获取最近的服务节点
                if (mvec2_cur_sol[cur])
                {
                    int u, v = cur;
                    int layer = 0;
                    int cost = 0;
                    int flow = INT_MAX;
                    IntVector vec_path;
                    vec_path.push_back(v);

                    while ((u = pvec_parent->at(v)) != -1)
                    {
                        layer++;
                        cost += ins->cost[v][u];
                        flow = min(flow, ins->capacity[v][u] - ins->flow[v][u]);

                        vec_path.push_back(u);

                        if (u == start)
                        {
                            break;
                        }

                        v = u;
                    }

                    pvec_flow_path->push_back(FlowPath(start, cur, layer, cost, flow, vec_path));
                    if (pvec_flow_path->size() > 20)
                    {
                        return CDN_OK;
                    }
                }

                for (int i = 0; i < ins->nodes; ++i)
                {
                    // 因为是从消费结点到服务结点反向遍历,因此是ins->capacity[i][cur]
                    if (vec_visited[i] == false && (ins->capacity[i][cur] - ins->flow[i][cur]) > 0)//(ins->capacity[cur][i]-ins->flow[cur][i])>0)
                    {
                        q_node.push(i);
                        (*pvec_parent)[i] = cur;
                        vec_visited[i] = true;
                    }
                }
            }

            if (pvec_flow_path->empty())
            {
                return CDN_FIND_SERVER_FAILED;
            }

            return CDN_OK;
        }

        cdnStatus LocalSearch3()
        {
            if (!ins)
            {
                return CDN_ERROR;
            }

            srand((unsigned int)time(NULL));

            cdnStatus ret = CDN_OK;

            // step1.放置服务器,找可行解
            // 贪心,每次只给当前结点找流量,找不全也没关系,最后统一检查某结点解超过建立服务器的情形
            for (int i=0; i<ins->consumers; ++i)
            {
                int cur_cons = mvec_con_req[i].index; // 当前消费结点
                int cur_nodes = ins->server_conn[cur_cons];  // 和当前消费结点挂接的网络结点
                int cur_flow_need = mvec_con_req[i].links;  // 当前消费结点的带宽需求

                // 判断流量是否足够
                int add_server = INVALID_NODE;
                bool must_set_server = false;

                // 判断当前消费结点是否需要添加新的服务点
                bool flow_satisfied = IsFlowSatisfied(cur_nodes, cur_flow_need, &add_server, &must_set_server);
                flow_satisfied = flow_satisfied; // unused variable
                
                if (add_server != INVALID_NODE)
                {
                    mvec2_servers.push_back(add_server);
                    mvec2_cur_sol[add_server] = true;
                    server_num++;

                    if (cur_nodes == add_server)
                    {
                        mvec2_set_server[cur_nodes] = true;
                    }

                    if (must_set_server)
                    {
                        mvec2_set_server_fix[cur_nodes] = true;
                    }

                    // 更新当前及之前的节点flow
                    //Reinit3(); // 此处理应重新寻找流量,但出于效率考虑不予重置
                    UpdateFlowPath3(cur_nodes, add_server);
                }
                else
                {
                    // 更新流量
                    UpdateFlowPath3(cur_nodes, INVALID_NODE);
                }
            }

            bool has_call_min_cost = false;
            // 补全上一步没找全流量的消费节点,实在找不到流量则新建服务器
            while (true)
            {
                int cur_invalid_cons_ = INVALID_NODE;
                int flow_needed_ = 0;
                if (IsSolutionValid3(&cur_invalid_cons_, &flow_needed_))
                {
                    OUTPUT_INFO(cout << "Valid solution!" << endl;)
                    break;
                }
                else
                {
                    OUTPUT_INFO(cout << "Invalid solution! node " << cur_invalid_cons_ << " need " << flow_needed_ << endl;)
                    ret = UpdateFlowPath3(cur_invalid_cons_, INVALID_NODE, false);
                    if (ret == CDN_FIND_SERVER_FAILED)
                    {
                        OUTPUT_INFO(cout << "update node " << cur_invalid_cons_ << " flow failed, no path!" << endl;)
                        int new_pos = INVALID_NODE;
                        ret = AddOneServer3(cur_invalid_cons_, flow_needed_, &new_pos);
                        Reinit3();
                        //ret = UpdateFlowPath3(cur_invalid_cons_, INVALID_NODE, false);
                        ret = FindAllFlow_MinCost();
                        has_call_min_cost = true;
                        GetPaths(ins->mvec_edges, ins->mvec_G, mvec2_servers);
                        //break;
                    }
                }
            }

            //OutputServerNonmove("non_move.txt");

            // 执行到此则已有完整的可行解
            RecordCost(0);
            
            // 消费节点的cost大于建设服务器的成本时为其增加服务器
            GetCostOfCons(mvec2_vec_cost);
            sort(mvec2_vec_cost.begin(), mvec2_vec_cost.end(), cmp);
            while (mvec2_vec_cost[0].links > ins->server_cost)
            {
                if (server_num < ins->consumers)
                {
                    int cur_node = ins->server_conn[mvec2_vec_cost[0].index];
                    if (mvec2_cur_sol[cur_node])
                    {
                        OUTPUT_INFO(cout << "error in compute server cost\n";)
                    }
                    mvec2_servers.push_back(cur_node);
                    mvec2_cur_sol[cur_node] = true;
                    server_num++;

                    Reinit3();
                    ret = FindAllFlow_MinCost();
                    has_call_min_cost = true;
                    GetPaths(ins->mvec_edges, ins->mvec_G, mvec2_servers);

                    mvec2_vec_cost.clear();
                    GetCostOfCons(mvec2_vec_cost);
                    sort(mvec2_vec_cost.begin(), mvec2_vec_cost.end(), cmp);
                }
                else
                {
                    break;
                }
            }

            {
                OUTPUT_INFO(cout << "server number: " << server_num << endl;)
            }

            if (!has_call_min_cost)
            {
                Reinit3();
                ret = FindAllFlow_MinCost();
                has_call_min_cost = true;
            }

            // step2.局部搜索
            
            // 邻域动作:交换相邻的边,删除一个服务点,添加一个服务点
            do 
            {
                for (int i=0; i<ins->nodes+2; ++i)
                {
                    for (int j = 0; j < ins->nodes + 2; ++j)
                    {
                        m_search_list[i][j] = 1;
                    }
                }

                if (ins->nodes < SCALE_BOUND)
                {
                    m_running_mode = CRM_REPEAT_MODE;
                }

                ret = AddAndRemoveOneServerForBS();
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }

                if (ins->nodes < 2 * SCALE_BOUND)
                {
                    m_running_mode = CRM_REPEAT_MODE;
                }

                // backup for add server
                // 从最优解开始搜索
                if (!mvec2_sol_best.empty())
                {
                    mvec2_servers.assign(mvec2_servers_best.begin(), mvec2_servers_best.end());
                    mvec2_cur_sol.assign(mvec2_sol_best.begin(), mvec2_sol_best.end());
                    server_num = best_num_server;
                }

                IntVector _vec_servers_bc(mvec2_servers.begin(), mvec2_servers.end());
                BoolVector _vec_cur_sol_bc(mvec2_cur_sol.begin(), mvec2_cur_sol.end());
                int cur_server_num = server_num;

                OUTPUT_INFO(cout << "\nadd server\n\n";)
                ret = AddOneServerAndFind();
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }

                mvec2_servers.assign(_vec_servers_bc.begin(), _vec_servers_bc.end());
                mvec2_cur_sol.assign(_vec_cur_sol_bc.begin(), _vec_cur_sol_bc.end());
                server_num = cur_server_num;

                OUTPUT_INFO(cout << "\nremove server\n\n";)
                ret = RemoveOneServerAndFind();
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }
            } while (false);
            
            // 记录结果
            if (best_cost < ins->consumers*ins->server_cost)
            {
                mvec_cur_paths.clear();
                fordFulkerson3(ins->inc_cost, ins->nodes, ins->nodes + 1);
                mvec_best_paths.clear();
                mvec_best_paths.insert(mvec_best_paths.begin(),
                    mvec_cur_paths.begin(), mvec_cur_paths.end());

                cout << "best cost:" << best_cost << "\n";
            }

            /*if (ValidSolution() == false)
            {
                OUTPUT_INFO(cout << "invalid solution\n";)
            }*/

            PrintTime("terminate");

            return ret;
        }

        cdnStatus InitSolution()
        {
            cdnStatus ret = CDN_OK;

            int failed_cons;
            int failed_times = 0;

            int failed_upbound = ins->nodes * 10;

            for (int i = 0; i < server_num; ++i)
            {
                mvec_servers.push_back(mvec_links[i].index);
                mvec_cur_sol[mvec_links[i].index] = true;
            }

            int iter = 1;

            do
            {
                ret = FindValidSol(&failed_cons, iter);
                if (ret == CDN_OK)
                {
                    failed_times = 0;
                    break;
                }
                else if (ret == CDN_FIND_SERVER_FAILED)
                {
                    failed_times++;
                    IntVector add_sets(1, failed_cons);
                    FindServerFromNode(failed_cons, &add_sets, iter);
                    assert(add_sets.size() > 1);

                    int old_pos = add_sets.back();
                    int rand_index = rand() % (add_sets.size() - 1);
                    int new_pos = add_sets[rand_index];
                    MoveServerPosition(old_pos, new_pos, iter);
                }

                iter++;

                if (failed_times > failed_upbound)
                {
                    ret = CDN_FIND_SERVER_FAILED;
                    OUTPUT_INFO(cout << "exceed failed_upbound\n";)
                    break;
                }
            } while (true);

            return ret;
        }

        cdnStatus ResetSolution()
        {
            cdnStatus ret = CDN_OK;

            mvec_servers.clear();

            mvec_cur_sol.clear();
            mvec_cur_sol.resize(ins->nodes, false);

            mvec_del_tabu_lis.clear();
            mvec_del_tabu_lis.resize(ins->nodes, 0);

            mvec_add_tabu_lis.clear();
            mvec_add_tabu_lis.resize(ins->nodes, 0);

            return ret;
        }

        cdnStatus FindCurOptimal(int iter)
        {
            cdnStatus ret = CDN_OK;

            int temp_cost = cur_cost;
            int cur_iter = 1;

            int success_times = 0;

            do
            {
                mvec2_servers.clear();
                mvec2_cur_sol.clear();
                mvec2_servers.insert(mvec2_servers.begin(), mvec_servers.begin(), mvec_servers.end());
                mvec2_cur_sol.insert(mvec2_cur_sol.begin(), mvec_cur_sol.begin(), mvec_cur_sol.end());

                int cur_server;
                int cur_node;

                int select_server = INVALID_NODE;
                int select_node = INVALID_NODE;

                int temp_s;

                for (size_t i = 0; i < mvec2_servers.size(); ++i)
                {
                    cur_server = mvec2_servers[i];
                    for (size_t j = 0; j < mvec_server_candates.size(); ++j)
                    {
                        cur_node = mvec_server_candates[j];
                        if (!mvec2_cur_sol[cur_node])
                        {
                            temp_s = mvec_servers[i];
                            mvec_cur_sol[mvec_servers[i]] = false;
                            mvec_servers[i] = cur_node;
                            mvec_cur_sol[mvec_servers[i]] = true;

                            Reinit(); // TODO:优化Reinit内部

                            int failed_cons;
                            ret = FindValidSol(&failed_cons, cur_iter);
                            if (ret == CDN_OK)
                            {
                                if (cur_cost < temp_cost)
                                {
                                    temp_cost = cur_cost;
                                    select_node = cur_node;
                                    select_server = cur_server;
                                    //OUTPUT_INFO(cout << "cost: " << cur_cost << "\n";)
                                }

                                success_times++;
                            }
                            else if (ret == CDN_FIND_SERVER_FAILED)
                            {
                                success_times = 0;
                            }

                            mvec_cur_sol[mvec_servers[i]] = false;
                            mvec_servers[i] = temp_s;
                            mvec_cur_sol[mvec_servers[i]] = true;
                        }
                    }
                }

                cur_iter++;

                OUTPUT_INFO(cout << "find a solution" << "\n";);

                if (select_server == INVALID_NODE)
                {
                    break;
                }
                else
                {
                    for (size_t i = 0; i < mvec_servers.size(); ++i)
                    {
                        if (mvec_servers[i] == select_server)
                        {
                            mvec_servers[i] = select_node;
                            break;
                        }
                    }
                    mvec_cur_sol[select_server] = false;
                    mvec_cur_sol[select_node] = true;
                }
            } while (true);

            return ret;
        }

        cdnStatus AddOneServerAndFind()
        {
            cdnStatus ret = CDN_OK;

            int server_add_num = 0;
          
            do 
            {
                if (server_num >= ins->consumers)
                {
                    break;
                }

                bool has_optimal = false;
                IntVector vec_servers_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec2_servers.begin(), mvec2_servers.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec2_cur_sol.begin(), mvec2_cur_sol.end());

                int cur_server;
                int cur_cost_local = best_cost;
                int select_server = INVALID_NODE;
                int temp = -1;

                vector<LinkE> vec_non_server_flow_;

                for (size_t i = 0; i < mvec_server_candates.size(); ++i)
                {
                    cur_server = mvec_server_candates[i];
                    if (!vec_cur_sol_[cur_server] && !mvec2_cur_sol[cur_server])
                    {
                        int inflow_ = 0;
                        int cur_node_;
                        for (int k = 0; k < ins->linked_edges[cur_server]; ++k)
                        {
                            cur_node_ = ins->bfs_node[cur_server][k + 1];
                            if (ins->inc_cost[cur_node_][cur_server] > 0)
                            {
                                inflow_ += ins->inc_cost[cur_node_][cur_server];
                            }
                        }

                        vec_non_server_flow_.push_back(LinkE(cur_server, inflow_));
                    }
                }

                if (m_big_scale)
                {
                    sort(vec_non_server_flow_.begin(), vec_non_server_flow_.end(), cmp);
                }

                cur_cost_local = best_cost;
                for (size_t i = 0; i < vec_non_server_flow_.size(); ++i)
                {
                    if (m_big_scale)
                    {
                        if ((double)clock() > m_time_end)
                        {
                            return CDN_TIME_OUT;
                        }
                    }

                    // 增加流经流量最多的点为服务器,然后调用最小费用流算法
                    int cur_add_ = vec_non_server_flow_[i].index;
                    mvec2_servers.push_back(cur_add_);
                    mvec2_cur_sol[cur_add_] = true;
                    server_num++;

                    Reinit3();
                    ret = FindAllFlow_MinCost();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < cur_cost_local)
                        {
                            cur_cost_local = best_cost;
                            select_server = cur_add_;
                            has_optimal = true;
                            server_add_num = 0;
                        }
                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    mvec2_servers.pop_back();
                    mvec2_cur_sol[cur_add_] = false;
                    server_num--;

                    if (m_big_scale && i>20)
                    {
                        break;
                    }
                }

                if (select_server != INVALID_NODE)
                {
                    mvec2_servers.push_back(select_server);
                    mvec2_cur_sol[select_server] = true;
                    server_num++;
                    //OUTPUT_INFO(cout << "add one server " << mvec2_servers.size() << "\n";)

                    cur_cost_local = best_cost;
                    ret = FindCurOptimal_Links();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < cur_cost_local)
                        {
                            cur_cost_local = best_cost;
                            has_optimal = true;
                            server_add_num = 0;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {

                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }
                }
                else
                {
                    cur_cost_local = best_cost;
                    ret = FindCurOptimal_Links();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < cur_cost_local)
                        {
                            cur_cost_local = best_cost;
                            has_optimal = true;
                            server_add_num = 0;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {

                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }
                }

                server_add_num++;

                if (!has_optimal && server_add_num>2) // 如果没有改进,尝试三次
                {
                    break;
                }
            } while (true);

            return ret;
        }

        cdnStatus RemoveOneServerAndFind()
        {
            cdnStatus ret = CDN_OK;

            int server_delete_num = 0;

            do 
            {
                bool has_optimal = false;
                IntVector vec_servers_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec2_servers.begin(), mvec2_servers.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec2_cur_sol.begin(), mvec2_cur_sol.end());

                int cur_server;
                int cur_cost_local = best_cost;

                int select_server = INVALID_NODE;
                int temp_ = INT_MAX;

                vector<LinkE> vec_server_flow;

                // 选择边最少的服务节点
                for (size_t i = 0; i < vec_servers_.size(); ++i)
                {
                    cur_server = vec_servers_[i];

                    if (mvec2_set_server_fix[cur_server])
                    {
                        continue;
                    }

                    int flow_supply_ = 0;

                    // 是否挂载消费节点
                    if (ins->connect_consumer[cur_server] > -1)
                    {
                        flow_supply_ += ins->connect_consumer_req[cur_server];
                    }

                    for (int k=0; k<ins->linked_edges[cur_server];++k)
                    {
                        flow_supply_ += ins->inc_cost[cur_server][ins->bfs_node[cur_server][k + 1]];
                    }

                    vec_server_flow.push_back(LinkE(cur_server, flow_supply_));
                }

                if (m_big_scale)
                {
                    sort(vec_server_flow.begin(), vec_server_flow.end(), cmp_less);
                }

                cur_cost_local = best_cost;
                for (size_t i=0; i<vec_server_flow.size(); ++i)
                {
                    if (m_big_scale)
                    {
                        if ((double)clock() > m_time_end)
                        {
                            return CDN_TIME_OUT;
                        }
                    }

                    // 删除节点,然后使用最小费用流求解
                    int cur_del_ = vec_server_flow[i].index;
                    IntVector::iterator it = mvec2_servers.begin();
                    while (it != mvec2_servers.end())
                    {
                        if (*it == cur_del_)
                        {
                            mvec2_servers.erase(it);
                            mvec2_cur_sol[cur_del_] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                        }
                    } // delete one server
       
                    Reinit3();
                    ret = FindAllFlow_MinCost();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < cur_cost_local)
                        {
                            cur_cost_local = best_cost;
                            select_server = cur_del_;
                            server_delete_num = 0;
                            has_optimal = true;
                        }
                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    mvec2_servers.push_back(cur_del_);
                    mvec2_cur_sol[cur_del_] = true;
                    server_num++;

                    if (m_big_scale && i>20)
                    {
                        break;
                    }
                }

                if (select_server != INVALID_NODE)
                {
                    // 删除当前服务节点
                    IntVector::iterator it = mvec2_servers.begin();
                    while (it != mvec2_servers.end())
                    {
                        if (*it == select_server)
                        {
                            mvec2_servers.erase(it);
                            mvec2_cur_sol[select_server] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                        }
                    } // delete one server

                    cur_cost_local = best_cost;
                    ret = FindCurOptimal_Links();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < cur_cost_local)
                        {
                            cur_cost_local = best_cost;
                            select_server = cur_server;
                            server_delete_num = 0;
                            has_optimal = true;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {

                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    OUTPUT_INFO(cout << "remove one server, " << mvec2_servers.size() << "\n";)
                }
                else
                {
                    cur_cost_local = best_cost;
                    ret = FindCurOptimal_Links();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < cur_cost_local)
                        {
                            cur_cost_local = best_cost;
                            select_server = cur_server;
                            server_delete_num = 0;
                            has_optimal = true;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {

                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }
                }

                server_delete_num++;

                if (!has_optimal && server_delete_num>3)
                {
                    break;
                }
            } while (true);

            return ret;
        }

        cdnStatus AddAndRemoveOneServerForBS()
        {
            cdnStatus ret = CDN_OK;

            do 
            {
                bool has_optimal = false;
                int optimal_add = best_cost;
                int optimal_del = best_cost;

                int select_add_server = INVALID_NODE;
                int select_del_server = INVALID_NODE;

                IntVector vec_servers_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec2_servers.begin(), mvec2_servers.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec2_cur_sol.begin(), mvec2_cur_sol.end());

                vector<LinkE> vec_non_server_flow_;
                for (size_t i = 0; i < mvec_server_candates.size(); ++i)
                {
                    int cur_server = mvec_server_candates[i];
                    if (!vec_cur_sol_[cur_server] && !mvec2_cur_sol[cur_server])
                    {
                        int inflow_ = 0;
                        int cur_node_;
                        for (int k = 0; k < ins->linked_edges[cur_server]; ++k)
                        {
                            cur_node_ = ins->bfs_node[cur_server][k + 1];
                            if (ins->inc_cost[cur_node_][cur_server] > 0)
                            {
                                inflow_ += ins->inc_cost[cur_node_][cur_server];
                            }
                        }

                        vec_non_server_flow_.push_back(LinkE(cur_server, inflow_));
                    }
                }

                int real_add_times_ = 0;
                sort(vec_non_server_flow_.begin(), vec_non_server_flow_.end(), cmp);
                for (size_t i = 0; i < vec_non_server_flow_.size(); ++i)
                {
                    if ((double)clock() > m_time_end)
                    {
                        return CDN_TIME_OUT;
                    }

                    // 增加流经流量最多的点为服务器,然后调用最小费用流算法
                    int cur_add_ = vec_non_server_flow_[i].index;
                    if (mvec2_has_added[cur_add_] && m_big_scale)
                    {
                        continue;
                    }

                    mvec2_servers.push_back(cur_add_);
                    mvec2_cur_sol[cur_add_] = true;
                    server_num++;

                    real_add_times_++;
                    Reinit3();
                    ret = FindAllFlow_MinCost();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < optimal_add)
                        {
                            optimal_add = best_cost;
                            select_add_server = cur_add_;
                            has_optimal = true;
                        }
                        else
                        {
                            mvec2_has_added[cur_add_] = true;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {
                        mvec2_has_added[cur_add_] = true;
                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    mvec2_servers.pop_back();
                    mvec2_cur_sol[cur_add_] = false;
                    server_num--;

                    if (real_add_times_ > 10)
                    {
                        break;
                    }
                }

                // 删除服务器
                vector<LinkE> vec_server_flow;

                // 选择边最少的服务节点
                for (size_t i = 0; i < vec_servers_.size(); ++i)
                {
                    int cur_server = vec_servers_[i];

                    if (mvec2_set_server_fix[cur_server])
                    {
                        continue;
                    }

                    int flow_supply_ = 0;

                    // 是否挂载消费节点
                    if (ins->connect_consumer[cur_server] > -1)
                    {
                        flow_supply_ += ins->connect_consumer_req[cur_server];
                    }

                    for (int k = 0; k < ins->linked_edges[cur_server]; ++k)
                    {
                        flow_supply_ += ins->inc_cost[cur_server][ins->bfs_node[cur_server][k + 1]];
                    }

                    vec_server_flow.push_back(LinkE(cur_server, flow_supply_));
                }
                sort(vec_server_flow.begin(), vec_server_flow.end(), cmp_less);

                int real_del_times_ = 0;
                for (size_t i = 0; i < vec_server_flow.size(); ++i)
                {
                    if ((double)clock() > m_time_end)
                    {
                        return CDN_TIME_OUT;
                    }

                    // 删除节点,然后使用最小费用流求解
                    int cur_del_ = vec_server_flow[i].index;
                    if (mvec2_has_deleted[cur_del_] && m_big_scale)
                    {
                        continue;
                    }

                    IntVector::iterator it = mvec2_servers.begin();
                    while (it != mvec2_servers.end())
                    {
                        if (*it == cur_del_)
                        {
                            mvec2_servers.erase(it);
                            mvec2_cur_sol[cur_del_] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                        }
                    } // delete one server

                    real_del_times_++;
                    Reinit3();
                    ret = FindAllFlow_MinCost();
                    if (ret == CDN_OK)
                    {
                        if (best_cost < optimal_del)
                        {
                            optimal_del = best_cost;
                            select_del_server = cur_del_;
                            has_optimal = true;
                        }
                        else
                        {
                            mvec2_has_deleted[cur_del_] = true;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {
                        mvec2_has_deleted[cur_del_] = true;
                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    mvec2_servers.push_back(cur_del_);
                    mvec2_cur_sol[cur_del_] = true;
                    server_num++;

                    if (real_del_times_ > 10)
                    {
                        break;
                    }
                }

                // 选择需要进行的操作
                OUTPUT_INFO(cout << "del " << optimal_del << " add " << optimal_add << endl;)
                if (!has_optimal)
                {
                    OUTPUT_INFO(cout << "no optimal\n";)
                    ret = FindCurOptimal_Links();
                    if (ret == CDN_OK)
                    {

                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {

                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }
                    break;
                }
                else if (optimal_add <= optimal_del)
                {
                    mvec2_servers.push_back(select_add_server);
                    mvec2_cur_sol[select_add_server] = true;
                    server_num++;
                    OUTPUT_INFO(cout << "add server " << select_add_server << "\n";)
                }
                else
                {
                    IntVector::iterator it = mvec2_servers.begin();
                    while (it != mvec2_servers.end())
                    {
                        if (*it == select_del_server)
                        {
                            mvec2_servers.erase(it);
                            mvec2_cur_sol[select_del_server] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                        }
                    } // delete one server
                    OUTPUT_INFO(cout << "del server " << select_del_server << "\n";)
                }

                ret = FindCurOptimal_Links();
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }
            } while (true);

            return ret;
        }

        cdnStatus FindCurOptimal_Links()
        {
            cdnStatus ret = CDN_OK;

            int temp_cost = best_cost;

            int iter = 0;

            //int success_times = 0;
            //clock_t time_e;

            do
            {
                IntVector vec_servers_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec2_servers.begin(), mvec2_servers.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec2_cur_sol.begin(), mvec2_cur_sol.end());

                int cur_server;
                int cur_node;

                int select_server = INVALID_NODE;
                int select_node = INVALID_NODE;

                int temp_s;

                for (int i = 0; i < ins->nodes + 2; ++i)
                {
                    for (int j = 0; j < ins->nodes + 2; ++j)
                    {
                        flow_S[i][j] = ins->inc_cost[i][j];//TODO
                    }
                }

                for (size_t i = 0; i < vec_servers_.size(); ++i)
                {
                    cur_server = vec_servers_[i];

                    bool is_move = !mvec2_set_server[cur_server];

                    if (m_running_mode == CRM_REPEAT_MODE)
                    {
                        is_move = !mvec2_set_server_fix[cur_server];
                    }

                    if (is_move)
                    {
                        for (int j = 1; j <= ins->linked_edges[cur_server]; ++j)
                        {
                            if ((double)clock() > m_time_end)
                            {
                                return CDN_TIME_OUT;
                            }

                            cur_node = ins->bfs_node[cur_server][j];

                            // 计算当前节点是否可以作为新的服务点
                            if (!vec_cur_sol_[cur_node])
                            {
                                int cur_ser_out_flow = 0;
                                int cur_node_out_flow = 0;

                                for (int k = 0; k < ins->nodes; ++k)
                                {
                                    if (flow_S[cur_server][k] > 0)
                                    {
                                        cur_ser_out_flow += flow_S[cur_server][k];
                                    }

                                    if (ins->capacity[cur_node][k] > 0)
                                    {
                                        cur_node_out_flow += ins->capacity[cur_node][k];
                                    }
                                }

                                bool adj_has_no_ser = true;
                                for (int l=0; l<ins->linked_edges[cur_node]; ++l)
                                {
                                    int cur_node_adj = ins->bfs_node[cur_node][l + 1];

                                    if (cur_node_adj == cur_server)
                                    {
                                        continue;
                                    }

                                    if (vec_cur_sol_[cur_node_adj])
                                    {
                                        adj_has_no_ser = false;
                                    }
                                }

                                bool is_swap = cur_node_out_flow >= cur_ser_out_flow || m_running_mode == CRM_REPEAT_MODE;
                                if (m_big_scale)
                                {
                                    is_swap = adj_has_no_ser && cur_node_out_flow >= cur_ser_out_flow && m_search_list[cur_server][cur_node] > 0
                                        || m_running_mode == CRM_REPEAT_MODE;
                                }

                                if (is_swap)
                                {
                                    temp_s = mvec2_servers[i];
                                    mvec2_cur_sol[mvec2_servers[i]] = false;
                                    mvec2_servers[i] = cur_node;
                                    mvec2_cur_sol[mvec2_servers[i]] = true;

                                    iter++;
                                    Reinit3();
                                    ret = FindAllFlow_MinCost();
                                    if (ret == CDN_OK)
                                    {
                                        if (best_cost < temp_cost)
                                        {
                                            temp_cost = best_cost;
                                            select_server = cur_server;
                                            select_node = cur_node;
                                        }
                                        else
                                        {
                                            m_search_list[cur_server][cur_node] = 0;
                                        }
                                    }
                                    else if (ret == CDN_FIND_SERVER_FAILED)
                                    {
                                        m_search_list[cur_server][cur_node] = 0;
                                    }

                                    mvec2_cur_sol[mvec2_servers[i]] = false;
                                    mvec2_servers[i] = temp_s;
                                    mvec2_cur_sol[mvec2_servers[i]] = true;
                                }
                            }
                        }
                    }

                    /*time_e = clock();
                    if ((double)time_e > time_end)
                    {
                        return CDN_TIME_OUT;
                    }*/
                }

                if (select_server == INVALID_NODE)
                {
                    break;
                }
                else
                {
                    OUTPUT_INFO(cout << "find a solution" << "\n";);
                    for (size_t i = 0; i < mvec2_servers.size(); ++i)
                    {
                        if (mvec2_servers[i] == select_server)
                        {
                            mvec2_servers[i] = select_node;
                            break;
                        }
                    }
                    mvec2_cur_sol[select_server] = false;
                    mvec2_cur_sol[select_node] = true;
                }
            } while (true);

            OUTPUT_INFO(cout << "iter times: " << iter << "\n";)

            return ret;
        }

        bool IsSolutionValid3(int* cur_invalid_cons, int* flow_needed)
        {
            int cur_node_connect_s = 0;
            for (int i = 0; i < ins->consumers; ++i)
            {
                cur_node_connect_s = ins->server_conn[i];
                if (mvec2_cur_sol[cur_node_connect_s])
                {
                    continue; // 连接消费结点的网络结点已选中为服务器放置地点
                }

                int inflow = 0;
                int outflow = 0;

                for (int j = 0; j < ins->nodes; ++j)
                {
                    inflow += ins->flow[j][cur_node_connect_s];
                    outflow += ins->flow[cur_node_connect_s][j];
                }

                if (inflow - outflow < ins->connect_consumer_req[cur_node_connect_s])
                {
                    *cur_invalid_cons = cur_node_connect_s;
                    *flow_needed = ins->connect_consumer_req[cur_node_connect_s] - (inflow - outflow);
                    return false;
                }
            }

            return true;
        }

        cdnStatus Reinit3()
        {
            mvec_cur_paths.clear();

            cur_cost = INT_MAX;

            for (int i = 0; i < ins->nodes + 2; ++i)
            {
                for (int j = 0; j < ins->nodes + 2; ++j)
                {
                    if (ins->flow[i][j] > 0)
                    {
                        ins->flow[i][j] = 0;
                    }
                }
            }

            mvec2_lack_flow.clear();
            mvec2_lack_flow.resize(ins->nodes, 0);

            mvec2_cons_flow.clear();
            mvec2_cons_flow.resize(ins->nodes, 0);

            mvec2_cons_cost.clear();
            mvec2_cons_cost.resize(ins->nodes, 0);

            return CDN_OK;
        }

        void OutputServers(bool has_seq=false)
        {
            ofstream out_file;
            out_file.open("servers.txt");

            if (out_file.is_open())
            {
                if (has_seq)
                {
                    for (size_t i = 0; i < mvec2_cur_sol.size(); ++i)
                    {
                        if (mvec2_cur_sol[i])
                        {
                            out_file << i << " ";
                        }
                    }
                }
                else
                {
                    for (size_t i = 0; i < mvec2_servers.size(); ++i)
                    {
                        out_file << mvec2_servers[i] << " ";
                    }
                }

                out_file.close();
            }
        }

        void GetCostOfCons(vector<LinkE>& vec_cost)
        {
            IntVector vec_cons_flow(ins->consumers, 0);
            IntVector vec_cons_cost(ins->consumers, 0);

            for (size_t i = 0; i < mvec_cur_paths.size(); ++i)
            {
                IntVector& vec_path = mvec_cur_paths[i];

                size_t nsize = vec_path.size();
                int cons_ = vec_path[nsize - 2];
                int flow_ = vec_path[nsize - 1];

                if (vec_path[1] == -1)
                {
                    vec_cons_cost[cons_] = ins->server_cost;
                }
                else
                {
                    for (size_t j = 0; j < nsize - 2; ++j)
                    {
                        if (vec_path[j+1] == -1)
                        {
                            break;
                        }

                        vec_cons_cost[cons_] += ins->cost[vec_path[j]][vec_path[j + 1]] * flow_;
                    }
                }
                
                vec_cons_flow[cons_] += flow_;
            }

            for (int i=0; i<ins->consumers; ++i)
            {
                vec_cost.push_back(LinkE(i, vec_cons_cost[i]));
            }
        }

        bool ValidSolution3(int** flow_matrix)
        {
            bool ret = true;

            for (int i = 0; i < ins->nodes; ++i)
            {
                for (int j = 0; j<ins->nodes; ++j)
                {
                    if (flow_matrix[i][j] > ins->capacity[i][j])
                    {
                        OUTPUT_INFO(cout << "edge[" << i << "," << j << "] error flow, exceed\n";)
                        ret = false;
                    }
                }
            }

            return ret;
        }

        void OutputServerNonmove(string strfile)
        {
            ofstream out_server;
            out_server.open(strfile);

            if (out_server.is_open())
            {
                out_server << "non-move:\n";
                for (size_t i = 0; i < mvec2_set_server.size(); ++i)
                {
                    if (mvec2_set_server[i])
                    {
                        out_server << i << " ";
                    }
                }

                out_server << "\n\nmust non-move:\n";

                for (size_t i = 0; i < mvec2_set_server_fix.size(); ++i)
                {
                    if (mvec2_set_server_fix[i])
                    {
                        out_server << i << " ";
                    }
                }

                out_server << "\n";

                out_server.close();
            }
        }

        void PrintTime(string strcont = "")
        {
            m_time_cur = clock();
            double time_int = (double)(m_time_cur - m_time_b) / CLOCKS_PER_SEC;
            cout << strcont << " time: " << time_int << "\n\n";
        }

#ifndef OLD_UPDATE_FLOW
        bool DijkstraPath(int start_, int* end_, int n)
        {
            int ret = -1;

            BoolVector vec_visited(n, false);
            path[start_] = -1;

            for (int i = 0; i < n; ++i)
            {
                if (ins->cost[start_][i] > 0)
                {
                    //dist[i] = ins->cost[start_][i];
                    dist[i] = INT_MAX;
                    path[i] = start_;
                }
                else
                {
                    dist[i] = INT_MAX;
                    path[i] = -1;
                }
            }
            dist[start_] = 0;

            h.clear();
            h.insert(start_);
            while (!h.empty())
            {
                start_ = *h.begin();
                if (mvec2_cur_sol[start_])
                {
                    *end_ = start_;
                    return true;
                    //return dist[start_];
                }

                h.erase(h.begin());

                if (vec_visited[start_])
                {
                    continue;
                }
                vec_visited[start_] = true;

                for (int i = 0; i < n; ++i)
                {
                    if (!vec_visited[i] && dist[i] > dist[start_] + ins->cost[start_][i] &&
                        ins->capacity[i][start_] > ins->flow[i][start_])
                    {
                        //h.erase(i);
                        dist[i] = dist[start_] + ins->cost[start_][i];
                        path[i] = start_;
                        h.insert(i);
                    }
                }
            }

            return false;
        }
#endif

        bool* inq;
        int* d;
        int* a;
        int* pre;

        int** flow_S;
        int** m_search_list;

        double m_time_end;
        clock_t m_time_b;
        clock_t m_time_cur;

        IntVector mvec2_servers;
        BoolVector mvec2_cur_sol;

        BoolVector mvec2_has_deleted;
        BoolVector mvec2_has_added;

        BoolVector mvec2_set_server;
        BoolVector mvec2_set_server_fix;

        BoolVector mvec2_lack_flow;

        IntVector mvec2_cons_cost;  // 消费结点的开销
        IntVector mvec2_cons_flow;  // 消费结点获得的流

        vector<LinkE> mvec2_vec_cost;

        IntVector mvec2_servers_best;
        BoolVector mvec2_sol_best;
        vector<IntVector> mvec2_G_best;
        vector<Edge> mvec2_edges_best;
    };

} // namespace cdn

#endif // CDN_SOLUTION_H
