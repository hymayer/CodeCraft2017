#ifndef CDN_SOLUTION3_H
#define CDN_SOLUTION3_H

#include "solution.h"
#include <set>

//#define OUTPUT_DEBUG_FILE

#define OLD_UPDATE_FLOW3
#ifndef OLD_UPDATE_FLOW3
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
    enum nsStatus
    {
        NS_OK,
        NS_ERROR,
        NS_OPTIMAL,
        NS_UNBOUND,
        NS_INFEASI
    };

    enum nsArcState
    {
        STATE_UPPER = -1,
        STATE_TREE = 0,
        STATE_LOWER = 1
    };

    enum nsArcDirection
    {
        DIR_DOWN = -1,
        DIR_UP = 1
    };

    class NetworkSimplex
    {
        // 网络单纯性算法,参考lemon实现
    public:
        NetworkSimplex(const Digraph& graph)
            : m_graph(graph)
            , MAX(std::numeric_limits<int>::max())
            , INF(std::numeric_limits<int>::has_infinity ? std::numeric_limits<int>::infinity() : MAX)
        {
            m_node_id.resize(m_graph.NodeSize());
            m_arc_id.resize(m_graph.ArcSize());

            Reset();
        }

        nsStatus SetData(IntVector& supply, IntVector& lower, IntVector& upper, IntVector& cost)
        {
            m_has_lower = true;
            for (ArcIt a(m_graph); a.ID() != INVALID_TAG; ++a)
            {
                mvec_lower[m_arc_id[a.ID()]] = lower[a.ID()];
                mvec_upper[m_arc_id[a.ID()]] = upper[a.ID()];
                mvec_cost[m_arc_id[a.ID()]] = cost[a.ID()];
            }

            for (NodeIt n(m_graph); n.ID() != INVALID_TAG; ++n)
            {
                mvec_supply[m_node_id[n.ID()]] = supply[n.ID()];
            }

            return NS_OK;
        }

        void GetFlow(IntVector &map) const
        {
            for (ArcIt a(m_graph); a.ID() != INVALID_TAG; ++a)
            {
                map[a.ID()] = mvec_flow[m_arc_id[a.ID()]];
            }
        }

        int GetEdgeFlow(int arc_id, int* source) const
        {
            *source = m_graph.source(Arc(arc_id)).ID();

            int flow_in = 0;
            for (InArcIt a(m_graph, Node(*source)); a.ID() != INVALID_TAG; ++a)
            {
                flow_in += mvec_flow[m_arc_id[a.ID()]];
            }

            int flow_out = 0;
            for (OutArcIt a(m_graph, Node(*source)); a.ID() != INVALID_TAG; ++a)
            {
                flow_out += mvec_flow[m_arc_id[a.ID()]];
            }

            return flow_in-flow_out;
        }

        int GetEdgeSource(int arc_id) const
        {
            return mvec_source[m_arc_id[arc_id]];
        }

        int GetSourceFlow(int arc_id) const
        {
            return mvec_flow[m_arc_id[arc_id]];
        }

        void GetFlowToMatrix(int** flow_) const
        {
            for (ArcIt a(m_graph); a.ID() != INVALID_TAG; ++a)
            {
                int sor_ = m_graph.source(a).ID();
                int tar_ = m_graph.target(a).ID();

                flow_[sor_][tar_] = mvec_flow[m_arc_id[a.ID()]];
            }
        }

        int GetCost() const
        {
            int c = 0;

            for (ArcIt a(m_graph); a.ID() != INVALID_TAG; ++a)
            {
                int i = m_arc_id[a.ID()];
                c += int(mvec_flow[i]) * int(mvec_cost[i]);
            }

            return c;
        }

        nsStatus Run()
        {
            if (!InitSol())
            {
                return NS_INFEASI;
            }

            if (!InitSPTData())
            {
                return NS_UNBOUND;
            }

            while (FindEnteringArc())
            {
                FindJoinNode();
                bool change = FindLeavingArc();
                if (delta >= MAX)
                {
                    return NS_UNBOUND;
                }

                UpdateFlow(change);
                if (change)
                {
                    UpdateSPTData();
                    UpdatePhi();
                }
            }

            for (int e = m_search_arc_num; e != m_all_arc_num; ++e)
            {
                if (mvec_flow[e] != 0)
                {
                    return NS_INFEASI;
                }
            }

            if (m_has_lower)
            {
                for (int i = 0; i != m_arc_num; ++i)
                {
                    int c = mvec_lower[i];
                    if (c != 0)
                    {
                        mvec_flow[i] += c;
                        mvec_supply[mvec_source[i]] += c;
                        mvec_supply[mvec_target[i]] -= c;
                    }
                }
            }

            if (m_sum_supply == 0)
            {
                int max_pot = -std::numeric_limits<int>::max();
                for (int i = 0; i != m_node_num; ++i)
                {
                    if (mvec_phi[i] > max_pot)
                    {
                        max_pot = mvec_phi[i];
                    }
                }
                if (max_pot > 0)
                {
                    for (int i = 0; i != m_node_num; ++i)
                    {
                        mvec_phi[i] -= max_pot;
                    }
                }
            }

            return NS_OPTIMAL;
        }

        bool InitSol()
        {
            if (m_node_num == 0)
            {
                return false;
            }

            m_sum_supply = 0;
            for (int i = 0; i != m_node_num; ++i)
            {
                m_sum_supply += mvec_supply[i];
            }

            assert(m_sum_supply == 0);

            if (m_has_lower)
            {
                for (int i = 0; i != m_arc_num; ++i)
                {
                    int c = mvec_lower[i];
                    if (c >= 0)
                    {
                        mvec_cap[i] = mvec_upper[i] < MAX ? mvec_upper[i] - c : INF;
                    }
                    else
                    {
                        mvec_cap[i] = mvec_upper[i] < MAX + c ? mvec_upper[i] - c : INF;
                    }
                    mvec_supply[mvec_source[i]] -= c;
                    mvec_supply[mvec_target[i]] += c;
                }
            }
            else
            {
                for (int i = 0; i != m_arc_num; ++i)
                {
                    mvec_cap[i] = mvec_upper[i];
                }
            }

            int artifical_cost;
            if (std::numeric_limits<int>::is_exact)
            {
                artifical_cost = std::numeric_limits<int>::max() / 2 + 1;
            }
            else
            {
                artifical_cost = 0;
                for (int i = 0; i != m_arc_num; ++i)
                {
                    if (mvec_cost[i] > artifical_cost) artifical_cost = mvec_cost[i];
                }
                artifical_cost = (artifical_cost + 1) * m_node_num;
            }

            for (int i = 0; i != m_arc_num; ++i)
            {
                mvec_flow[i] = 0;
                m_spt_state[i] = STATE_LOWER;
            }

            m_spt_root = m_node_num;
            m_spt_parent[m_spt_root] = -1;
            m_spt_pred[m_spt_root] = -1;
            m_spt_thread[m_spt_root] = 0;
            m_spt_rev_thread[0] = m_spt_root;
            m_spt_succ_num[m_spt_root] = m_node_num + 1;
            m_spt_last_succ[m_spt_root] = m_spt_root - 1;
            mvec_supply[m_spt_root] = -m_sum_supply;
            mvec_phi[m_spt_root] = 0;

            if (m_sum_supply == 0)
            {
                m_search_arc_num = m_arc_num;
                m_all_arc_num = m_arc_num + m_node_num;
                for (int u = 0, e = m_arc_num; u != m_node_num; ++u, ++e)
                {
                    m_spt_parent[u] = m_spt_root;
                    m_spt_pred[u] = e;
                    m_spt_thread[u] = u + 1;
                    m_spt_rev_thread[u + 1] = u;
                    m_spt_succ_num[u] = 1;
                    m_spt_last_succ[u] = u;
                    mvec_cap[e] = INF;
                    m_spt_state[e] = STATE_TREE;
                    if (mvec_supply[u] >= 0)
                    {
                        m_spt_pred_dir[u] = DIR_UP;
                        mvec_phi[u] = 0;
                        mvec_source[e] = u;
                        mvec_target[e] = m_spt_root;
                        mvec_flow[e] = mvec_supply[u];
                        mvec_cost[e] = 0;
                    }
                    else
                    {
                        m_spt_pred_dir[u] = DIR_DOWN;
                        mvec_phi[u] = artifical_cost;
                        mvec_source[e] = m_spt_root;
                        mvec_target[e] = u;
                        mvec_flow[e] = -mvec_supply[u];
                        mvec_cost[e] = artifical_cost;
                    }
                }
            }

            return true;
        }

        void FindJoinNode()
        {
            int u = mvec_source[m_t_in_arc];
            int v = mvec_target[m_t_in_arc];
            while (u != v)
            {
                if (m_spt_succ_num[u] < m_spt_succ_num[v])
                {
                    u = m_spt_parent[u];
                }
                else
                {
                    v = m_spt_parent[v];
                }
            }
            m_t_join = u;
        }

        bool FindEnteringArc()
        {
            int c, min = 0;
            int cnt = m_p_block_size;
            int e;
            for (e = m_p_next_arc; e != m_search_arc_num; ++e)
            {
                c = m_spt_state[e] * (mvec_cost[e] + mvec_phi[mvec_source[e]] - mvec_phi[mvec_target[e]]);
                if (c < min)
                {
                    min = c;
                    m_t_in_arc = e;
                }
                if (--cnt == 0)
                {
                    if (min < 0) goto search_end;
                    cnt = m_p_block_size;
                }
            }

            for (e = 0; e != m_p_next_arc; ++e)
            {
                c = m_spt_state[e] * (mvec_cost[e] + mvec_phi[mvec_source[e]] - mvec_phi[mvec_target[e]]);
                if (c < min)
                {
                    min = c;
                    m_t_in_arc = e;
                }
                if (--cnt == 0)
                {
                    if (min < 0) goto search_end;
                    cnt = m_p_block_size;
                }
            }
            if (min >= 0)
            {
                return false;
            }

        search_end:
            m_p_next_arc = e;
            return true;
        }

        bool FindLeavingArc()
        {
            int first, second;
            if (m_spt_state[m_t_in_arc] == STATE_LOWER)
            {
                first = mvec_source[m_t_in_arc];
                second = mvec_target[m_t_in_arc];
            }
            else
            {
                first = mvec_target[m_t_in_arc];
                second = mvec_source[m_t_in_arc];
            }
            delta = mvec_cap[m_t_in_arc];
            int result = 0;
            int c, d;
            int e;

            for (int u = first; u != m_t_join; u = m_spt_parent[u])
            {
                e = m_spt_pred[u];
                d = mvec_flow[e];
                if (m_spt_pred_dir[u] == DIR_DOWN)
                {
                    c = mvec_cap[e];
                    d = c >= MAX ? INF : c - d;
                }

                if (d < delta)
                {
                    delta = d;
                    m_t_u_out = u;
                    result = 1;
                }
            }

            for (int u = second; u != m_t_join; u = m_spt_parent[u])
            {
                e = m_spt_pred[u];
                d = mvec_flow[e];
                if (m_spt_pred_dir[u] == DIR_UP)
                {
                    c = mvec_cap[e];
                    d = c >= MAX ? INF : c - d;
                }

                if (d <= delta)
                {
                    delta = d;
                    m_t_u_out = u;
                    result = 2;
                }
            }

            if (result == 1)
            {
                m_t_u_in = first;
                m_t_v_in = second;
            }
            else
            {
                m_t_u_in = second;
                m_t_v_in = first;
            }

            return result != 0;
        }

        void UpdateFlow(bool change)
        {
            if (delta > 0)
            {
                int val = m_spt_state[m_t_in_arc] * delta;
                mvec_flow[m_t_in_arc] += val;
                for (int u = mvec_source[m_t_in_arc]; u != m_t_join; u = m_spt_parent[u])
                {
                    mvec_flow[m_spt_pred[u]] -= m_spt_pred_dir[u] * val;
                }

                for (int u = mvec_target[m_t_in_arc]; u != m_t_join; u = m_spt_parent[u])
                {
                    mvec_flow[m_spt_pred[u]] += m_spt_pred_dir[u] * val;
                }
            }

            if (change)
            {
                m_spt_state[m_t_in_arc] = STATE_TREE;
                m_spt_state[m_spt_pred[m_t_u_out]] = (mvec_flow[m_spt_pred[m_t_u_out]] == 0) ? STATE_LOWER : STATE_UPPER;
            }
            else
            {
                m_spt_state[m_t_in_arc] = -m_spt_state[m_t_in_arc];
            }
        }

        void UpdateSPTData()
        {
            int old_rev_thread = m_spt_rev_thread[m_t_u_out];
            int old_succ_num = m_spt_succ_num[m_t_u_out];
            int old_last_succ = m_spt_last_succ[m_t_u_out];
            m_t_v_out = m_spt_parent[m_t_u_out];

            if (m_t_u_in == m_t_u_out)
            {
                m_spt_parent[m_t_u_in] = m_t_v_in;
                m_spt_pred[m_t_u_in] = m_t_in_arc;
                m_spt_pred_dir[m_t_u_in] = m_t_u_in == mvec_source[m_t_in_arc] ? DIR_UP : DIR_DOWN;

                if (m_spt_thread[m_t_v_in] != m_t_u_out)
                {
                    int after = m_spt_thread[old_last_succ];
                    m_spt_thread[old_rev_thread] = after;
                    m_spt_rev_thread[after] = old_rev_thread;
                    after = m_spt_thread[m_t_v_in];
                    m_spt_thread[m_t_v_in] = m_t_u_out;
                    m_spt_rev_thread[m_t_u_out] = m_t_v_in;
                    m_spt_thread[old_last_succ] = after;
                    m_spt_rev_thread[after] = old_last_succ;
                }
            }
            else
            {
                int thread_continue = old_rev_thread == m_t_v_in ?
                    m_spt_thread[old_last_succ] : m_spt_thread[m_t_v_in];

                int stem = m_t_u_in;
                int par_stem = m_t_v_in;
                int next_stem;
                int last = m_spt_last_succ[m_t_u_in];
                int before, after = m_spt_thread[last];
                m_spt_thread[m_t_v_in] = m_t_u_in;
                m_spt_dirty_revs.clear();
                m_spt_dirty_revs.push_back(m_t_v_in);

                while (stem != m_t_u_out)
                {
                    next_stem = m_spt_parent[stem];
                    m_spt_thread[last] = next_stem;
                    m_spt_dirty_revs.push_back(last);

                    before = m_spt_rev_thread[stem];
                    m_spt_thread[before] = after;
                    m_spt_rev_thread[after] = before;

                    m_spt_parent[stem] = par_stem;
                    par_stem = stem;
                    stem = next_stem;

                    last = m_spt_last_succ[stem] == m_spt_last_succ[par_stem] ?
                        m_spt_rev_thread[par_stem] : m_spt_last_succ[stem];
                    after = m_spt_thread[last];
                }

                m_spt_parent[m_t_u_out] = par_stem;
                m_spt_thread[last] = thread_continue;
                m_spt_rev_thread[thread_continue] = last;
                m_spt_last_succ[m_t_u_out] = last;

                if (old_rev_thread != m_t_v_in)
                {
                    m_spt_thread[old_rev_thread] = after;
                    m_spt_rev_thread[after] = old_rev_thread;
                }

                for (int i = 0; i != int(m_spt_dirty_revs.size()); ++i)
                {
                    int u = m_spt_dirty_revs[i];
                    m_spt_rev_thread[m_spt_thread[u]] = u;
                }

                int tmp_sc = 0, tmp_ls = m_spt_last_succ[m_t_u_out];
                for (int u = m_t_u_out, p = m_spt_parent[u]; u != m_t_u_in; u = p, p = m_spt_parent[u])
                {
                    m_spt_pred[u] = m_spt_pred[p];
                    m_spt_pred_dir[u] = -m_spt_pred_dir[p];
                    tmp_sc += m_spt_succ_num[u] - m_spt_succ_num[p];
                    m_spt_succ_num[u] = tmp_sc;
                    m_spt_last_succ[p] = tmp_ls;
                }

                m_spt_pred[m_t_u_in] = m_t_in_arc;
                m_spt_pred_dir[m_t_u_in] = m_t_u_in == mvec_source[m_t_in_arc] ? DIR_UP : DIR_DOWN;
                m_spt_succ_num[m_t_u_in] = old_succ_num;
            }

            int up_limit_out = m_spt_last_succ[m_t_join] == m_t_v_in ? m_t_join : -1;
            int last_succ_out = m_spt_last_succ[m_t_u_out];
            for (int u = m_t_v_in; u != -1 && m_spt_last_succ[u] == m_t_v_in; u = m_spt_parent[u])
            {
                m_spt_last_succ[u] = last_succ_out;
            }

            if (m_t_join != old_rev_thread && m_t_v_in != old_rev_thread)
            {
                for (int u = m_t_v_out; u != up_limit_out && m_spt_last_succ[u] == old_last_succ;
                u = m_spt_parent[u])
                {
                    m_spt_last_succ[u] = old_rev_thread;
                }
            }
            else if (last_succ_out != old_last_succ)
            {
                for (int u = m_t_v_out; u != up_limit_out && m_spt_last_succ[u] == old_last_succ;
                u = m_spt_parent[u])
                {
                    m_spt_last_succ[u] = last_succ_out;
                }
            }

            for (int u = m_t_v_in; u != m_t_join; u = m_spt_parent[u])
            {
                m_spt_succ_num[u] += old_succ_num;
            }

            for (int u = m_t_v_out; u != m_t_join; u = m_spt_parent[u])
            {
                m_spt_succ_num[u] -= old_succ_num;
            }
        }

        void UpdatePhi()
        {
            int sigma = mvec_phi[m_t_v_in] - mvec_phi[m_t_u_in] - m_spt_pred_dir[m_t_u_in] * mvec_cost[m_t_in_arc];

            int end = m_spt_thread[m_spt_last_succ[m_t_u_in]];
            for (int u = m_t_u_in; u != end; u = m_spt_thread[u])
            {
                mvec_phi[u] += sigma;
            }
        }

        bool InitSPTData()
        {
            const double BLOCK_SIZE_FACTOR = 1.0;
            const int MIN_BLOCK_SIZE = 10;

            m_p_block_size = std::max(int(BLOCK_SIZE_FACTOR *
                std::sqrt(double(m_search_arc_num))), MIN_BLOCK_SIZE);
            m_p_next_arc = 0;

            int curr, total = 0;
            vector<Node> supply_nodes, demand_nodes;
            for (NodeIt u(m_graph); u.ID() != INVALID_TAG; ++u)
            {
                curr = mvec_supply[m_node_id[u.ID()]];
                if (curr > 0)
                {
                    total += curr;
                    supply_nodes.push_back(u);
                }
                else if (curr < 0)
                {
                    demand_nodes.push_back(u);
                }
            }

            if (total <= 0)
            {
                return true;
            }

            IntVector arc_vector;
            if (m_sum_supply >= 0)
            {
                if (supply_nodes.size() == 1 && demand_nodes.size() == 1)
                {
                    BoolVector reached(m_graph.NodeSize(), false);
                    Node s = supply_nodes[0], t = demand_nodes[0];
                    vector<Node> stack;
                    reached[t.ID()] = true;
                    stack.push_back(t);
                    while (!stack.empty())
                    {
                        Node u, v = stack.back();
                        stack.pop_back();
                        if (v == s)
                        {
                            break;
                        }

                        for (InArcIt a(m_graph, v); a.ID() != INVALID_TAG; ++a)
                        {
                            if (reached[(u = m_graph.source(a), u.ID())])
                            {
                                continue;
                            }

                            int j = m_arc_id[a.ID()];
                            if (mvec_cap[j] >= total)
                            {
                                arc_vector.push_back(j);
                                reached[u.ID()] = true;
                                stack.push_back(u);
                            }
                        }
                    }
                }
                else
                {
                    for (int i = 0; i != int(demand_nodes.size()); ++i)
                    {
                        Node v = demand_nodes[i];
                        int c, min_cost = std::numeric_limits<int>::max();
                        Arc min_arc;
                        for (InArcIt a(m_graph, v); a.ID() != INVALID_TAG; ++a)
                        {
                            c = mvec_cost[m_arc_id[a.ID()]];
                            if (c < min_cost)
                            {
                                min_cost = c;
                                min_arc = a;
                            }
                        }

                        if (min_cost != std::numeric_limits<int>::max())
                        {
                            arc_vector.push_back(m_arc_id[min_arc.ID()]);
                        }
                    }
                }
            }

            for (int i = 0; i != int(arc_vector.size()); ++i)
            {
                m_t_in_arc = arc_vector[i];
                if (m_spt_state[m_t_in_arc] * (mvec_cost[m_t_in_arc] + mvec_phi[mvec_source[m_t_in_arc]] -
                    mvec_phi[mvec_target[m_t_in_arc]]) >= 0)
                {
                    continue;
                }

                FindJoinNode();
                bool change = FindLeavingArc();
                if (delta >= MAX)
                {
                    return false;
                }

                UpdateFlow(change);
                if (change)
                {
                    UpdateSPTData();
                    UpdatePhi();
                }
            }
            return true;
        }

        NetworkSimplex& ResetParams()
        {
            for (int i = 0; i != m_node_num; ++i)
            {
                mvec_supply[i] = 0;
            }

            for (int i = 0; i != m_arc_num; ++i)
            {
                mvec_lower[i] = 0;
                mvec_upper[i] = INF;
                mvec_cost[i] = 1;
            }

            m_has_lower = false;
            return *this;
        }

        cdnStatus Reset()
        {
            m_node_num = m_graph.NodeSize();
            m_arc_num = m_graph.ArcSize();
            int all_node_num = m_node_num + 1;
            int max_arc_num = m_arc_num + 2 * m_node_num;

            mvec_source.resize(max_arc_num);
            mvec_target.resize(max_arc_num);

            mvec_lower.resize(m_arc_num);
            mvec_upper.resize(m_arc_num);
            mvec_cap.resize(max_arc_num);
            mvec_cost.resize(max_arc_num);
            mvec_supply.resize(all_node_num);
            mvec_flow.resize(max_arc_num);
            mvec_phi.resize(all_node_num);

            m_spt_parent.resize(all_node_num);
            m_spt_pred.resize(all_node_num);
            m_spt_pred_dir.resize(all_node_num);
            m_spt_thread.resize(all_node_num);
            m_spt_rev_thread.resize(all_node_num);
            m_spt_succ_num.resize(all_node_num);
            m_spt_last_succ.resize(all_node_num);
            m_spt_state.resize(max_arc_num);

            int i = 0;
            for (NodeIt n(m_graph); n.ID() != INVALID_TAG; ++n, ++i)
            {
                m_node_id[n.ID()] = i;
            }
            if (m_node_num > 1)
            {
                const int skip = std::max(m_arc_num / m_node_num, 3);
                int i = 0, j = 0;
                for (ArcIt a(m_graph); a.ID() != INVALID_TAG; ++a)
                {
                    m_arc_id[a.ID()] = i;
                    mvec_source[i] = m_node_id[m_graph.source(a).ID()];
                    mvec_target[i] = m_node_id[m_graph.target(a).ID()];
                    if ((i += skip) >= m_arc_num)
                    {
                        i = ++j;
                    }
                }
            }
            else
            {
                int i = 0;
                for (ArcIt a(m_graph); a.ID() != INVALID_TAG; ++a, ++i)
                {
                    m_arc_id[a.ID()] = i;
                    mvec_source[i] = m_node_id[m_graph.source(a).ID()];
                    mvec_target[i] = m_node_id[m_graph.target(a).ID()];
                }
            }

            ResetParams();

            return CDN_OK;
        }

    private:
        const Digraph& m_graph;

        int m_node_num;
        int m_arc_num;
        int m_all_arc_num;
        int m_search_arc_num;

        bool m_has_lower;
        int m_sum_supply;

        IntVector m_node_id;
        IntVector m_arc_id;
        IntVector mvec_source;
        IntVector mvec_target;

        IntVector mvec_lower;
        IntVector mvec_upper;
        IntVector mvec_cap;
        IntVector mvec_cost;
        IntVector mvec_supply;
        IntVector mvec_flow;
        IntVector mvec_phi;

        // 维护支撑树的数据
        IntVector m_spt_parent;
        IntVector m_spt_pred;
        IntVector m_spt_thread;
        IntVector m_spt_rev_thread;
        IntVector m_spt_succ_num;
        IntVector m_spt_last_succ;
        CharVector m_spt_pred_dir;
        CharVector m_spt_state;
        IntVector m_spt_dirty_revs;
        int m_spt_root;

        int m_p_block_size;
        int m_p_next_arc;

        // 辅助数据
        int m_t_in_arc;
        int m_t_join;
        int m_t_u_in;
        int m_t_v_in;
        int m_t_u_out;
        int m_t_v_out;
        int delta;

        const int MAX;
        const int INF;
    };

    struct Solution3 : public Solution
    {
        Solution3(Instance* ins)
            : Solution(ins)
            , m_lack_flow_node(INVALID_NODE)
            , mvec3_cur_sol(ins->nodes, false)
            , mvec3_node_ser_level(ins->nodes, -1)
            , mvec3_has_deleted(ins->nodes, false)
            , mvec3_has_added(ins->nodes, false)
            //, mvec3_search_tabulist(ins->nodes, 0)
            , mvec3_set_server(ins->nodes, false)
            , mvec3_set_server_fix(ins->nodes, false)
            , mvec3_lack_flow(ins->consumers, true)
            , mvec3_cons_cost(ins->nodes, 0)
            , mvec3_cons_flow(ins->nodes, 0)
        {
            // 初始最优解
            mvec_best_paths.clear();
            best_cost = 0;

            m_least_level = 0;
            for (int i = 0; i < ins->consumers; ++i)
            {
                IntVector vec_path;
                int cur_conn = ins->server_conn[i];
                int cur_req = ins->server_req[i];

                int k = 0;
                while (cur_req > ins->mvec_server_type[k].first)
                {
                    k++;
                }

                m_least_level = max(m_least_level, k);

                vec_path.push_back(cur_conn);
                vec_path.push_back(ins->connect_consumer[cur_conn]);
                vec_path.push_back(ins->connect_consumer_req[cur_conn]);
                vec_path.push_back(k);

                best_cost += ins->mvec_server_type[k].second;
                best_cost += ins->node_cost[cur_conn];

                mvec_best_paths.push_back(vec_path);
            }

            m_init_cost = best_cost;
            m_max_level = (int)(ins->mvec_server_type.size()-1);
            
            mvec3_servers.reserve(ins->consumers + 1);
            mvec3_ser_level.reserve(ins->consumers + 1);
            mvec3_vec_cost.reserve(ins->consumers + 1);
            m_time_b = ins->m_time_b;

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

        ~Solution3()
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

        cdnStatus AddOneServer3(int update_node, int flow_need, int* new_server_pos)
        {
            cdnStatus ret = CDN_OK;

            IntVector vec_parent(ins->nodes, 0);
            IntVector vec_pos;

            ret = FindLackFlowPath(update_node, flow_need, &vec_parent, &vec_pos);
            if (ret == CDN_OK)
            {

            }
            else if (ret == CDN_FIND_SERVER_FAILED)
            {

            }

            *new_server_pos = vec_pos[rand() % vec_pos.size()];
            if (mvec3_cur_sol[*new_server_pos])
            {
                OUTPUT_INFO(cout << "error happened, in AddOneServer3 " << *new_server_pos << "\n";)
            }

            mvec3_servers.push_back(*new_server_pos);
            mvec3_ser_level.push_back(m_max_level);
            mvec3_node_ser_level[*new_server_pos] = m_max_level;
            mvec3_cur_sol[*new_server_pos] = true;
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
                int cur_flow_need = mvec_con_req[i].links - mvec3_cons_flow[cur_nodes];  // 当前消费结点的带宽需求
                int cur_all_flow_need = mvec_con_req[i].links;

                bool can_not_find = false;

                if (!mvec3_cur_sol[cur_nodes] && cur_flow_need > 0)
                {
                    // 尽可能的满足流量,存在暂时不能满足而等待新增服务点来满足的情况
#ifdef OLD_UPDATE_FLOW3
                    IntVector vec_parent(ins->nodes, 0);
#endif
                    int flow_sum = 0;
                    int flow_lack = 0;
                    int flow_cost = mvec3_cons_cost[cur_nodes];
                    int flow_ = mvec3_cons_flow[cur_nodes];
                    while (true)
                    {
                        if (flow_sum == cur_flow_need)
                        {
                            mvec3_lack_flow[cur_cons] = false;
                            break;
                        }
#ifndef OLD_UPDATE_FLOW3

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
                            mvec3_cons_cost[cur_nodes] += flow_add_true * dist[find_ser];
                            mvec3_cons_flow[cur_nodes] += flow_add_true;
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

                            mvec3_cons_cost[cur_nodes] += flow_add_true * vec_flow_path[0].cost;
                            mvec3_cons_flow[cur_nodes] += flow_add_true;
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
                    if (mvec3_cur_sol[cur_nodes] && update_node == cur_nodes)
                    {
                        // 添加路径
                        IntVector vec_path;
                        vec_path.push_back(cur_nodes);
                        vec_path.push_back(-1);
                        vec_path.push_back(cur_cons);
                        vec_path.push_back(cur_all_flow_need);
                        mvec_cur_paths.push_back(vec_path);

                        mvec3_lack_flow[cur_cons] = false;
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
#ifdef OLD_UPDATE_FLOW3
                IntVector vec_parent(ins->nodes, 0);
#endif
                int flow_sum = 0;
                int flow_lack = 0;
                int flow_cost = 0;
                int flow_ = 0;
                vector<std::pair<int, int> > vec_pair_flow;

                cdnStatus st = CDN_OK;

                while (true)
                {
                    if (flow_sum == flow_needed)
                    {
                        ret = true;
                        break;
                    }

#ifndef OLD_UPDATE_FLOW3
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
                        if (vec_flow_path.size() > 1)
                        {
                            sort(vec_flow_path.begin(), vec_flow_path.end(), cmp_sl);
                        }

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
                        vec_pair_flow.push_back(make_pair(flow_add_truly, flow_add_truly*vec_flow_path[0].cost));
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
               
                if (!ret)
                {
                    RemoveFlow3(vec_paths);
                }
                else
                {
                    for (size_t i=0; i<vec_pair_flow.size(); ++i)
                    {
                        mvec3_cons_cost[cur_node] += vec_pair_flow[i].second;
                        mvec3_cons_flow[cur_node] += vec_pair_flow[i].first;
                    }
                }
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
                if (mvec3_cur_sol[cur])
                {
                    break;
                }

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

        bool bfs3(int** graph, int** rGraph, int s, int t, IntVector& parent)
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
                    if (visited[v] == false && rGraph[u][v] > 0 && graph[u][v] > 0)
                    {
                        q.push(v);
                        parent[v] = u;
                        visited[v] = true;
                    }
                }
            }

            return (visited[t] == true);
        }

        int fordFulkerson3(int** graph, int** rGraph, int s, int t)
        {
            int u, v;

#if 0
            {
                ofstream out_file;
                out_file.open("cur_flow_.txt");
                if (out_file.is_open())
                {
                    for (size_t i = 0; i < mvec3_servers_best.size(); ++i)
                    {
                        int k = 0;
                        while (rGraph[ins->nodes][mvec3_servers_best[i]] > ins->mvec_server_type[k].first)
                        {
                            k++;
                        }
                        out_file << mvec3_servers_best[i] << " " << k << "\n";
                    }

                    out_file << "\n";
                    out_file << best_cost << "\n";
                    out_file << "\n";

                    for (int i = 0; i < ins->nodes+2; ++i)
                    {
                        for (int j = 0; j < ins->nodes+2; ++j)
                        {
                            if (ins->inc_cost[i][j] > 0)
                            {
                                out_file << i << " " << j << " " << ins->inc_cost[i][j] << "\n";
                            }
                        }
                    }
                    out_file.close();
                }
        }
#endif

            IntVector vec_flow(ins->nodes, 0);
            for (size_t i = 0; i < mvec3_servers_best.size(); ++i)
            {
                int k = 0;
                while (rGraph[ins->nodes][mvec3_servers_best[i]] > ins->mvec_server_type[k].first)
                {
                    k++;
                }
                vec_flow[mvec3_servers_best[i]] = k;
            }

            IntVector parent(ins->nodes + 2, 0);
            int max_flow = 0;
            while (bfs3(graph, rGraph, s, t, parent))
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
                vec_path.push_back(vec_flow[vec_path[0]]);
                
                mvec_cur_paths.push_back(vec_path);
            }

#if 0
            {
                ofstream out_file;
                out_file.open("res_flow.txt");
                if (out_file.is_open())
                {
                    for (int i = 0; i < ins->nodes + 2; ++i)
                    {
                        for (int j = 0; j < ins->nodes + 2; ++j)
                        {
                            if (rGraph[i][j] > 0 && rGraph[i][j] == graph[i][j])
                            {
                                out_file << i << " " << j << " " << rGraph[i][j] << "\n";
                            }
                        }
                    }

                    out_file << "\n\n";

                    for (int i = 0; i < ins->nodes + 2; ++i)
                    {
                        for (int j = 0; j < ins->nodes + 2; ++j)
                        {
                            if (rGraph[i][j] > 0 && rGraph[i][j] < graph[i][j])
                            {
                                out_file << i << " " << j << " " << rGraph[i][j] << "\n";
                            }
                        }
                    }

                    out_file.close();
                }
            }
#endif
            return max_flow;
        }

        cdnStatus FindAllFlow_NS_MinCost()
        {
            cdnStatus ret = CDN_OK;

            do 
            {
                Digraph curG(ins->m_nsGraph);
                //IntVector vec_suply_(ins->m_supply);
                IntVector vec_cost_(ins->m_cost);
                IntVector vec_upper_(ins->m_upper);
                IntVector vec_lower_(ins->m_lower);

                // 连边
                ins->addNSExtra(curG, mvec3_servers, mvec3_ser_level, vec_cost_, vec_upper_, vec_lower_);

                NetworkSimplex ns(curG);

                ns.SetData(ins->m_supply, vec_lower_, vec_upper_, vec_cost_);
                nsStatus res = ns.Run();
                if (res != NS_OPTIMAL)
                {
                    //cout << "ERROR: flow not found\n";
                    ret = CDN_FIND_SERVER_FAILED;
                    for (size_t i = 0; i < ins->m_cons_edge.size(); ++i)
                    {
                        int e = ins->m_cons_edge[i];
                        int source = INVALID_TAG;
                        int flow = ns.GetEdgeFlow(e, &source);
                        if (flow < ins->m_cons_req[i])
                        {
                            m_lack_flow_node = source;
                            m_lack_flow_num = ins->m_cons_req[i] - flow;
                            break;
                        }
                    }
                    break;
                }
                else
                {
                    IntVector vec_node_level_(ins->nodes, -1);
                    IntVector vec_ser_flow(ins->nodes, 0);
                    for (size_t i = 0; i < ins->m_sour_edge.size(); ++i)
                    {
                        int e = ins->m_sour_edge[i];
                        int flow = ns.GetSourceFlow(e);

                        vec_ser_flow[ins->m_sour_ser[i]] = flow;

                        int k = 0;
                        while (flow > ins->mvec_server_type[k].first)
                        {
                            k++;
                        }
                        vec_node_level_[ins->m_sour_ser[i]] = k;
                    }

                    int cur_cost = 0;
                    for (int i = 0; i < ins->nodes; ++i)
                    {
                        if (mvec3_cur_sol[i])
                        {
                            cur_cost += ins->mvec_server_type[vec_node_level_[i]].second;
                            cur_cost += ins->node_cost[i];
                        }
                    }

                    if (cur_cost + ns.GetCost() < best_cost)
                    {
                        best_cost = cur_cost + ns.GetCost();
                        best_num_server = (int)mvec3_servers.size();

                        OUTPUT_INFO(cout << "Cost:" << best_cost << "\n";)

                        for (int i = 0; i < ins->nodes + 2; ++i)
                        {
                            for (int j = 0; j < ins->nodes + 2; ++j)
                            {
                                ins->inc_cost[i][j] = 0;
                            }
                        }

                        // 记录流量
                        ns.GetFlowToMatrix(ins->inc_cost);
                        for (int i = 0; i < ins->nodes; ++i)
                        {
                            if (vec_ser_flow[i] > 0)
                            {
                                ins->inc_cost[ins->nodes][i] = vec_ser_flow[i];
                            }
                        }

                        // 记录最优解
                        mvec3_servers_best.assign(mvec3_servers.begin(), mvec3_servers.end());
                        mvec3_level_best.assign(mvec3_ser_level.begin(), mvec3_ser_level.end());
                        mvec3_sol_best.assign(mvec3_cur_sol.begin(), mvec3_cur_sol.end());
                    }
                }
            } while (false);

            return ret;
        }

        cdnStatus FindAllFlow_MinCost()
        {
            cdnStatus ret = CDN_OK;

#ifdef USE_NETWORK_SIMPLEX
            ret = FindAllFlow_NS_MinCost();
#else
            // 连边
            ins->addExtra(mvec3_servers, mvec3_ser_level);

            do
            {
                int flow = 0;
                int cost = 0;
                while (shortest_mincost(ins->nodes, ins->nodes + 1, flow, cost, inq, d, a, pre));

                // is solution valid?
                // 只需判断到达消费节点的流量是否满足,链路带宽上限由算法保证
                for (int i = 0; i < ins->consumers; i++)
                {
                    int cur_conn = ins->server_conn[i];
                    int nsize = (int)ins->mvec_G[cur_conn].size();
                    for (int j = nsize - 1; j >= 0; --j)
                    {
                        Edge& eg = ins->mvec_edges[ins->mvec_G[cur_conn][j]];
                        if (eg.to == (ins->nodes + 1) && eg.flow > 0)
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

                IntVector vec_node_level_(ins->nodes, -1);
                IntVector& vec_ser_ = ins->mvec_G[ins->nodes];
                for (size_t i = 0; i < vec_ser_.size(); ++i)
                {
                    Edge& eg = ins->mvec_edges[vec_ser_[i]];
                    if (eg.flow > 0)
                    {
                        int k = 0;
                        while (eg.flow > ins->mvec_server_type[k].first)
                        {
                            k++;
                        }
                        vec_node_level_[eg.to] = k;
                    }
                }

                int cur_cost = 0;
                for (int i = 0; i < ins->nodes; ++i)
                {
                    if (mvec3_cur_sol[i])
                    {
                        cur_cost += ins->mvec_server_type[vec_node_level_[i]].second;
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

                    mvec3_servers_best.assign(mvec3_servers.begin(), mvec3_servers.end());
                    mvec3_level_best.assign(mvec3_ser_level.begin(), mvec3_ser_level.end());
                    mvec3_sol_best.assign(mvec3_cur_sol.begin(), mvec3_cur_sol.end());

                    /*size_t n_server_ = 0;
                    for (size_t i=0; i<mvec3_cur_sol.size(); ++i)
                    {
                    if (mvec3_cur_sol[i])
                    {
                    n_server_++;
                    }
                    }
                    if (n_server_ != mvec3_servers.size())
                    {
                    cout << "\nerror happened!\n\n" << endl;
                    }*/

                    //mvec3_G_best.assign(ins->mvec_G.begin(), ins->mvec_G.end());
                    //mvec3_edges_best.assign(ins->mvec_edges.begin(), ins->mvec_edges.end());
                }
            } while (false);
#endif

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

                if (mvec3_cur_sol[adj_node])
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
                int min_cost_node = -1;
                for (int j = 0; j < ins->linked_edges[cur_cons_node]; ++j)
                {
                    int adj_node = ins->bfs_node[cur_cons_node][j + 1];

                    if (ins->cost[cur_cons_node][adj_node] == min_cost)
                    {
                        // TODO:选流量带宽最大的（目前选择连接的边最多的）
                        if (ins->linked_edges[adj_node] > min_cost_edge && !mvec3_cur_sol[adj_node])
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

                if (min_cost_node == -1)
                {
                    min_cost_node = cur_cons_node;
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
                int min_cost_node = -1;
                //IntVector vec_cand_min_cost;
                for (int j = 0; j < ins->linked_edges[cur_cons_node]; ++j)
                {
                    int adj_node = ins->bfs_node[cur_cons_node][j + 1];

                    if (ins->cost[cur_cons_node][adj_node] == min_cost)
                    {
                        // TODO:选流量带宽最大的（目前选择连接的边最多的）
                        if (ins->linked_edges[adj_node] > min_cost_edge && !mvec3_cur_sol[adj_node])
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

                if (min_cost_node == -1)
                {
                    min_cost_node = cur_cons_node;
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
            if (mvec3_cur_sol[start])
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

            bool is_first = true;

            while (!q_node.empty())
            {
                int cur = q_node.front();
                q_node.pop();

                // 以消费节点为中心进行广度优先遍历,获取最近的服务节点
                if (mvec3_cur_sol[cur])
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

                    if (vec_path.size() > 5 && is_first)
                    {
                        return CDN_FIND_SERVER_FAILED;
                    }

                    is_first = false;
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

            unsigned int seed = (unsigned int)time(NULL);
            cout << "seed:" << seed << endl;
            srand(seed);

            cdnStatus ret = CDN_OK;

            // step1.放置服务器,找可行解
            // 贪心,每次只给当前结点找流量,找不全也没关系,最后统一检查某结点解超过建立服务器的情形
            int req_max = mvec_con_req[0].links;
            while (m_max_level >= 0)
            {
                if (ins->mvec_server_type[m_max_level].first < 2 * req_max)
                {
                    break;
                }
                m_max_level--;
            }

            int medium_index = (int)(ins->mvec_server_type.size() + 1) / 2;
            m_max_level = max(m_least_level, medium_index-1);

            {
                OUTPUT_INFO(cout << m_max_level << endl;)
            }

            //ins->server_cost = ins->mvec_server_type[m_max_level].second;
            ins->server_cost = ins->mvec_server_type.back().second;
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
                    mvec3_servers.push_back(add_server);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[add_server] = m_max_level;
                    mvec3_cur_sol[add_server] = true;
                    server_num++;

                    if (cur_nodes == add_server)
                    {
                        mvec3_set_server[cur_nodes] = true;
                    }

                    if (must_set_server)
                    {
                        mvec3_set_server_fix[cur_nodes] = true;
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

            // 补全上一步没找全流量的消费节点,实在找不到流量则新建服务器
            while (true)
            {
                int cur_invalid_cons_ = INVALID_NODE;
                int flow_needed_ = 0;
 
                Reinit3();
                ret = FindAllFlow_MinCost();
                if (ret == CDN_OK)
                {
                    OUTPUT_INFO(cout << "Valid solution!" << endl;)
                    break;
                }
                else if (ret == CDN_FIND_SERVER_FAILED)
                {
#ifdef USE_NETWORK_SIMPLEX
                    cur_invalid_cons_ = m_lack_flow_node;
                    flow_needed_ = m_lack_flow_num;
#else
                    IsSolutionValid4(&cur_invalid_cons_, &flow_needed_);
#endif
                    
                    int new_pos = INVALID_NODE;
                    ret = AddOneServer3(cur_invalid_cons_, flow_needed_, &new_pos);
                    if (ret == CDN_OK)
                    {
                        OUTPUT_INFO(cout << "add server " << new_pos << "\n";)
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {
                        OUTPUT_INFO(cout << "add server failed!\n";)
                    }
                }
            }

            //OutputServerNonmove("non_move.txt");

            // 执行到此则已有完整的可行解
            {
                PrintTime("after initialize");
                OUTPUT_INFO(cout << "server number: " << server_num << endl;)
            }

            // step2.局部搜索
            // 邻域动作:交换相邻的边,删除一个服务点,添加一个服务点
            int search_times = 0;
            int no_opt_times = 0;
            int best_level_ = 0;
            int cur_level_ = m_max_level;
            int new_cycle = 0;
            //IntVector vec_candidate_bc_;
            do 
            {
                int cur_best_ = best_cost;

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
                if (!mvec3_sol_best.empty())
                {
                    mvec3_servers.assign(mvec3_servers_best.begin(), mvec3_servers_best.end());
                    mvec3_ser_level.assign(mvec3_level_best.begin(), mvec3_level_best.end());
                    mvec3_cur_sol.assign(mvec3_sol_best.begin(), mvec3_sol_best.end());
                    server_num = best_num_server;
                }

                IntVector _vec_servers_bc(mvec3_servers.begin(), mvec3_servers.end());
                IntVector _vec_ser_level_bc(mvec3_ser_level.begin(), mvec3_ser_level.end());
                BoolVector _vec_cur_sol_bc(mvec3_cur_sol.begin(), mvec3_cur_sol.end());
                int cur_server_num = server_num;

                OUTPUT_INFO(cout << "\nadd server, " << m_max_level << "\n\n";)
                ret = AddOneServerAndFind();
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }

                mvec3_servers.assign(_vec_servers_bc.begin(), _vec_servers_bc.end());
                mvec3_ser_level.assign(_vec_ser_level_bc.begin(), _vec_ser_level_bc.end());
                mvec3_cur_sol.assign(_vec_cur_sol_bc.begin(), _vec_cur_sol_bc.end());
                server_num = cur_server_num;

                OUTPUT_INFO(cout << "\nremove server, " << m_max_level << "\n\n";)
                ret = RemoveOneServerAndFind();
                if (ret == CDN_TIME_OUT)
                {
                    break;
                }

                search_times++;

                if (best_cost < cur_best_)
                {
                    best_level_ = m_max_level;
                }

                if (search_times % 2 == 0)
                {
                    m_max_level++;
                    if (m_max_level >= int(ins->mvec_server_type.size()))
                    {
                        m_max_level = m_least_level + 1;
                        new_cycle++;
                    }
                }

                if (new_cycle > 2)
                {
                    m_max_level = best_level_;
                    m_big_scale = false;
                }

                //mvec3_search_tabulist.clear();
                //mvec3_search_tabulist.resize(ins->nodes, INT_MAX);
            } while (true);
            
            // 记录结果
            if (best_cost < ins->consumers*ins->server_cost)
            {
                for (int i = 0; i < ins->consumers; ++i)
                {
                    int cur_conn = ins->server_conn[i];
                    ins->inc_cost[cur_conn][ins->nodes + 1] = ins->server_req[i];
                }

                for (int i = 0; i < ins->nodes + 2; ++i)
                {
                    for (int j = 0; j<ins->nodes + 2; ++j)
                    {
                        ins->flow[i][j] = ins->inc_cost[i][j];
                    }
                }
                mvec_cur_paths.clear();
                fordFulkerson3(ins->inc_cost, ins->flow, ins->nodes, ins->nodes + 1);
                mvec_best_paths.clear();
                mvec_best_paths.insert(mvec_best_paths.begin(),
                    mvec_cur_paths.begin(), mvec_cur_paths.end());

                cout << "best cost:" << best_cost << "\n";
            }

            PrintTime("terminate");

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
                IntVector vec_ser_level_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec3_servers.begin(), mvec3_servers.end());
                vec_ser_level_.insert(vec_ser_level_.begin(), mvec3_ser_level.begin(), mvec3_ser_level.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec3_cur_sol.begin(), mvec3_cur_sol.end());

                int cur_server;
                int cur_cost_local = best_cost;
                int select_server = INVALID_NODE;

                vector<LinkE> vec_non_server_flow_;

                for (size_t i = 0; i < mvec_server_candates.size(); ++i)
                {
                    cur_server = mvec_server_candates[i];
                    if (!vec_cur_sol_[cur_server] && !mvec3_cur_sol[cur_server])
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
                    mvec3_servers.push_back(cur_add_);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[cur_add_] = m_max_level;
                    mvec3_cur_sol[cur_add_] = true;
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

                    mvec3_servers.pop_back();
                    mvec3_ser_level.pop_back();
                    mvec3_node_ser_level[cur_add_] = -1;
                    mvec3_cur_sol[cur_add_] = false;
                    server_num--;

                    if (m_big_scale && i>20)
                    {
                        break;
                    }
                }

                if (select_server != INVALID_NODE)
                {
                    mvec3_servers.push_back(select_server);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[select_server] = m_max_level;
                    mvec3_cur_sol[select_server] = true;
                    server_num++;

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
                IntVector vec_ser_level_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec3_servers.begin(), mvec3_servers.end());
                vec_ser_level_.insert(vec_ser_level_.begin(), mvec3_ser_level.begin(), mvec3_ser_level.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec3_cur_sol.begin(), mvec3_cur_sol.end());

                int cur_server;
                int cur_cost_local = best_cost;
                int select_server = INVALID_NODE;

                vector<LinkE> vec_server_flow;

                // 选择边最少的服务节点
                for (size_t i = 0; i < vec_servers_.size(); ++i)
                {
                    cur_server = vec_servers_[i];

                    if (mvec3_set_server_fix[cur_server])
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
                    IntVector::iterator it = mvec3_servers.begin();
                    IntVector::iterator it_level = mvec3_ser_level.begin();
                    while (it != mvec3_servers.end())
                    {
                        if (*it == cur_del_)
                        {
                            mvec3_servers.erase(it);
                            mvec3_ser_level.erase(it_level);
                            mvec3_node_ser_level[cur_del_] = -1;
                            mvec3_cur_sol[cur_del_] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                            ++it_level;
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

                    mvec3_servers.push_back(cur_del_);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[cur_del_] = m_max_level;
                    mvec3_cur_sol[cur_del_] = true;
                    server_num++;

                    if (m_big_scale && i>20)
                    {
                        break;
                    }
                }

                if (select_server != INVALID_NODE)
                {
                    // 删除当前服务节点
                    IntVector::iterator it = mvec3_servers.begin();
                    IntVector::iterator it_level = mvec3_ser_level.begin();
                    while (it != mvec3_servers.end())
                    {
                        if (*it == select_server)
                        {
                            mvec3_servers.erase(it);
                            mvec3_ser_level.erase(it_level);
                            mvec3_node_ser_level[select_server] = -1;
                            mvec3_cur_sol[select_server] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                            ++it_level;
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

                    OUTPUT_INFO(cout << "remove one server, " << mvec3_servers.size() << "\n";)
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

            int try_times = m_big_scale ? 10 : 20;

            do 
            {
                bool has_optimal = false;
                int optimal_add = best_cost;
                int optimal_del = best_cost;

                int select_add_server = INVALID_NODE;
                int select_del_server = INVALID_NODE;

                IntVector vec_servers_;
                IntVector vec_ser_level_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec3_servers.begin(), mvec3_servers.end());
                vec_ser_level_.insert(vec_ser_level_.begin(), mvec3_ser_level.begin(), mvec3_ser_level.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec3_cur_sol.begin(), mvec3_cur_sol.end());

                vector<LinkE> vec_non_server_flow_;
                for (size_t i = 0; i < mvec_server_candates.size(); ++i)
                {
                    int cur_server = mvec_server_candates[i];
                    if (!vec_cur_sol_[cur_server] && !mvec3_cur_sol[cur_server])
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
                    if (mvec3_has_added[cur_add_] && m_big_scale)
                    {
                        continue;
                    }

                    mvec3_servers.push_back(cur_add_);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[cur_add_] = m_max_level;
                    mvec3_cur_sol[cur_add_] = true;
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
                            mvec3_has_added[cur_add_] = true;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {
                        mvec3_has_added[cur_add_] = true;
                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    mvec3_servers.pop_back();
                    mvec3_ser_level.pop_back();
                    mvec3_node_ser_level[cur_add_] = -1;
                    mvec3_cur_sol[cur_add_] = false;
                    server_num--;

                    if (real_add_times_ > try_times)
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

                    if (mvec3_set_server_fix[cur_server])
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
                    if (mvec3_has_deleted[cur_del_] && m_big_scale)
                    {
                        continue;
                    }

                    IntVector::iterator it = mvec3_servers.begin();
                    IntVector::iterator it_level = mvec3_ser_level.begin();
                    while (it != mvec3_servers.end())
                    {
                        if (*it == cur_del_)
                        {
                            mvec3_servers.erase(it);
                            mvec3_ser_level.erase(it_level);
                            mvec3_node_ser_level[cur_del_] = -1;
                            mvec3_cur_sol[cur_del_] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                            ++it_level;
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
                            mvec3_has_deleted[cur_del_] = true;
                        }
                    }
                    else if (ret == CDN_FIND_SERVER_FAILED)
                    {
                        mvec3_has_deleted[cur_del_] = true;
                    }
                    else if (ret == CDN_TIME_OUT)
                    {
                        return ret;
                    }

                    mvec3_servers.push_back(cur_del_);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[cur_del_] = m_max_level;
                    mvec3_cur_sol[cur_del_] = true;
                    server_num++;

                    if (real_del_times_ > try_times)
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
                    mvec3_servers.push_back(select_add_server);
                    mvec3_ser_level.push_back(m_max_level);
                    mvec3_node_ser_level[select_add_server] = m_max_level;
                    mvec3_cur_sol[select_add_server] = true;
                    server_num++;
                    OUTPUT_INFO(cout << "add server " << select_add_server << "\n";)
                }
                else
                {
                    IntVector::iterator it = mvec3_servers.begin();
                    IntVector::iterator it_level = mvec3_ser_level.begin();
                    while (it != mvec3_servers.end())
                    {
                        if (*it == select_del_server)
                        {
                            mvec3_servers.erase(it);
                            mvec3_ser_level.erase(it_level);
                            mvec3_node_ser_level[select_del_server] = -1;
                            mvec3_cur_sol[select_del_server] = false;
                            server_num--;
                            break;
                        }
                        else
                        {
                            ++it;
                            ++it_level;
                        }
                    } // delete one server
                    OUTPUT_INFO(cout << "del server " << select_del_server << "\n";)
                }

                //ret = FindCurOptimal_Links();
                //if (ret == CDN_TIME_OUT)
                //{
                //    break;
                //}
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
                IntVector vec_ser_level_;
                BoolVector vec_cur_sol_;
                vec_servers_.insert(vec_servers_.begin(), mvec3_servers.begin(), mvec3_servers.end());
                vec_ser_level_.insert(vec_ser_level_.begin(), mvec3_ser_level.begin(), mvec3_ser_level.end());
                vec_cur_sol_.insert(vec_cur_sol_.begin(), mvec3_cur_sol.begin(), mvec3_cur_sol.end());

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

                    bool is_move = !mvec3_set_server[cur_server];

                    if (m_running_mode == CRM_REPEAT_MODE)
                    {
                        is_move = !mvec3_set_server_fix[cur_server];
                    }

                    is_move = true;
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
                            if (!vec_cur_sol_[cur_node])// && mvec3_search_tabulist[cur_node]>0)
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
                                    is_swap = (adj_has_no_ser && cur_node_out_flow >= cur_ser_out_flow && m_search_list[cur_server][cur_node] > 0)
                                        || m_running_mode == CRM_REPEAT_MODE;
                                }

                                if (is_swap)
                                {
                                    temp_s = mvec3_servers[i];
                                    mvec3_cur_sol[mvec3_servers[i]] = false;
                                    mvec3_node_ser_level[mvec3_servers[i]] = -1;

                                    mvec3_servers[i] = cur_node;
                                    mvec3_cur_sol[mvec3_servers[i]] = true;
                                    mvec3_node_ser_level[mvec3_servers[i]] = m_max_level;

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
                                        //mvec3_search_tabulist[cur_node] = 0;
                                    }

                                    mvec3_cur_sol[mvec3_servers[i]] = false;
                                    mvec3_node_ser_level[mvec3_servers[i]] = -1;
                                    mvec3_servers[i] = temp_s;
                                    mvec3_cur_sol[mvec3_servers[i]] = true;
                                    mvec3_node_ser_level[mvec3_servers[i]] = m_max_level;
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
                    for (size_t i = 0; i < mvec3_servers.size(); ++i)
                    {
                        if (mvec3_servers[i] == select_server)
                        {
                            mvec3_servers[i] = select_node;
                            break;
                        }
                    }
                    mvec3_node_ser_level[select_server] = -1;
                    mvec3_cur_sol[select_server] = false;
                    mvec3_node_ser_level[select_node] = m_max_level;
                    mvec3_cur_sol[select_node] = true;
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
                if (mvec3_cur_sol[cur_node_connect_s])
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

        cdnStatus IsSolutionValid4(int* cur_invalid_cons, int* flow_needed)
        {
            // 只需判断到达消费节点的流量是否满足,链路带宽上限由算法保证
            for (int i = 0; i < ins->consumers; i++)
            {
                int cur_conn = ins->server_conn[i];
                int nsize = (int)ins->mvec_G[cur_conn].size();
                for (int j = nsize - 1; j >= 0; --j)
                {
                    Edge& eg = ins->mvec_edges[ins->mvec_G[cur_conn][j]];
                    if (eg.to == (ins->nodes + 1) && eg.flow > 0)
                    {
                        if (eg.flow < ins->server_req[i])
                        {
                            *cur_invalid_cons = cur_conn;
                            *flow_needed = ins->server_req[i] - eg.flow;
                            return CDN_FIND_SERVER_FAILED;
                        }
                        else
                        {
                            break;
                        }
                    }
                }
            }

            return CDN_OK;
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

            mvec3_lack_flow.clear();
            mvec3_lack_flow.resize(ins->nodes, 0);

            mvec3_cons_flow.clear();
            mvec3_cons_flow.resize(ins->nodes, 0);

            mvec3_cons_cost.clear();
            mvec3_cons_cost.resize(ins->nodes, 0);

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
                    for (size_t i = 0; i < mvec3_cur_sol.size(); ++i)
                    {
                        if (mvec3_cur_sol[i])
                        {
                            out_file << i << " ";
                        }
                    }
                }
                else
                {
                    for (size_t i = 0; i < mvec3_servers.size(); ++i)
                    {
                        out_file << mvec3_servers[i] << " ";
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
                for (size_t i = 0; i < mvec3_set_server.size(); ++i)
                {
                    if (mvec3_set_server[i])
                    {
                        out_server << i << " ";
                    }
                }

                out_server << "\n\nmust non-move:\n";

                for (size_t i = 0; i < mvec3_set_server_fix.size(); ++i)
                {
                    if (mvec3_set_server_fix[i])
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

#ifndef OLD_UPDATE_FLOW3
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
                if (mvec3_cur_sol[start_])
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

        int m_lack_flow_node;
        int m_lack_flow_num;

        bool* inq;
        int* d;
        int* a;
        int* pre;

        int** flow_S;
        int** m_search_list;

        int m_init_cost;
        int m_least_level;
        int m_max_level;

        double m_time_end;
        clock_t m_time_b;
        clock_t m_time_cur;

        IntVector mvec3_servers;
        IntVector mvec3_ser_level;
        BoolVector mvec3_cur_sol;
        IntVector mvec3_node_ser_level;

        BoolVector mvec3_has_deleted;
        BoolVector mvec3_has_added;

        //IntVector mvec3_search_tabulist;

        BoolVector mvec3_set_server;
        BoolVector mvec3_set_server_fix;

        BoolVector mvec3_lack_flow;

        IntVector mvec3_cons_cost;  // 消费结点的开销
        IntVector mvec3_cons_flow;  // 消费结点获得的流

        vector<LinkE> mvec3_vec_cost;

        IntVector mvec3_servers_best;
        IntVector mvec3_level_best;
        BoolVector mvec3_sol_best;
        vector<IntVector> mvec3_G_best;
        vector<Edge> mvec3_edges_best;
    };

} // namespace cdn

#endif // CDN_SOLUTION3_H
