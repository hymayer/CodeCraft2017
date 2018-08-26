#ifndef CDN_SOLUTION_H
#define CDN_SOLUTION_H

#include <ctime>
#include <queue>
#include <vector>
#include <climits>
#include <cassert>

#include <sstream>
#include <fstream>
#include <iostream>

#include <algorithm>

using namespace std;

namespace cdn {

typedef vector<double> RealVector;
typedef vector<bool> BoolVector;
typedef vector<int> IntVector;
typedef vector<signed char> CharVector;
typedef queue<int> IntQueue;

#ifndef LIMIT_CPU_TIME
#define LIMIT_CPU_TIME 85
#endif

#ifndef FIXED_TABU_LEN
#define FIXED_TABU_LEN 50
#endif

#define SCALE_BOUND 250

#define INVALID_NODE -1
#define INVALID_TAG -1

//#define OUTPUT_STD_INFO
//#define OUTPUT_LOG_FILE

#ifdef OUTPUT_STD_INFO
#define OUTPUT_INFO(n) n
#else
#define OUTPUT_INFO(n)  
#endif

//#define PRIMARY_MATCH

#define USE_NETWORK_SIMPLEX

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
    CRM_REPEAT_MODE,
    CRM_FINAL_MODE
} cdnRunningMode;

typedef enum
{
    CST_RANDOM = 0,
    CST_SERVER_LINKS,
    CST_TABU,
} cdnSearchType;

enum
{
    CDC_LESSER = 0,
    CDC_EQUAL,
    CDC_GREATER
};

template<class TYPE>
string ToStr(TYPE i)
{
    stringstream s;
    s << i;
    return s.str();
}

class Digraph;

class Node
{
public:
    Node()
    {
    }

    explicit Node(int pid)
    {
        id = pid;
    }

    int ID() const
    {
        return id;
    }

    bool operator==(const Node& node) const
    {
        return id == node.id;
    }

    bool operator!=(const Node& node) const
    {
        return id != node.id;
    }

    bool operator<(const Node& node) const
    {
        return id < node.id;
    }

protected:
    
    int id;

    friend class Digraph;
};

class Arc
{
public:
    Arc()
    {
    }

    explicit Arc(int pid)
    {
        id = pid;
    }

    int ID() const
    {
        return id;
    }

    bool operator==(const Arc& arc) const
    {
        return id == arc.id;
    }

    bool operator!=(const Arc& arc) const
    {
        return id != arc.id;
    }

    bool operator<(const Arc& arc) const
    {
        return id < arc.id;
    }

protected:
    
    int id;

    friend class Digraph;
};

class Digraph
{
public:
    Digraph()
        : nodes()
        , first_node(-1)
        , first_free_node(-1)
        , arcs()
        , first_free_arc(-1)
    {
    }

    int NodeSize() const
    {
        return int(nodes.size());
    }

    int ArcSize() const
    {
        return int(arcs.size());
    }

    Node addNode()
    {
        int n;

        if (first_free_node == -1)
        {
            n = (int)nodes.size();
            nodes.push_back(NodeT());
        }
        else
        {
            n = first_free_node;
            first_free_node = nodes[n].next;
        }

        nodes[n].next = first_node;
        if (first_node != -1)
        {
            nodes[first_node].prev = n;
        }

        first_node = n;
        nodes[n].prev = -1;

        nodes[n].first_in = nodes[n].first_out = -1;

        return Node(n);
    }

    Arc addArc(Node u, Node v)
    {
        int n;

        if (first_free_arc == -1)
        {
            n = (int)arcs.size();
            arcs.push_back(ArcT());
        }
        else
        {
            n = first_free_arc;
            first_free_arc = arcs[n].next_in;
        }

        arcs[n].source = u.id;
        arcs[n].target = v.id;

        arcs[n].next_out = nodes[u.id].first_out;
        if (nodes[u.id].first_out != -1)
        {
            arcs[nodes[u.id].first_out].prev_out = n;
        }

        arcs[n].next_in = nodes[v.id].first_in;
        if (nodes[v.id].first_in != -1)
        {
            arcs[nodes[v.id].first_in].prev_in = n;
        }

        arcs[n].prev_in = arcs[n].prev_out = -1;

        nodes[u.id].first_out = nodes[v.id].first_in = n;

        return Arc(n);
    }

protected:
    struct NodeT
    {
        int first_in;
        int first_out;
        int prev;
        int next;
    };

    struct ArcT
    {
        int target;
        int source;
        int prev_in;
        int prev_out;
        int next_in;
        int next_out;
    };

public:

    Node source(Arc e) const
    {
        return Node(arcs[e.id].source);
    }

    Node target(Arc e) const
    {
        return Node(arcs[e.id].target);
    }

    void first(Node& node) const
    {
        node.id = first_node;
    }

    void next(Node& node) const
    {
        node.id = nodes[node.id].next;
    }

    void first(Arc& arc) const
    {
        int n;
        for (n = first_node;
        n != -1 && nodes[n].first_out == -1;
            n = nodes[n].next)
        {
        }
        arc.id = (n == -1) ? -1 : nodes[n].first_out;
    }

    void next(Arc& arc) const
    {
        if (arcs[arc.id].next_out != -1)
        {
            arc.id = arcs[arc.id].next_out;
        }
        else
        {
            int n;
            for (n = nodes[arcs[arc.id].source].next;
            n != -1 && nodes[n].first_out == -1;
                n = nodes[n].next)
            {
            }
            arc.id = (n == -1) ? -1 : nodes[n].first_out;
        }
    }

    void firstOut(Arc &e, const Node& v) const
    {
        e.id = nodes[v.id].first_out;
    }

    void nextOut(Arc &e) const
    {
        e.id = arcs[e.id].next_out;
    }

    void firstIn(Arc &e, const Node& v) const
    {
        e.id = nodes[v.id].first_in;
    }

    void nextIn(Arc &e) const
    {
        e.id = arcs[e.id].next_in;
    }

    static int id(Node v)
    {
        return v.id;
    }

    static int id(Arc e)
    {
        return e.id;
    }

protected:
    vector<NodeT> nodes;
    int first_node;
    int first_free_node;
    vector<ArcT> arcs;
    int first_free_arc;
};

class NodeIt : public Node
{
public:

    NodeIt()
    {}

    explicit NodeIt(const Digraph& digraph)
        : m_digraph(&digraph)
    {
        m_digraph->first(static_cast<Node&>(*this));
    }

    NodeIt(const Digraph& digraph, const Node& node)
        : Node(node)
        , m_digraph(&digraph)
    {}

    NodeIt& operator++()
    {
        m_digraph->next(*this);
        return *this;
    }

private:
    const Digraph* m_digraph;
};

class ArcIt : public Arc
{
public:

    ArcIt()
    { }

    explicit ArcIt(const Digraph& digraph)
        : m_digraph(&digraph)
    {
        m_digraph->first(static_cast<Arc&>(*this));
    }

    ArcIt(const Digraph& digraph, const Arc& arc)
        : Arc(arc)
        , m_digraph(&digraph)
    { }

    ArcIt& operator++()
    {
        m_digraph->next(*this);
        return *this;
    }

private:
    const Digraph* m_digraph;
};

class OutArcIt : public Arc
{
public:

    OutArcIt()
    { }

    OutArcIt(const Digraph& digraph, const Node& node)
        : m_digraph(&digraph)
    {
        m_digraph->firstOut(*this, node);
    }

    OutArcIt(const Digraph& digraph, const Arc& arc)
        : Arc(arc)
        , m_digraph(&digraph)
    {}

    OutArcIt& operator++()
    {
        m_digraph->nextOut(*this);
        return *this;
    }

private:
    const Digraph* m_digraph;
};

class InArcIt : public Arc
{
public:

    InArcIt()
    { }

    InArcIt(const Digraph& digraph, const Node& node)
        : m_digraph(&digraph)
    {
        m_digraph->firstIn(*this, node);
    }

    InArcIt(const Digraph& digraph, const Arc& arc)
        : Arc(arc)
        , m_digraph(&digraph)
    {}

    InArcIt& operator++()
    {
        m_digraph->nextIn(*this);
        return *this;
    }

private:
    const Digraph* m_digraph;
};

struct Edge 
{
    Edge(int f, int t, int cap, int flow, int cost)
        : from(f)
        , to(t)
        , cap(cap)
        , flow(flow)
        , cost(cost)
    {}

    int from, to, cap, flow, cost;                  //边的起点，终点，容量，流量，单位带宽租用费
};

struct Instance
{
    Instance(char* graph[])
        : nodes(0)
        , edges(0)
        , consumers(0)
        , server_cost(0)
        , capacity(NULL)
        , cost(NULL)
        , node_cost(NULL)
        , server_req(NULL)
        , server_conn(NULL)
        , all_flow_req(0)
        , connect_consumer(NULL)
        , connect_consumer_req(NULL)
        , linked_edges(NULL)
        , pn(NULL)
    {
        m_time_b = clock();

#ifdef PRIMARY_MATCH
        ParserPrimary(graph);
#else
        ParserFinal(graph);
#ifdef USE_NETWORK_SIMPLEX
        InitNS();
#endif
#endif
        
    }

    ~Instance()
    {
        FreeMemory();
    }

    void ParserPrimary(char* graph[])
    {
        string strLine;
        int nCurLine = 0;

        // line 1
        strLine = graph[nCurLine++];
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

        // empty line2
        strLine = graph[nCurLine++];

        // line3
        server_cost = atoi(graph[nCurLine++]);

        // empty line4
        strLine = graph[nCurLine++];

        // network
        int start, stop, band, cost_;
        size_t iPos2;
        for (int i = 0; i < edges; i++)
        {
            assert(i + 4 == nCurLine);
            strLine = graph[nCurLine++];

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

            //OUTPUT_INFO(cout << start << " " << stop << " " << band << " " << cost_ << endl;)
        }

        // empty line
        nCurLine++;

        // consumer network
        int consid, cons_c, req;
        for (int i = 0; i < consumers; ++i)
        {
            strLine = graph[i + nCurLine];
            iPos = strLine.find(' ');
            consid = atoi(strLine.substr(0, iPos).c_str()); // 消费节点id
            iPos1 = strLine.find(' ', iPos + 1);
            cons_c = atoi(strLine.substr(iPos + 1, iPos1).c_str()); // 和消费结点相连的网络结点id
            req = atoi(strLine.substr(iPos1 + 1).c_str()); // 消费结点带宽需求

            server_conn[consid] = cons_c;
            server_req[consid] = req;
            connect_consumer[cons_c] = consid;
            connect_consumer_req[cons_c] = req;

            all_flow_req += req;

            //OUTPUT_INFO(cout << consid << " " << cons_c << " " << req << endl;)
        }
    }

    void ParserFinal(char* graph[])
    {
        string strLine;
        int nCurLine = 0;

        // line 1
        strLine = graph[nCurLine++];
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

        // empty line2
        strLine = graph[nCurLine++];

        int ser_seq, ser_cap, ser_cost;
        while ((strLine = graph[nCurLine++])!="\n")
        {
            iPos = strLine.find(' ');
            if (iPos == string::npos)
            {
                break;
            }

            ser_seq = atoi(strLine.substr(0, iPos).c_str());
            ser_seq = ser_seq;
            iPos1 = strLine.find(' ', iPos + 1);
            ser_cap = atoi(strLine.substr(iPos + 1, iPos1).c_str());
            ser_cost = atoi(strLine.substr(iPos1 + 1).c_str());
            mvec_server_type.push_back(make_pair(ser_cap, ser_cost));
        }

        int node_seq_, node_cost_;
        for (int i = 0; i < nodes; i++)
        {
            strLine = graph[nCurLine++];
            iPos = strLine.find(' ');
            node_seq_ = atoi(strLine.substr(0, iPos).c_str());
            node_cost_ = atoi(strLine.substr(iPos + 1).c_str());
            node_cost[node_seq_] = node_cost_;
        }

        // empty line
        strLine = graph[nCurLine++];

        // network
        int start, stop, band, cost_;
        size_t iPos2;
        for (int i = 0; i < edges; i++)
        {
            strLine = graph[nCurLine++];

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

            //OUTPUT_INFO(cout << start << " " << stop << " " << band << " " << cost_ << endl;)
        }

        // empty line
        nCurLine++;

        // consumer network
        int consid, cons_c, req;
        for (int i = 0; i < consumers; ++i)
        {
            strLine = graph[i + nCurLine];
            iPos = strLine.find(' ');
            consid = atoi(strLine.substr(0, iPos).c_str()); // 消费节点id
            iPos1 = strLine.find(' ', iPos + 1);
            cons_c = atoi(strLine.substr(iPos + 1, iPos1).c_str()); // 和消费结点相连的网络结点id
            req = atoi(strLine.substr(iPos1 + 1).c_str()); // 消费结点带宽需求

            server_conn[consid] = cons_c;
            server_req[consid] = req;
            connect_consumer[cons_c] = consid;
            connect_consumer_req[cons_c] = req;

            all_flow_req += req;

            //OUTPUT_INFO(cout << consid << " " << cons_c << " " << req << endl;)
        }
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

    void addExtra(const IntVector& vec_servers, const IntVector& vec_ser_level)
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
#ifdef PRIMARY_MATCH
            mvec_edges.push_back(Edge(s, vec_servers[i], INT_MAX, 0, 0));
#else 
            mvec_edges.push_back(Edge(s, vec_servers[i], mvec_server_type[vec_ser_level[i]].first, 0, 0));
#endif
            
            mvec_edges.push_back(Edge(vec_servers[i], s, 0, 0, 0));
            nsize = (int)mvec_edges.size();
            mvec_G[s].push_back(nsize - 2);
            mvec_G[vec_servers[i]].push_back(nsize - 1);
        }
    }

    void InitNS()
    {
        m_supply.resize(nodes + 3);
        m_lower.resize(edges * 2 + consumers * 2);
        m_upper.resize(edges * 2 + consumers * 2);
        m_cost.resize(edges * 2 + consumers * 2);

        pn = new Node[nodes + 2];
        int all_req = 0;
        for (int i = 0; i < nodes; ++i)
        {
            pn[i] = m_nsGraph.addNode();
            if (connect_consumer[i] > -1)
            {
                m_supply[pn[i].ID()] = -connect_consumer_req[i];
                all_req += connect_consumer_req[i];
            }
            else
            {
                m_supply[pn[i].ID()] = 0;
            }
        }

        pn[nodes] = m_nsGraph.addNode();
        m_supply[pn[nodes].ID()] = all_req;
        //supply[pn[ins->nodes+1]] = -all_req;

        pn[nodes + 1] = m_nsGraph.addNode();
        m_supply[pn[nodes + 1].ID()] = 0;

        for (int i = 0; i < nodes; ++i)
        {
            for (int j = 0; j < nodes; ++j)
            {
                if (capacity[i][j] > 0)
                {
                    Arc a = m_nsGraph.addArc(pn[i], pn[j]);
                    m_lower[a.ID()] = 0;
                    m_upper[a.ID()] = capacity[i][j];
                    m_cost[a.ID()] = cost[i][j];
                }
            }
        }

        // sink
        for (int i = 0; i < consumers; ++i)
        {
            int cur_conn = server_conn[i];
            int cur_req = server_req[i];

            Arc a = m_nsGraph.addArc(pn[cur_conn], pn[nodes + 1]);
            m_lower[a.ID()] = 0; //cur_req; 
            m_upper[a.ID()] = INT_MAX;
            m_cost[a.ID()] = 0;
            m_cons_edge.push_back(a.ID());
            m_cons_req.push_back(cur_req);
        }

        Arc a = m_nsGraph.addArc(pn[nodes], pn[nodes + 1]);
        m_lower[a.ID()] = 0;
        m_upper[a.ID()] = INT_MAX;
        m_cost[a.ID()] = 0;
    }

    void addNSExtra(Digraph& nsG,const IntVector& vec_servers, const IntVector& vec_ser_level, 
        IntVector& vec_co, IntVector& vec_up, IntVector& vec_lo)
    {
        m_sour_edge.clear();
        m_sour_ser.clear();
        for (size_t i = 0; i < vec_servers.size(); ++i)
        {
            Arc a = nsG.addArc(pn[nodes], pn[vec_servers[i]]);
            vec_lo[a.ID()] = 0;
            vec_up[a.ID()] = mvec_server_type[vec_ser_level[i]].first; // INT_MAX;
            vec_co[a.ID()] = 0;
            m_sour_edge.push_back(a.ID());
            m_sour_ser.push_back(vec_servers[i]);
        }
    }

    int nodes;
    int edges;
    int consumers;
    int server_cost;

    clock_t m_time_b;

    int ** capacity;
    int ** flow;
    int ** bfs_node;  // 网络节点广度遍历时由近到远的节点集合
    int ** cost;
    int ** inc_cost;

    int * node_cost;

    // 数组长度为消费节点的个数
    int * server_req;            // 消费结点带宽需求,数组下标为消费结点ID
    int * server_conn;           // 消费结点连接网络结点的映射,数组下标为消费结点ID

    int all_flow_req;

    // 数组长度为网络节点的个数
    int * connect_consumer;      // 和消费节点相连的网络节点
    int * connect_consumer_req;  // 和消费节点相连的网络节点的带宽需求
    int * linked_edges;          // 每个网络结点相连的边数

    vector<pair<int, int> > mvec_server_type;

    vector<IntVector> mvec_G;
    vector<IntVector> mvec_G_backup;
    vector<Edge> mvec_edges;
    vector<Edge> mvec_edges_backup;

    Node* pn;
    Digraph m_nsGraph;
    IntVector m_supply;
    IntVector m_lower;
    IntVector m_upper;
    IntVector m_cost;
    IntVector m_cons_edge;
    IntVector m_cons_req;
    IntVector m_sour_edge;
    IntVector m_sour_ser;
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

struct FlowPath
{
    FlowPath(int con, int ser, int layer, int cost,
        int flow, IntVector& path)
        : consumer(con)
        , server(ser)
        , bfs_layer(layer)
        , cost(cost)
        , flow(flow)
        , paths(path)
    {
        // nothing to do
    }

    /*FlowPath(const FlowPath& obj)
        : consumer(obj.consumer)
        , server(obj.server)
        , bfs_layer(obj.bfs_layer)
        , cost(obj.cost)
        , flow(obj.flow)
        , paths(obj.paths)
    {
        // nothing to do
    }*/

    int consumer;
    int server;
    int bfs_layer;
    int cost;
    int flow;

    IntVector paths;
};

struct Solution
{
    Solution(Instance* ins)
        : ins(ins)
        , server_num(0)
        , m_big_scale(ins->nodes>2*SCALE_BOUND)
        , cur_cost(INT_MAX)
        , best_cost(INT_MAX)
        , best_num_server(0)
        , last_best_iter(0)
        , m_running_mode(CRM_INST_MODE)
        , m_search_type(CST_SERVER_LINKS)
        , mvec_cur_sol(ins->nodes, false)
        , mvec_best_sol(ins->nodes, false)
        , mvec_server_nodes(ins->nodes, 0)
        , mvec_add_tabu_lis(ins->nodes, 0)
        , mvec_del_tabu_lis(ins->nodes, 0)
    {
        // 预处理,结果数据在搜索过程中直接使用,提高效率
        for (int i = 0; i < ins->nodes; ++i)
        {
            mvec_links.push_back(LinkE(i, ins->linked_edges[i]));

            if (ins->linked_edges[i] > 2 || (ins->linked_edges[i] == 2 && ins->connect_consumer[i] > -1))
            {
                mvec_server_candates.push_back(i);
            }
            else if (ins->linked_edges[i] == 2)
            {
                mvec_2_links_no_cons.push_back(i);
            }
        }
        sort(mvec_links.begin(), mvec_links.end(), cmp);

        for (int i = 0; i < ins->consumers; ++i)
        {
            mvec_con_req.push_back(LinkE(i, ins->server_req[i]));
        }
        sort(mvec_con_req.begin(), mvec_con_req.end(), cmp);

        BfsTransEveryNode();
    }

    ~Solution()
    {
        // nothing to do
    }

    cdnStatus BFS(int start)
    {
        int index = 0;
        int edges = ins->linked_edges[start];

        BoolVector vec_visited(ins->nodes, false);
        IntQueue q_node;
        q_node.push(start); // start是虚拟节点
        ins->bfs_node[start][index++] = start;
        vec_visited[start] = true;

        bool is_enough = false;

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

                    if (index > edges)
                    {
                        is_enough = true;
                        break;
                    }
                }
            }

            if (is_enough)
            {
                break;
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

    cdnStatus BfsTraversal(int start, int* stop, IntVector* pvec_parent,
        vector<FlowPath>* pvec_flow_path)
    {
        if (mvec_cur_sol[start])
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
            if (mvec_cur_sol[cur])
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


    cdnStatus UpdateFlow(int consumer, int flow_needed, int& flow_sum,
        int* flow_lack, vector<FlowPath>& vec_flow_path)
    {
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

        mvec_server_nodes[flow_path.server]++;

        flow_sum += cur_add_flow;

        IntVector vec_res_path(vec_path);
        vec_res_path.push_back(-1);
        vec_res_path.push_back(ins->connect_consumer[consumer]);
        vec_res_path.push_back(cur_add_flow);

        mvec_cur_paths.push_back(vec_res_path);

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

        return CDN_OK;
    }

    cdnStatus AddFlow(int cur_invalid_cons, int flow_needed)
    {
        IntVector vec_parent(ins->nodes, 0);

        int stop;
        int flow_sum = 0;

        cdnStatus ret = CDN_OK;

        vector<FlowPath> vec_flow_path;

        while (true)
        {
            if (flow_sum == flow_needed)
            {
                return CDN_OK;
            }

            vec_flow_path.clear();

            // 每次找出到各服务器点的最优
            ret = BfsTraversal(cur_invalid_cons, &stop, &vec_parent, &vec_flow_path);
            if (ret == CDN_OK)
            {
                sort(vec_flow_path.begin(), vec_flow_path.end(), cmp_sl);

                int flow_lack = 0;
                ret = UpdateFlow(cur_invalid_cons, flow_needed, flow_sum, &flow_lack, vec_flow_path);
                if (ret == CDN_LACK_FLOW)
                {
                    // 遍历补全剩余的流量
                }
                else if (ret == CDN_OK)
                {
                    break;
                }
            }
            else if (ret == CDN_FIND_SERVER)
            {
                break;
            }
            else if (ret == CDN_FIND_SERVER_FAILED)
            {
                // 列出当前流量不能满足的节点

                break;
            }
        }

        return ret;
    }

    cdnStatus FindValidSol(int* failed_cons, int iter)
    {
        cdnStatus ret = CDN_OK;
        int cur_consumer;

        for (size_t i = 0; i < mvec_con_req.size(); ++i)
        {
            cur_consumer = ins->server_conn[mvec_con_req[i].index];
            ret = AddFlow(cur_consumer, mvec_con_req[i].links);
            if (ret == CDN_FIND_SERVER_FAILED)
            {
                *failed_cons = cur_consumer;
                return ret;
            }
        }

        RecordCost(iter);
        return CDN_OK;

        // 检查搜索结果
        /*int cur_invalid_cons = INVALID_NODE;
        int flow_needed = 0;
        if (IsSolutionValid(&cur_invalid_cons, &flow_needed))
        {
            RecordCost(iter);
            return CDN_OK;
        }
        else
        {
            assert(false);
            OUTPUT_INFO(cout << "node " << ToStr(cur_invalid_cons)
                << " need " << ToStr(flow_needed) << "\n";)

            return CDN_FIND_SERVER_FAILED;
        }*/
    }

    cdnStatus LocalSearch()
    {
        if (!ins)
        {
            return CDN_ERROR;
        }

        const bool random_init_sol = false; // 初始解生成策略
        const int max_iter = 1000000;

        int iter_search_time = 0;

        int server_num_r = min((int)mvec_server_candates.size(), ins->consumers);
        int server_num_l = 1; //min(ins->consumers / 3, 3);

        // 构造初始解
        server_num = (server_num_l + server_num_r) / 2;
        for (int i = 0; i < server_num; ++i)
        {
            mvec_servers.push_back(mvec_links[i].index);
            mvec_cur_sol[mvec_links[i].index] = true;
        }

        int iter = 1;
        int succeed_times = 0;
        int fail_times = 0;
        cdnStatus ret = CDN_OK;

        clock_t time_start = clock();
        clock_t time_end;
        double time_interval;

        int failed_cons = INVALID_NODE;

        bool need_delete_server = false;

        srand((unsigned int)time(NULL));

        //m_search_type = CST_RANDOM; // 效果更好

        #ifdef OUTPUT_LOG_FILE
        ofstream output_file;
        output_file.open("info_log.txt");
        if (!output_file.is_open())
        {
            return CDN_ERROR;
        }
        output_file << "server number: " << server_num << "\n";
        #endif

        do
        {
            if (iter % 10000 == 0 || iter - last_best_iter > 500 || need_delete_server)
            {
                if (fail_times-succeed_times >= 300)
                {
                    server_num_l = server_num + 1;
                }
                server_num--;
                need_delete_server = false;
                if (server_num < server_num_l)
                {
                    iter_search_time++;
                    if (iter_search_time > 2)
                    {
                        break;
                    }

                    server_num = best_num_server!=INT_MAX ? best_num_server : server_num_r;
                }

                mvec_servers.clear();

                mvec_cur_sol.clear();
                mvec_cur_sol.resize(ins->nodes, false);

                if (random_init_sol)
                {
                    IntVector vec_choose_server;
                    GetRandoms(ins->nodes, server_num, vec_choose_server);
                    for (size_t i = 0; i < vec_choose_server.size(); ++i)
                    {
                        mvec_servers.push_back(vec_choose_server[i]);
                        mvec_cur_sol[vec_choose_server[i]] = true;
                    }
                }
                else
                {
                    for (int i = 0; i < server_num; ++i)
                    {
                        mvec_servers.push_back(mvec_links[i].index);
                        mvec_cur_sol[mvec_links[i].index] = true;
                    }
                }

                mvec_del_tabu_lis.clear();
                mvec_del_tabu_lis.resize(ins->nodes, 0);

                mvec_add_tabu_lis.clear();
                mvec_add_tabu_lis.resize(ins->nodes, 0);

                last_best_iter = iter;

                if (m_running_mode > CRM_INIT_MODE)
                {
                    Reinit();
                }

                OUTPUT_INFO(cout << "server number: " << server_num << "\n";)
                #ifdef OUTPUT_LOG_FILE
                output_file << "server number: " << server_num << "\n";
                #endif
            }

            m_running_mode = CRM_RUNNING_MODE;
            ret = FindValidSol(&failed_cons, iter);
            if (ret == CDN_OK)
            {
                succeed_times++;
                fail_times = 0;

                if (succeed_times > 20)
                {
                    need_delete_server = true;
                    succeed_times = 0;
                    continue;
                }

                // move
                int out_ser = 0;
                int in_ser = 0;
                ret = FindMovePairServer(&out_ser, &in_ser, iter);

                assert(in_ser != INVALID_NODE);

                ret = MoveServerPosition(out_ser, in_ser, iter);

                #ifdef OUTPUT_LOG_FILE
                output_file << "S " << out_ser << " --> " << in_ser << "\n";
                #endif
            }
            else if (ret == CDN_FIND_SERVER_FAILED)
            {
                assert(failed_cons != INVALID_NODE);

                fail_times++;
                succeed_times = 0;

                // move
                IntVector add_sets(1, failed_cons);
                FindServerFromNode(failed_cons, &add_sets, iter);
                assert(add_sets.size() > 1);

                int old_pos = add_sets.back();
                int rand_index = rand() % (add_sets.size() - 1);
                int new_pos = add_sets[rand_index];
                MoveServerPosition(old_pos, new_pos, iter);

                #ifdef OUTPUT_LOG_FILE
                output_file << "F " << failed_cons << ", " << old_pos << " --> " << new_pos << "\n";
                #endif
            }

            iter++;

            time_end = clock();

            time_interval = (double)(time_end - time_start) / CLOCKS_PER_SEC;
            if (time_interval > LIMIT_CPU_TIME)
            {
                break;
            }

            if (m_running_mode > CRM_INIT_MODE)
            {
                Reinit();
            }
        } while (iter < max_iter);

        #ifdef OUTPUT_LOG_FILE
        if (output_file.is_open())
        {
            output_file.close();
        }
        #endif

        OUTPUT_INFO(cout << "iter times:" << iter << endl;)
        OUTPUT_INFO(cout << "time: " << time_interval << endl;)
        OUTPUT_INFO(cout << "best server number:" << best_num_server << endl;)
        OUTPUT_INFO(cout << "best cost:" << best_cost << endl;)

        return CDN_OK;
    }

    cdnStatus FindAddServer(int* add_server, int iter)
    {
        cdnStatus ret = CDN_OK;

        int temp = INT_MAX;
        bool selected = false;

        int cur_dd = INVALID_NODE;
        int tabu_node = INVALID_NODE;

        for (size_t i = 0; i < mvec_links.size(); ++i)
        {
            cur_dd = mvec_links[i].index;
            if (!mvec_cur_sol[cur_dd])
            {
                if (mvec_del_tabu_lis[cur_dd] < iter)
                {
                    selected = true;
                    *add_server = cur_dd;
                    break;
                }
                else
                {
                    // 选择最早被禁忌的
                    if (mvec_del_tabu_lis[cur_dd] - iter < temp)
                    {
                        temp = mvec_del_tabu_lis[cur_dd] - iter;
                        tabu_node = cur_dd;
                    }
                }
            }
        }

        if (!selected)
        {
            *add_server = tabu_node;
        }

        return ret;
    }

    cdnStatus AddOneServer(int new_server, int iter)
    {
        cdnStatus ret = CDN_OK;

        // 调用者确保传入的节点未被选作服务器
        mvec_cur_sol[new_server] = true;
        mvec_servers.push_back(new_server);

        server_num++;

        // 设置禁忌
        mvec_add_tabu_lis[new_server] = iter + FIXED_TABU_LEN + rand() % 10;

        ret = Reinit();

        return ret;
    }

    cdnStatus FindServerFromNode(int node, IntVector* nodes_set, int iter)
    {
        // 以当前找寻服务器失败的节点为起点,选中待移除的服务器节点为终点,在其中随机选择一个结点为新的服务点
        cdnStatus ret = CDN_OK;

        int cur_node;
        int temp = INT_MAX;
        int tabu_node = INVALID_NODE; // 如果全部被禁忌则选最早被禁忌的

        // 收集可以作为新服务器放置位置的点
        for (int i = 1; i < ins->nodes; ++i)
        {
            cur_node = ins->bfs_node[node][i];

            if (mvec_cur_sol[cur_node])
            {
                break;
            }

            if (mvec_del_tabu_lis[cur_node] < iter)
            {
                nodes_set->push_back(cur_node);
            }
            else
            {
                // tabu
                if (mvec_del_tabu_lis[cur_node] - iter < temp)
                {
                    temp = mvec_del_tabu_lis[cur_node] - iter;
                    tabu_node = cur_node;
                }
            }
        }

        // 选择需要移除的服务器结点
        switch (m_search_type)
        {
        case CST_SERVER_LINKS:
        {
            bool selected = false;
            temp = INT_MAX;
            int tabu_temp = INT_MAX;
            int non_tabu_node = INVALID_NODE;
            for (size_t i = 0; i < mvec_servers.size(); ++i)
            {
                cur_node = mvec_servers[i];
                if (mvec_add_tabu_lis[cur_node] < iter)
                {
                    if (mvec_server_nodes[cur_node] < temp)
                    {
                        temp = mvec_server_nodes[cur_node];
                        non_tabu_node = cur_node;
                        selected = true;
                    }
                }
                else
                {
                    if (mvec_server_nodes[cur_node] < tabu_temp)
                    {
                        tabu_temp = mvec_server_nodes[cur_node];
                        tabu_node = cur_node;
                    }
                }
            }

            if (selected)
            {
                nodes_set->push_back(non_tabu_node);
            }
            else
            {
                nodes_set->push_back(tabu_node);
            }
            break;
        }
        case CST_RANDOM:
        case CST_TABU:
        {
            nodes_set->push_back(mvec_servers[rand() % mvec_servers.size()]);
            break;
        }
        default:
            break;
        }

        return ret;
    }

    cdnStatus FindMovePairServer(int* out_ser, int* in_ser, int iter)
    {
        cdnStatus ret = CDN_OK;

        switch (m_search_type)
        {
        case CST_SERVER_LINKS:
        {
            int temp = INT_MAX;
            int cur_ser;

            bool selected = false;

            int tabu_temp = INT_MAX;
            int tabu_node = INVALID_NODE;

            // 找到移除的服务器节点
            for (size_t i = 0; i < mvec_servers.size(); ++i)
            {
                cur_ser = mvec_servers[i];
                if (mvec_add_tabu_lis[cur_ser] < iter)
                {
                    if (mvec_server_nodes[cur_ser] < temp)
                    {
                        temp = mvec_server_nodes[cur_ser];
                        *out_ser = cur_ser;
                        selected = true;
                    }
                }
                else
                {
                    if (mvec_server_nodes[cur_ser] < tabu_temp)
                    {
                        tabu_temp = mvec_server_nodes[cur_ser];
                        tabu_node = cur_ser;
                    }
                }
            }

            if (!selected)
            {
                *out_ser = tabu_node;
                ret = CDN_SELECT_NONE;
            }

            // 找到即将成为服务器节点的节点
            int cur_node;
            temp = -1;
            tabu_temp = -1;
            selected = false;
            tabu_node = INVALID_NODE;
            for (int i = 1; i < ins->nodes; ++i) // 只在当前节点最近的邻域内选择
            {
                cur_node = ins->bfs_node[*out_ser][i];
                if (!mvec_cur_sol[cur_node]) // 只能是用户节点
                {
                    if (mvec_del_tabu_lis[cur_node] < iter)
                    {
                        if (ins->linked_edges[cur_node] > temp)
                        {
                            temp = ins->linked_edges[cur_node];
                            *in_ser = cur_node;
                            selected = true;
                            if (rand() % ins->nodes < i)
                            {
                                break;
                            }
                        }
                    }
                    else
                    {
                        if (ins->linked_edges[cur_node] > tabu_temp)
                        {
                            tabu_temp = ins->linked_edges[cur_node];
                            tabu_node = cur_node;
                        }
                    }
                }
            }

            if (!selected)
            {
                *in_ser = tabu_node;
                ret = CDN_SELECT_NONE;
            }

            break;
        }
        case CST_RANDOM:
        {
            int rand_index = rand() % mvec_servers.size();
            *out_ser = mvec_servers[rand_index];

            IntVector vec_server_candi_;
            vec_server_candi_.reserve(ins->nodes);

            for (size_t i=0; i<mvec_server_candates.size(); ++i)
            {
                if (!mvec_cur_sol[mvec_server_candates[i]])
                {
                    vec_server_candi_.push_back(mvec_server_candates[i]);
                }
            }

            *in_ser = vec_server_candi_[rand() % vec_server_candi_.size()];
            break;
        }   
        case CST_TABU: // 有问题
        {
            int temp = INT_MAX;
            int cur_ser = INVALID_NODE;
            for (size_t i = 0; i < mvec_servers.size(); ++i)
            {
                if (mvec_add_tabu_lis[mvec_servers[i]] < temp)
                {
                    temp = mvec_add_tabu_lis[mvec_servers[i]];
                    cur_ser = mvec_servers[i];
                }
            }
            *out_ser = cur_ser;

            temp = INT_MAX;
            for (size_t i = 0; i < mvec_server_candates.size(); ++i)
            {
                if (!mvec_cur_sol[mvec_server_candates[i]] && mvec_server_candates[i] != *out_ser)
                {
                    if (mvec_del_tabu_lis[mvec_server_candates[i]] < temp)
                    {
                        temp = mvec_del_tabu_lis[mvec_server_candates[i]];
                        cur_ser = mvec_server_candates[i];
                    }
                }
            }
            *in_ser = cur_ser;
            break;
        }
        default:
            break;
        }

        return ret;
    }

    cdnStatus MoveServerPosition(int old_position, int new_position, int iter)
    {
        cdnStatus ret = CDN_OK;

        mvec_cur_sol[new_position] = true;
        mvec_cur_sol[old_position] = false;

        for (size_t i = 0; i < mvec_servers.size(); ++i)
        {
            if (mvec_servers[i] == old_position)
            {
                mvec_servers[i] = new_position;
                break;
            }
        }

        // 设置禁忌
        mvec_add_tabu_lis[new_position] = iter + FIXED_TABU_LEN + rand() % 10;
        mvec_del_tabu_lis[old_position] = iter + FIXED_TABU_LEN + rand() % 10;

        ret = Reinit();

        return ret;
    }

    cdnStatus FindDeleteServer(int* add_server, int iter)
    {
        cdnStatus ret = CDN_OK;

        int temp = INT_MAX;
        int cur_ser;

        bool selected = false;

        int tabu_temp = INT_MAX;
        int tabu_node = INVALID_NODE;

        for (size_t i = 0; i < mvec_servers.size(); ++i)
        {
            cur_ser = mvec_servers[i];
            if (mvec_add_tabu_lis[cur_ser] < iter)
            {
                if (mvec_server_nodes[cur_ser] < temp)
                {
                    temp = mvec_server_nodes[cur_ser];
                    *add_server = cur_ser;
                    selected = true;
                }
            }
            else
            {
                if (mvec_server_nodes[cur_ser] < tabu_temp)
                {
                    tabu_temp = mvec_server_nodes[cur_ser];
                    tabu_node = cur_ser;
                }
            }
        }

        if (!selected)
        {
            *add_server = tabu_node;
            ret = CDN_SELECT_NONE;
        }

        return ret;
    }

    cdnStatus DeleteServer(int del_server, int iter)
    {
        cdnStatus ret = CDN_OK;

        int index = INVALID_NODE;

        for (size_t i = 0; i < mvec_servers.size(); ++i)
        {
            if (mvec_servers[i] == del_server)
            {
                index++;
                mvec_servers[i] = del_server;
                break;
            }
        }

        assert(index != INVALID_NODE);

        mvec_cur_sol[del_server] = false;
        IntVector::iterator it = mvec_servers.begin();
        mvec_servers.erase(it + index);

        server_num--;

        ret = Reinit();

        // 设置禁忌
        mvec_del_tabu_lis[del_server] = iter + FIXED_TABU_LEN + rand() % 10;

        return ret;
    }

    // discard
    cdnStatus DeleteMinEdgeServer(int* p_del_server, int iter)
    {
        cdnStatus ret = CDN_OK;
        int tmp = INT_MAX;
        int cur_server;

        // TODO:判断是否在禁忌列表之内

        size_t index = INT_MAX;
        for (size_t i = 0; i < mvec_servers.size(); ++i)
        {
            cur_server = mvec_servers[i];
            if (ins->linked_edges[cur_server] < tmp
                && mvec_add_tabu_lis[cur_server] < iter)
            {
                index = i;
                tmp = ins->linked_edges[cur_server];
            }
        }

        assert(index != INT_MAX);
        if (index == INT_MAX)
        {
            // 都在禁忌之中
            return CDN_SELECT_NONE;
        }

        *p_del_server = mvec_servers[index];

        mvec_cur_sol[mvec_servers[index]] = false;
        IntVector::iterator it = mvec_servers.begin();
        mvec_servers.erase(it + index);

        server_num--;

        // 设置禁忌
        mvec_del_tabu_lis[*p_del_server] = iter + FIXED_TABU_LEN + rand() % 10;

        ret = Reinit();

        return ret;
    }

    cdnStatus Reinit()
    {
        mvec_cur_paths.clear();

        mvec_server_nodes.clear();
        mvec_server_nodes.resize(ins->nodes, 0);

        m_running_mode = CRM_INIT_MODE;

        cur_cost = INT_MAX;

        for (int i = 0; i < ins->nodes; ++i)
        {
            for (int j = 0; j < ins->nodes; ++j)
            {
                if (ins->flow[i][j] > 0)
                {
                    ins->flow[i][j] = 0;
                }
            }
        }

        return CDN_OK;
    }

    void RecordCost(int iter)
    {
        cur_cost = Cost();
        if (cur_cost < best_cost)
        {
            best_cost = cur_cost;
            best_num_server = server_num;

            // temp code
            {
                OUTPUT_INFO(cout << "best cost:" << best_cost << endl;)
                //OUTPUT_INFO(cout << "no change time:" << iter-last_best_iter << endl;)
                //OutputSolution("optimal_result.txt");
            }
            // temp code end

            last_best_iter = iter;

            mvec_best_sol.clear();
            mvec_best_sol.insert(mvec_best_sol.begin(),
                mvec_cur_sol.begin(), mvec_cur_sol.end());

            mvec_best_paths.clear();
            mvec_best_paths.insert(mvec_best_paths.begin(),
                mvec_cur_paths.begin(), mvec_cur_paths.end());


        }
    }

    bool ValidSolution()
    {
        bool ret = true;

        for (int i=0; i<ins->nodes; ++i)
        {
            for (int j=0; j<ins->nodes; ++j)
            {
                if (ins->flow[i][j] > ins->capacity[i][j])
                {
                    cout << "edge[" << i << "," << j << "] error flow, exceed\n";
                    ret = false;
                }
            }
        }

        IntVector vec_cons_flow(ins->consumers, 0);

        for (size_t i = 0; i < mvec_best_paths.size(); ++i)
        {
            IntVector& vec_path = mvec_best_paths[i];

            size_t nsize = vec_path.size();

            int cons_ = vec_path[nsize - 2];
            int flow_ = vec_path[nsize - 1];

            vec_cons_flow[cons_] += flow_;
        }

        for (size_t i = 0; i < vec_cons_flow.size(); ++i)
        {
            if (vec_cons_flow[i] < ins->server_req[i])
            {
                cout << "consumer-" << i << " lack flow " << 
                    (ins->server_req[i]- vec_cons_flow[i]) << "\n";
                ret = false;
            }
        }

        return ret;
    }

    void OutputSolution(const string& file_name = "result.txt")
    {
        ofstream out;
        out.open(file_name.c_str());

        if (out.is_open())
        {
            if (best_cost == INT_MAX)
            {
                // 没有找到合法解
                out << "NA\n";
            }
            else
            {
                out << ToStr(mvec_best_paths.size()) << "\n";
                out << "\n";

                for (size_t i = 0; i < mvec_best_paths.size(); ++i)
                {
                    IntVector& vec_path = mvec_best_paths[i];
                    for (size_t j = 0; j < vec_path.size(); ++j)
                    {
                        if (vec_path[j] >= 0)
                        {
                            out << ToStr(vec_path[j]) << " ";
                        }
                    }

                    out << "\n";
                }
            }

            out.close();
        }
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
            result += ToStr(mvec_best_paths.size());
            result += "\n\n";
            for (size_t i = 0; i < mvec_best_paths.size(); ++i)
            {
                IntVector& vec_path = mvec_best_paths[i];
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

                if (i < mvec_best_paths.size() - 1)
                {
                    result += "\n";
                }
            }
        }
    }

    int Cost()
    {
        int cost = server_num * ins->server_cost;

        for (int i = 0; i < ins->nodes; ++i)
        {
            for (int j = 0; j < ins->nodes; ++j)
            {
                if (ins->flow[i][j] > 0)
                {
                    cost += ins->flow[i][j] * ins->cost[i][j];
                }
            }
        }

        return cost;
    }

    void GetConsumerLackFlow(int consumer, int* lack_flow)
    {
        if (mvec_cur_sol[consumer])
        {
            *lack_flow = 0;
            return;
        }

        int inflow = 0;
        int outflow = 0;

        for (int j = 0; j < ins->nodes; ++j)
        {
            inflow += ins->flow[j][consumer];
            outflow += ins->flow[consumer][j];
        }

        *lack_flow = ins->connect_consumer_req[consumer] - (inflow - outflow);

        assert(*lack_flow >= 0);
    }

    // 判断当前解是否可行
    bool IsSolutionValid(int* cur_invalid_cons, int* flow_needed)
    {
        int cur_node_connect_s = 0;
        for (int i = 0; i < ins->consumers; ++i)
        {
            cur_node_connect_s = ins->server_conn[i];
            if (mvec_cur_sol[cur_node_connect_s])
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

    void GetPaths(vector<Edge>& vecEdges, vector<IntVector>& vec_G, IntVector& vec_servers)
    {
        if (vecEdges.empty() || vec_G.empty())
        {
            return;
        }

        //vector<string> vec_list;
        mvec_cur_paths.clear();

        for (size_t i = 0; i < vec_servers.size(); i++)
        {
            vector<int> q;
            int u = vec_servers[i];
            //string route = "";
            IntVector vec_path;
            int a = INT_MAX;
            size_t temp = 0;
            size_t j = 0;
            while (j < ins->mvec_G[u].size())
            {
                Edge& e = ins->mvec_edges[ins->mvec_G[u][j]];
                if (e.flow > 0)
                {
                    if (u == vec_servers[i])
                    {
                        temp = j;
                    }
                    //route += ToStr(e.from) + " ";
                    vec_path.push_back(e.from);
                    q.push_back(ins->mvec_G[u][j]);
                    a = min(a, e.flow);
                    j = 0;
                    u = e.to;
                    if (e.to == ins->nodes + 1)
                    {
                        for (int p = 0; p < ins->consumers; p++)
                        {
                            if (ins->server_conn[p] == e.from)
                            {
                                //route += ToStr(p) + " " + ToStr(a);
                                vec_path.push_back(-1);
                                vec_path.push_back(p);
                                vec_path.push_back(a);
                                break;
                            }
                        }

                        //vec_list.push_back(route);
                        mvec_cur_paths.push_back(vec_path);
                        //cout << route << endl;

                        for (size_t k = 0; k < q.size(); k++)
                        {
                            ins->mvec_edges[q[k]].flow -= a;
                        }

                        q.clear();
                        j = temp;
                        u = vec_servers[i];
                        //route = "";
                        vec_path.clear();
                        a = INT_MAX;
                    }
                }
                else
                {
                    j++;
                }
            }
        }
    }

    bool GetRandoms(int n, int m, IntVector& vec_servers)
    {
        srand((unsigned int)time(NULL));

        for (int i = 0; i < n; ++i)
        {
            if (rand() % (n - i) < m)
            {
                vec_servers.push_back(i);
                m--;
            }
        }

        return true;
    }

    static bool cmp(const LinkE& a, const LinkE& b)
    {
        return a.links > b.links;
    }

    static bool cmp_less(const LinkE& a, const LinkE& b)
    {
        return a.links < b.links;
    }

    static bool cmp_sl(const FlowPath& a, const FlowPath& b)
    {
        if (a.cost == b.cost)
        {
            if (a.bfs_layer == b.bfs_layer)
            {
                return a.flow > b.flow;
            }
            else
            {
                return a.bfs_layer < b.bfs_layer;
            }
        }
        else
        {
            return a.cost < b.cost;
        }
    }

    static bool cmp_p(const pair<int, int>& a, const pair<int, int>& b)
    {
        if (a.second == b.second)
        {
            return a.first > b.first;
        }
        else
        {
            return a.second < b.second;
        }
    }

    Instance* ins;
    int server_num;

    bool m_big_scale;

    int cur_cost;
    int best_cost;

    int best_num_server;

    int last_best_iter;

    cdnRunningMode m_running_mode;
    cdnSearchType m_search_type;

    BoolVector mvec_cur_sol;
    BoolVector mvec_best_sol;

    IntVector mvec_servers; // 服务器节点集合

    IntVector mvec_server_nodes; // 记录服务器节点提供的流量路数

    IntVector mvec_server_candates; // 可被选为服务器的节点(不包括只有一条边的节点和未连接消费节点的两条边的节点)
    IntVector mvec_2_links_no_cons;

    vector<LinkE> mvec_links; // 网络节点\该节点相连边数
    vector<LinkE> mvec_con_req; // 消费节点\该节点流量需求

    IntVector mvec_add_tabu_lis;
    IntVector mvec_del_tabu_lis;

    vector<IntVector> mvec_cur_paths;
    vector<IntVector> mvec_best_paths;
};

} // namespace cdn

#endif // CDN_SOLUTION_H
