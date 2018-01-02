#include "deploy.h"
#include <stdio.h>
#include <math.h>
#include <iostream>
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <stack>
#include <time.h>
#include <vector>
using namespace std;

#define maxn 1000
#define maxm 200000
#define inf 2147483647
#define MAX_LINE_LENG 1000000
#define MAX_LINE_LENGG 55000

int queue[maxn], pre[maxn], flag[maxn];
int dist[maxn], maxFlow[maxn];
int cumn[maxn] = {-1};
int cumn_need[maxn] = {0};
int cumn_point[maxn] = {0};

int ser;
int total_need = 0;
int best = inf;

const int INITIAL_TEMP = 10000; 

vector<int> not_ser_node;
vector<int> ser_node;

vector<int> not_ser_node_cpy;
vector<int> ser_node_cpy;

clock_t start;

struct Edge {
    int v;
	int u;
	int next;
	int cost;
	int w;
    Edge() {}
    Edge(int u, int v, int next, int cost, int w): u(u), v(v), next(next), cost(cost), w(w) {}
} edge[maxm], edgecpy[maxm];
int head[maxn], tail;
int headcpy[maxn], tailcpy;

void init() {
    memset(head, -1, sizeof(head));
    memset(headcpy, -1, sizeof(headcpy));
    tail = 0;
    tailcpy = 0;
}

void add_edge(int u,int v,int cost,int w) {
    edge[tail] = Edge(u, v, head[u], cost, w);
    head[u] = tail++;
    edge[tail] = Edge(v, u, head[v], cost, w);
    head[v] = tail++;
}

void add_cum(int u,int v,int cost,int w) {
    edge[tail] = Edge(u, v, head[u], cost, w);
    head[u] = tail++;
    edge[tail] = Edge(v, u, head[v], -cost, 0);
    head[v] = tail++;
}

void add_ser(int u,int v,int cost,int w) {
    edgecpy[tailcpy] = Edge(u, v, headcpy[u], cost, w);
    headcpy[u] = tailcpy++;
    edgecpy[tailcpy] = Edge(v, u, headcpy[v], -cost, 0);
    headcpy[v] = tailcpy++;
}

int SPFA(int start, int end) {
	int i, u, v, front, rear;
    front = rear = 0;
    memset(flag, 0, sizeof(flag));
    memset(dist, 0x1f, sizeof(dist));
    memset(pre, -1, sizeof(pre));
    dist[start] = 0, dist[end] = inf ,flag[start]=1;
    maxFlow[start] = inf, queue[rear++] = start;
    while(front != rear){
        u = queue[front++];
        if(front >= maxn) front = 0;
        flag[u] = 0;
        for(i = headcpy[u]; i != -1; i = edgecpy[i].next) {
            v = edgecpy[i].v;
            if(edgecpy[i].w > 0 && dist[v] > dist[u] + edgecpy[i].cost) {
                dist[v] = dist[u] + edgecpy[i].cost;
                maxFlow[v] = min(edgecpy[i].w, maxFlow[u]);
                pre[v] = i;
                if( !flag[v]) {
                    queue[rear++] = v;
                    if(rear >= maxn) rear = 0;
                    flag[v] =1;
                }
            }
        }
    }
    return dist[end] != inf;
}

int MFMC(int start, int end, int* max, char * topo_file) {
    int min_cost = 0, v, total = 0;
    char output[MAX_LINE_LENGG], topo_temp[MAX_LINE_LENGG];
    memset(output, 0, sizeof(output));
    memset(topo_temp, 0, sizeof(topo_temp));
    stack<int> road;
    while( SPFA(start, end)) {
        v = end;
        int count = 1;
        while( pre[v] >= 0){
            edgecpy[pre[v]].w -= maxFlow[end];
			v = edgecpy[pre[v]].u;
        }
		
		int temp = end;
		road.push(maxFlow[end]);
		road.push(cumn[edgecpy[pre[end]].u]);
		while (edgecpy[pre[temp]].u != start) {
			road.push(edgecpy[pre[temp]].u - 1);
			temp = edgecpy[pre[temp]].u;
		}
		sprintf(output, "%d", road.top());
		strcat(topo_temp, output);
		road.pop();
		while ( !road.empty()) {
			sprintf(output, " %d", road.top());
			strcat(topo_temp, output);
			road.pop();
		}
		sprintf(output, "\n");
		strcat(topo_temp, output);
		total++;
		*max += maxFlow[end];
		min_cost += dist[end] * maxFlow[end];
    }
    sprintf(topo_file, "%d\n\n", total);
    strcat(topo_file, topo_temp);
    return min_cost;
}

void get_neighbor(){
	int choose = rand() % 3;
	if (((clock() - start) / CLOCKS_PER_SEC > 60) && ((clock() - start) / CLOCKS_PER_SEC < 80))  choose = 0;
	if ((clock() - start) / CLOCKS_PER_SEC > 82)  choose = 0;
	int index1 = rand() % (ser_node_cpy.size());
	int index2 = rand() % (not_ser_node_cpy.size());

	if ( choose == 0)   {
		int temp  = ser_node_cpy[index1];
		ser_node_cpy[index1] = not_ser_node_cpy[index2];
		not_ser_node_cpy[index2] = temp;
	} else if ( choose == 1)  {
		not_ser_node_cpy.push_back(ser_node_cpy[index1]);
		std::vector<int>::iterator it = ser_node_cpy.begin() + index1;
		ser_node_cpy.erase(it);
	} else {
		ser_node_cpy.push_back(not_ser_node_cpy[index2]);
		std::vector<int>::iterator it = not_ser_node_cpy.begin() + index2;
		not_ser_node_cpy.erase(it);
	}
}


int accept (int ans,int flow,double t){
	if(ans < best && flow >= total_need){
		return 1;
	}
	return 0;
}

char topo_file[MAX_LINE_LENG];
char topo_file_best[MAX_LINE_LENG];
void deploy_server(char * topo[MAX_EDGE_NUM], int line_num,char * filename)
{
	start = clock();

    int N, M, K, max = 0;

	sscanf( topo[0], "%d %d %d", &N, &M, &K);
	sscanf( topo[2], "%d", &ser);
	init();
	for (int i = 0; i < M; i++) {
		int uu, vv, ww, cc;
		sscanf( topo[4 + i], "%d %d %d %d", &uu, &vv, &ww, &cc);
		add_edge( uu + 1, vv + 1, cc, ww);
	}
	for (int i = 0; i < K; i++) {
		int vv, uu, ww;
		sscanf( topo[5 + M + i], "%d %d %d", &vv, &uu, &ww);
		add_cum( uu + 1, N + 2, 0, ww);
		cumn[uu + 1] = vv;
		cumn_need[vv] = ww;
		total_need += ww; 
		cumn_point[vv] = uu + 1;
	}
	
	memset(edgecpy, 0, sizeof(Edge) * maxm);
	memcpy(edgecpy, edge, sizeof(Edge) * maxm);
	memset(headcpy, -1, sizeof(head));
	memcpy(headcpy, head, sizeof(head));
	tailcpy = tail;
	
	int ans = 0;
	for (int i = 0; i < K; i++) {
		add_ser( 0, cumn_point[i], 0, inf);
		ans += ser;
	}
	memset(topo_file, 0, sizeof(topo_file));		
	ans += MFMC(0, N + 2, &max, topo_file);

	int cost_now = inf, times = K - 1;
	int cumn_point_flag[maxn];
	memset(cumn_point_flag, 0, sizeof(cumn_point_flag));
	while (times >= 0) {
		memset(edgecpy, 0, sizeof(Edge) * maxm);
		memcpy(edgecpy, edge, sizeof(Edge) * maxm);
		memset(headcpy, -1, sizeof(head));
		memcpy(headcpy, head, sizeof(head));
		tailcpy = tail;
		
		cumn_point_flag[cumn_point[times]] = 1;
		ans = 0;
		for (int i = 0; i < K; i++) {
			if (cumn_point_flag[cumn_point[i]] == 0) {
				add_ser( 0, cumn_point[i], 0, inf);
				ans += ser;
			}
		}
		memset(topo_file, 0, sizeof(topo_file));
		max = 0;		
		ans += MFMC(0, N + 2, &max, topo_file);
		if (ans < cost_now && max >= total_need) {
			cost_now = ans;
		}
		else cumn_point_flag[cumn_point[times]] = 0;
		times--;
	}
	
	memset(topo_file_best, 0, sizeof(topo_file_best));
	memcpy(topo_file_best, topo_file, sizeof(topo_file_best));

	srand((int)time(0));
	
	best = ans;
	printf("%d\n", ans);
	double t =  INITIAL_TEMP;
	const double t_min = 0.001;
	const double SPEED = 0.9999;
	double r = SPEED;
	
	//memset(cumn_point_flag, 0, sizeof(cumn_point_flag));
	for (int i = 0; i < K; i++) {
		if (cumn_point_flag[cumn_point[i]] == 0) {
			ser_node.push_back(cumn_point[i]);
		}
		else {
			not_ser_node.push_back(cumn_point[i]);
		}
	}
	
	int time_now = (clock() - start) / CLOCKS_PER_SEC;
	
	while(t > t_min){
		if ((clock() - start) / CLOCKS_PER_SEC > 80)  break;
		ser_node_cpy.clear();
		//copy(ser_node.begin(), ser_node.end(), ser_node_cpy.begin());
		for (int i = 0; i < ser_node.size(); i++) {
			ser_node_cpy.push_back(ser_node[i]);
		}
		not_ser_node_cpy.clear();
		//copy(not_ser_node.begin(), not_ser_node.end(), not_ser_node_cpy.begin());
		for (int i = 0; i < not_ser_node.size(); i++) {
			not_ser_node_cpy.push_back(not_ser_node[i]);
		}

		get_neighbor();

		memset(edgecpy, 0, sizeof(Edge) * maxm);
		memcpy(edgecpy, edge, sizeof(Edge) * maxm);
		memset(headcpy, -1, sizeof(head));
		memcpy(headcpy, head, sizeof(head));
		tailcpy = tail;
		
		ans = 0;
		for (int i = 0; i < ser_node_cpy.size(); i++) {
			//printf("%d ", ser_node_cpy[i]);
			add_ser( 0, ser_node_cpy[i], 0, inf);
			ans += ser;
		}
		//printf("\n");
		memset(topo_file, 0, sizeof(topo_file));
		max = 0;		
		ans += MFMC(0, N + 2, &max, topo_file);

		if(accept( ans, max, t)){
			printf("%d\n", ans);
			best = ans;
						
			ser_node.clear();
			//copy(ser_node_cpy.begin(), ser_node_cpy.end(), ser_node.begin());
			for (int i = 0; i < ser_node_cpy.size(); i++) {
				ser_node.push_back(ser_node_cpy[i]);
			}
			
			not_ser_node.clear();
			//copy(not_ser_node_cpy.begin(), not_ser_node_cpy.end(), not_ser_node.begin());
			for (int i = 0; i < not_ser_node_cpy.size(); i++) {
				not_ser_node.push_back(not_ser_node_cpy[i]);
			}
		
			memset(topo_file_best, 0, sizeof(topo_file_best));
			memcpy(topo_file_best, topo_file, sizeof(topo_file_best));
		}
		t *= r; 
	}
		
	not_ser_node.clear();
	for (int i = 1; i <= N; i++) {
		if (find(ser_node.begin(), ser_node.end(), i) == ser_node.end()) {
			not_ser_node.push_back(i);
		}
	}
	
	t =  INITIAL_TEMP;
	cout << endl;
		
	while(t > t_min){
		if ((clock() - start) / CLOCKS_PER_SEC > 88)  break;
		ser_node_cpy.clear();
		//copy(ser_node.begin(), ser_node.end(), ser_node_cpy.begin());
		for (int i = 0; i < ser_node.size(); i++) {
			ser_node_cpy.push_back(ser_node[i]);
		}
		not_ser_node_cpy.clear();
		//copy(not_ser_node.begin(), not_ser_node.end(), not_ser_node_cpy.begin());
		for (int i = 0; i < not_ser_node.size(); i++) {
			not_ser_node_cpy.push_back(not_ser_node[i]);
		}

		get_neighbor();

		memset(edgecpy, 0, sizeof(Edge) * maxm);
		memcpy(edgecpy, edge, sizeof(Edge) * maxm);
		memset(headcpy, -1, sizeof(head));
		memcpy(headcpy, head, sizeof(head));
		tailcpy = tail;
		
		ans = 0;
		for (int i = 0; i < ser_node_cpy.size(); i++) {
			//printf("%d ", ser_node_cpy[i]);
			add_ser( 0, ser_node_cpy[i], 0, inf);
			ans += ser;
		}
		//printf("\n");
		memset(topo_file, 0, sizeof(topo_file));
		max = 0;		
		ans += MFMC(0, N + 2, &max, topo_file);

		if(accept( ans, max, t)){
			printf("%d\n", ans);
			best = ans;
						
			ser_node.clear();
			//copy(ser_node_cpy.begin(), ser_node_cpy.end(), ser_node.begin());
			for (int i = 0; i < ser_node_cpy.size(); i++) {
				ser_node.push_back(ser_node_cpy[i]);
			}
			not_ser_node.clear();
			//copy(not_ser_node_cpy.begin(), not_ser_node_cpy.end(), not_ser_node.begin());
			for (int i = 0; i < not_ser_node_cpy.size(); i++) {
				not_ser_node.push_back(not_ser_node_cpy[i]);
			}
						
			memset(topo_file_best, 0, sizeof(topo_file_best));
			memcpy(topo_file_best, topo_file, sizeof(topo_file_best));
		}
		t *= r; 
	}

	write_result(topo_file_best, filename);

}
