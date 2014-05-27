//////////////////////////////////Graph Libriry by YogyKwan
#include<cstdio>
#include<cmath>
#include<cstring>
#include<iostream>
#include<algorithm>
#include<queue>
using namespace std;
typedef double type;
const type inf=1e9;
const double eps=1e-8;
const int maxn=110;
const int maxm=1310;
int dblcmp(double x){
	if(x<-eps) return -1;
	if(x>eps) return 1;
	return 0;
}
int dblcmp(int x){
	if(x<0) return -1;
	if(x>0) return 1;
	return 0;
}
struct MaxFlow{
    struct EDGE{
        int v,next;
        type c;
    }edge[maxm];
    int d[maxn],head[maxn];
	int src,des,tot;
	queue<int> q;
	void init(){
        memset(head,-1,sizeof(head));
        tot=0;
	}
	void add(int u,int v,type c){
		edge[tot].v=v,edge[tot].c=c,edge[tot].next=head[u];head[u]=tot++;
		edge[tot].v=u,edge[tot].c=0,edge[tot].next=head[v];head[v]=tot++;
	}
	bool bfs(){
		while(!q.empty()) q.pop();
		int u,v,i;
		type c;
		memset(d,-1,sizeof(d));
		d[src]=0;
		q.push(src);
		while(!q.empty()){
			u=q.front();
			q.pop();
			for(i=head[u];i!=-1;i=edge[i].next){
				v=edge[i].v;
				c=edge[i].c;
				if(dblcmp(c)>0 && d[v]==-1){
					d[v]=d[u]+1;
					q.push(v);
				}
			}
		}
		return (d[des]!=-1);
	}
	type dfs(int u,type mmin){
		if(u==des) return mmin;
		int i,v;
		type c,temp,ans=mmin;
		for(i=head[u];i!=-1 && dblcmp(mmin)>0;i=edge[i].next){
			v=edge[i].v;
			c=edge[i].c;
			if(dblcmp(c)>0 && d[v]==d[u]+1 && (temp=dfs(v,min(mmin,c)))){
				edge[i].c-=temp;
				edge[i^1].c+=temp;
				mmin-=temp;
			}
		}
		ans-=mmin;
		if(!dblcmp(ans)) d[u]=-1;
		return ans;
	}
	type dinic(){
		type ans=0;
		while(bfs()){
			ans+=dfs(src,inf);
		}
		return ans;
	}
};

struct MaxFlowMinCost{
	struct EDGE{
		int u,v,p,next;
		type c,w;
	}edge[maxm];
	int tot,src,des;
	int head[maxn],cnt[maxn],pre[maxn];
	type d[maxn];
	bool vis[maxn];
	queue<int> q;
	void init(){
        memset(head,-1,sizeof(head));
        tot=0;
	}
	void add(int u,int v,type c,type w){
		edge[tot].u=u,edge[tot].v=v,edge[tot].c=c,edge[tot].w=w,edge[tot].p=tot^1,edge[tot].next=head[u];head[u]=tot++;
		edge[tot].u=v,edge[tot].v=u,edge[tot].c=0,edge[tot].w=-w,edge[tot].p=tot^1,edge[tot].next=head[v];head[v]=tot++;
	}
	bool spfa(){
		while(!q.empty()) q.pop();
		fill(d,d+des+1,inf);
		memset(cnt,0,sizeof(cnt));
		memset(vis,0,sizeof(vis));
		d[src]=0;cnt[src]=1;vis[src]=1;
		pre[src]=-1;
		q.push(0);
		int u,v,i;
		type c,w;
		while(!q.empty()){
			u=q.front();
			q.pop();
			vis[u]=0;
			for(i=head[u];i!=-1;i=edge[i].next){
				v=edge[i].v;
				c=edge[i].c;
				w=edge[i].w;
				if(dblcmp(c)>0 && dblcmp(d[u]+w-d[v])<0){
					d[v]=d[u]+w;
					pre[v]=i;
					if(!vis[v]){
						if(++cnt[v]>des) return 0;
						vis[v]=1;
						q.push(v);
					}
				}
			}
		}
		return dblcmp(d[des]-inf);
	}
	type mfmc(){
		int i;
		type ans=0,m;
		while(spfa()){
			m=inf;
			for(i=pre[des];i!=-1;i=pre[edge[i].u]) m=min(m,edge[i].c);
			for(i=pre[des];i!=-1;i=pre[edge[i].u]){
				edge[i].c-=m;
				edge[i^1].c+=m;
			}
			ans+=m*d[des];
		}
		return ans;
	}
};

struct Matching{
    int x[maxm],y[maxm];
    deque<int> Q;
    bool mat[maxn][maxn],inque[maxn],inblossom[maxn];
    int match[maxn],pre[maxn],base[maxn];
    int findancestor(int u,int v){
        bool inpath[maxn]={false};
        while(1){
            u=base[u];
            inpath[u]=true;
            if(match[u]==-1)break;
            u=pre[match[u]];
        }
        while(1){
            v=base[v];
            if(inpath[v])return v;
            v=pre[match[v]];
        }
    }
    void reset(int u,int anc){
        while(u!=anc){
            int v=match[u];
            inblossom[base[u]]=1;
            inblossom[base[v]]=1;
            v=pre[v];
            if(base[v]!=anc)pre[v]=match[u];
            u=v;
        }
    }
    void contract(int u,int v,int n){
        int anc=findancestor(u,v);
        memset(inblossom,0,sizeof(inblossom));
        reset(u,anc);reset(v,anc);
        if(base[u]!=anc)pre[u]=v;
        if(base[v]!=anc)pre[v]=u;
        for(int i=1;i<=n;i++){
            if(inblossom[base[i]]){
                base[i]=anc;
                if(!inque[i]){
                    Q.push_back(i);
                    inque[i]=1;
                }
            }
        }
    }
    bool dfs(int S,int n){
        for(int i=0;i<=n;i++)pre[i]=-1,inque[i]=0,base[i]=i;
        Q.clear();Q.push_back(S);inque[S]=1;
        while(!Q.empty()){
            int u=Q.front();Q.pop_front();
            for(int v=1;v<=n;v++){
                if(mat[u][v]&&base[v]!=base[u]&&match[u]!=v){
                    if(v==S||(match[v]!=-1&&pre[match[v]]!=-1))contract(u,v,n);
                    else if(pre[v]==-1){
                        pre[v]=u;
                        if(match[v]!=-1)Q.push_back(match[v]),inque[match[v]]=1;
                        else{
                            u=v;
                            while(u!=-1){
                                v=pre[u];
                                int w=match[v];
                                match[u]=v;
                                match[v]=u;
                                u=w;
                            }
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }
    int solve(int n){
        memset(match,-1,sizeof(match));
        int ans=0;
        for(int i=1;i<=n;i++)
            if(match[i]==-1&&dfs(i,n))
                ans++;
        return ans;
    }
    int gao(int n,int m){
        memset(mat,0,sizeof(mat));
        for(int i=0;i<m;++i){
            mat[x[i]][y[i]]=mat[y[i]][x[i]]=1;
        }
        return solve(n);
    }
};
///////////////////////////////////////////////////////////

//////////////////////////////////Graph Libriry by YogyKwan
int main(){
}
