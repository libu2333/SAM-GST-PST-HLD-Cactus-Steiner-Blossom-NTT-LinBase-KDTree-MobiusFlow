#include<bits/stdc++.h>
using namespace std;
const int MAXV=100005,MAXE=200005,INF=0x3f3f3f3f;
// suffix automaton
struct SAM {
	static const int N=200005;
	int nxt[N][26],link[N],len[N],cnt,las;
	void init() {
		cnt=1;
		las=1;
		memset(nxt,0,sizeof(nxt));
		link[1]=0;
		len[1]=0;
	} void extend(int c) {
		int cur=++cnt,p=las;
		len[cur]=len[p]+1;
		while(p&&!nxt[p][c])nxt[p][c]=cur,p=link[p];
		if(!p)link[cur]=1;
		else {
			int q=nxt[p][c];
			if(len[q]==len[p]+1)link[cur]=q;
			else {
				int clone=++cnt;
				len[clone]=len[p]+1;
				memcpy(nxt[clone],nxt[q],sizeof(nxt[q]));
				link[clone]=link[q];
				while(p&&nxt[p][c]==q)nxt[p][c]=clone,p=link[p];
				link[q]=link[cur]=clone;
			}
		}
		las=cur;
	}
} sam;
// generalized suffix tree (tree from SAM)
vector<int>gstTree[SAM::N];
void buildGST() {
	for(int i=2; i<=sam.cnt; i++)gstTree[sam.link[i]].push_back(i);
}
// persistent segment tree
int pst_l[MAXV*40],pst_r[MAXV*40],pst_sum[MAXV*40],pst_root[MAXV],pst_tot;
int pst_update(int prev,int l,int r,int pos) {
	int cur=++pst_tot;
	pst_l[cur]=pst_l[prev];
	pst_r[cur]=pst_r[prev];
	pst_sum[cur]=pst_sum[prev]+1;
	int m=(l+r)>>1;
	if(l<r) {
		if(pos<=m) pst_l[cur]=pst_update(pst_l[prev],l,m,pos);
		else pst_r[cur]=pst_update(pst_r[prev],m+1,r,pos);
	}
	return cur;
}
int pst_merge(int x,int y) {
	if(!x||!y) return x|y;
	int z=++pst_tot;
	pst_sum[z]=pst_sum[x]+pst_sum[y];
	pst_l[z]=pst_merge(pst_l[x],pst_l[y]);
	pst_r[z]=pst_merge(pst_r[x],pst_r[y]);
	return z;
}
// cactus steiner tree placeholder
struct CactusSteiner {
	vector<int>adj[MAXV];
	void addEdge(int u,int v) {
		adj[u].push_back(v);
		adj[v].push_back(u);
	} vector<int>buildSteiner(vector<int>&pts) {
		return pts;
	}
};
// blossom algorithm for max weight matching
struct Blossom {
	int n;
	vector<vector<int>>g;
	vector<int>match,base,p,inq;
	vector<vector<int>>ed;
	int lca(int x,int y) {
		vector<int>vis(n+1);
		while(1) {
			x=base[x];
			vis[x]=1;
			if(!match[x])break;
			x= p[match[x]];
		}
		while(1) {
			y=base[y];
			if(vis[y])return y;
			y=p[match[y]];
		}
	}
	int findpath(int x,int y) {
		int L=lca(x,y);
		auto blossom=[&](int x) {
			while(base[x]!=L) {
				int y=match[x];
				inq[base[x]]=inq[base[y]]=1;
				p[x]=y;
				y=match[y];
				base[x]=base[y]=L;
				x=p[y];
			}
		};
		blossom(x);
		blossom(y);
		for(int i=1; i<=n; i++)if(inq[base[i]]&&!p[i]) {
				p[i]=y;
				q.push(i);
			}
		return 0;
	}
	queue<int>q;
	int augment(int s) {
		fill(inq.begin(),inq.end(),0);
		fill(p.begin(),p.end(),0);
		iota(base.begin(),base.end(),0);
		while(!q.empty())q.pop();
		q.push(s);
		inq[s]=1;
		while(!q.empty()) {
			int u=q.front();
			q.pop();
			for(int v:g[u]) {
				if(base[u]==base[v]||match[u]==v)continue;
				if(v==s||match[v]&&p[match[v]]) findpath(u,v);
				else if(!p[v]) {
					p[v]=u;
					if(!match[v]) {
						u=v;
						while(u) {
							int pv=p[u],nv=match[pv];
							match[u]=pv;
							match[pv]=u;
							u=nv;
						}
						return 1;
					}
					else q.push(match[v]),inq[match[v]]=1;
				}
			}
		}
		return 0;
	}
	int maxWeight(vector<vector<int>>&mat) {
		n=mat.size()-1;
		g.assign(n+1, {});
		match.assign(n+1,0);
		base.assign(n+1,0);
		p.assign(n+1,0);
		inq.assign(n+1,0);
		for(int i=1; i<=n; i++)for(int j=i+1; j<=n; j++)if(mat[i][j])g[i].push_back(j),g[j].push_back(i);
		int res=0;
		for(int i=1; i<=n; i++)if(!match[i])res+=augment(i);
		return res;
	}
}
blossom;
// NTT
struct NTT {
	int mod,root;
	void init(int m,int r) {
		mod=m;
		root=r;
	} int modpow(long long a,int e) {
		long long r=1;
		while(e) {
			if(e&1)r=r*a%mod;
			a=a*a%mod;
			e>>=1;
		}
		return r;
	} vector<int>mul(vector<int>a,vector<int>b) {
		int n=1,tot=a.size()+b.size()-1;
		while(n<tot)n<<=1;
		a.resize(n);
		b.resize(n);
		vector<int>w(n);
		for(int i=0; i<n; i++)w[i]=modpow(root,(mod-1)/n*i);
		function<void(vector<int>&,vector<int>&)>fft=[&](vector<int>&A,vector<int>&W) {
			int n=A.size();
			for(int i=1,j=0; i<n; i++) {
				int bit=n>>1;
				for(; j&bit; bit>>=1)j^=bit;
				j^=bit;
				if(i<j)swap(A[i],A[j]);
			}
			for(int len=2; len<=n; len<<=1) {
				int step=n/len;
				for(int i=0; i<n; i+=len)for(int j=0; j<len/2; j++) {
						int u=A[i+j],v=1LL*A[i+j+len/2]*W[step*j]%mod;
						A[i+j]=(u+v)%mod;
						A[i+j+len/2]=(u-v+mod)%mod;
					}
			}
		};
		fft(a,w);
		reverse(w.begin()+1,w.end());
		fft(b,w);
		vector<int>c(n);
		for(int i=0; i<n; i++)c[i]=1LL*a[i]*b[i]%mod;
		return c;
	}
}
ntt;
// polynomial inverse via Newton
struct PolyNewton {
	void inverse(vector<int>&a,vector<int>&res,int n) {
		res.assign(1,ntt.modpow(a[0],ntt.mod-2));
		while(res.size()<n) {
			int m=res.size()*2;
			vector<int>A(a.begin(),a.begin()+min((int)a.size(),m)),B=res;
			A=ntt.mul(A,ntt.mul(B,B));
			res.resize(m);
			for(int i=0; i<m; i++)res[i]=(2LL*res[i] - A[i] + ntt.mod)%ntt.mod;
		}
	}
}polyNewton;
// linear basis
struct LinearBasis {
	long long a[64];
	void init() {
		memset(a,0,sizeof(a));
	} void add(long long x) {
		for(int i=63; i>=0; i--)if(x>>i&1) {
				if(!a[i]) {
					a[i]=x;
					return;
				}
				x^=a[i];
			}
	} LinearBasis merge(LinearBasis&b) {
		LinearBasis c;
		for(int i=0; i<64; i++)c.a[i]=a[i]^b.a[i];
		return c;
	}
}basis;
// kd-tree
struct KDTree {
	struct Node {
		vector<int>pt;
		Node*l,*r;
	};
	Node*build(vector<vector<int>>&pts,int l,int r,int d) {
		if(l>r)return nullptr;
		int m=(l+r)/2;
		nth_element(pts.begin()+l,pts.begin()+m,pts.begin()+r+1,[&](auto&a,auto&b) {
			return a[d]<b[d];
		});
		Node*o=new Node();
		o->pt=pts[m];
		o->l=build(pts,l,m-1,(d+1)%pts[0].size());
		o->r=build(pts,m+1,r,(d+1)%pts[0].size());
		return o;
	}
}kdtree;
// mobius inversion apply (placeholder)
void mobiusInv(vector<long long>&f) {
	int n=f.size();
	for(int i=1; i<n; i++)for(int j=i; j<n; j+=i)f[j]-=f[i];
}
// min cost flow with SPFA
struct MinCostFlow {
	struct Edge {
		int v,w,c,nxt;
	};
	int head[MAXV],ecnt,S,T;
	int dist[MAXV],preV[MAXV],preE[MAXV];
	bool inq[MAXV];
	vector<Edge>e;
	void init(int n) {
		fill(head,head+n+1,-1);
		ecnt=0;
		e.clear();
	}
	void addEdge(int u,int v,int c,int w) {
		e.push_back({v,w,c,head[u]});
		head[u]=ecnt++;
		e.push_back({u,-w,0,head[v]});
		head[v]=ecnt++;
	}
	int minCost(int s,int t) {
		S=s;
		T=t;
		int flow=0,cost=0;
		while(true) {
			fill(dist,dist+T+1,INF);
			dist[S]=0;
			queue<int>q;
			q.push(S);
			inq[S]=1;
			while(!q.empty()) {
				int u=q.front();
				q.pop();
				inq[u]=0;
				for(int i=head[u]; i!=-1; i=e[i].nxt) {
					auto &ed=e[i];
					if(ed.c>0&&dist[ed.v]>dist[u]+ed.w) {
						dist[ed.v]=dist[u]+ed.w;
						preV[ed.v]=u;
						preE[ed.v]=i;
						if(!inq[ed.v]) {
							inq[ed.v]=1;
							q.push(ed.v);
						}
					}
				}
			}
			if(dist[T]==INF)break;
			int aug=INF;
			for(int v=T; v!=S; v=preV[v])aug=min(aug,e[preE[v]].c);
			flow+=aug;
			cost+=aug*dist[T];
			for(int v=T; v!=S; v=preV[v]) {
				auto &ed=e[preE[v]];
				ed.c-=aug;
				e[preE[v]^1].c+=aug;
			}
		}
		return cost;
	}
}flow;
int main() {
	ios::sync_with_stdio(false);
	cin.tie(NULL);
	int n,m;
	cin>>n>>m;
	flow.init(n);
	for(int i=0,u,v,c,w; i<m; i++) {
		cin>>u>>v>>c>>w;
		flow.addEdge(u,v,c,w);
	}
	int s,t;
	cin>>s>>t;
	cout<<flow.minCost(s,t);
	return 0;
}
