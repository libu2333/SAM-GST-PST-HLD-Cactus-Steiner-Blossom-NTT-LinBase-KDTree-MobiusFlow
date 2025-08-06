#include<bits/stdc++.h>
using namespace std;
const int MAXV=100005,MAXE=200005,INF=0x3f3f3f3f;
struct SAM {
    static const int N = MAXV * 2;
    int len[N], link[N], ch[N][26], last, tot;
    vector<int> tree[N];

    SuffixAutomaton() { init(); }
    void init() {
        memset(ch[0], 0, sizeof ch[0]);
        tot = last = 1;
        len[1] = 0; link[1] = 0;
    }

    void extend(char c) {
        int x = c - 'a', cur = ++tot, p = last;
        len[cur] = len[p] + 1;
        while (p && !ch[p][x]) ch[p][x] = cur, p = link[p];
        if (!p) link[cur] = 1;
        else {
            int q = ch[p][x];
            if (len[q] == len[p] + 1) link[cur] = q;
            else {
                int clone = ++tot;
                len[clone] = len[p] + 1;
                memcpy(ch[clone], ch[q], sizeof ch[q]);
                link[clone] = link[q];
                while (p && ch[p][x] == q) ch[p][x] = clone, p = link[p];
                link[q] = link[cur] = clone;
            }
        }
        last = cur;
    }

    void buildTree() {
        for (int i = 2; i <= tot; ++i)
            tree[link[i]].push_back(i);
    }
} sam;

struct GeneralizedSuffixTree {
    SuffixAutomaton sam;
    vector<int> pos[11]; // position list for each string

    void addString(const string& s, int idx) {
        sam.last = 1;
        for (char c : s) {
            sam.extend(c);
            pos[idx].push_back(sam.last);
        }
    }

    void finalize() {
        sam.buildTree();
    }
} sft;
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
    vector<int> adj[MAXV];
    int fa[MAXV], dep[MAXV], top[MAXV], sz[MAXV], son[MAXV], dfn[MAXV], clk = 0;
    int f[MAXV];
    vector<int> pts;

    void addEdge(int u, int v) {
        adj[u].push_back(v);
        adj[v].push_back(u);
    }

    void dfs1(int u, int p) {
        fa[u] = p; sz[u] = 1; son[u] = 0;
        for (int v : adj[u]) if (v != p) {
            dep[v] = dep[u] + 1;
            dfs1(v, u);
            sz[u] += sz[v];
            if (sz[v] > sz[son[u]]) son[u] = v;
        }
    }

    void dfs2(int u, int tp) {
        top[u] = tp; dfn[u] = ++clk;
        if (son[u]) dfs2(son[u], tp);
        for (int v : adj[u]) if (v != fa[u] && v != son[u]) dfs2(v, v);
    }

    int lca(int u, int v) {
        while (top[u] != top[v]) {
            if (dep[top[u]] < dep[top[v]]) swap(u, v);
            u = fa[top[u]];
        }
        return dep[u] < dep[v] ? u : v;
    }

    void markSteiner(vector<int>& nodes) {
        sort(nodes.begin(), nodes.end(), [&](int a, int b) { return dfn[a] < dfn[b]; });
        stack<int> stk; stk.push(nodes[0]);
        vector<pair<int,int>> extraEdges;
        for (int i = 1; i < nodes.size(); ++i) {
            int l = lca(stk.top(), nodes[i]);
            vector<int> tmp;
            while (dep[stk.top()] > dep[l]) {
                tmp.push_back(stk.top()); stk.pop();
            }
            if (stk.top() != l) {
                tmp.push_back(stk.top()); stk.pop();
                stk.push(l);
            }
            for (int j = tmp.size() - 1; j > 0; --j)
                extraEdges.emplace_back(tmp[j], tmp[j - 1]);
            if (!tmp.empty()) extraEdges.emplace_back(stk.top(), tmp.back());
            stk.push(nodes[i]);
        }
        vector<int> final;
        while (stk.size() > 1) {
            int u = stk.top(); stk.pop();
            extraEdges.emplace_back(stk.top(), u);
        }
        for (auto [u,v] : extraEdges) {
            f[u] = 1; f[v] = 1;
        }
    }

    vector<int> buildSteiner(vector<int>& terminals) {
        pts = terminals;
        dfs1(pts[0], 0);
        dfs2(pts[0], pts[0]);
        markSteiner(terminals);
        vector<int> result;
        for (int v : pts) if (f[v]) result.push_back(v);
        return result;
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
struct LinearBasis{
    static const int LG = 64;
    long long a[LG];
    void init(){memset(a,0,sizeof(a));}
    void add(long long x){
        for(int i=LG-1;i>=0;i--)if(x>>i&1){
            if(!a[i]){a[i]=x;return;}
            x^=a[i];
        }
    }
    bool canRepresent(long long x){
        for(int i=LG-1;i>=0;i--)if(x>>i&1)x^=a[i];
        return x==0;
    }
    long long maxXor(long long res=0){
        for(int i=LG-1;i>=0;i--)res=max(res,res^a[i]);
        return res;
    }
    LinearBasis merge(LinearBasis&b){
        LinearBasis res=*this;
        for(int i=0;i<LG;i++)if(b.a[i])res.add(b.a[i]);
        return res;
    }
}basis;
// kd-tree
struct KDTree{
    static const int K = 2; // dimension
    struct Node{
        array<int,K> pt;
        Node *l=nullptr, *r=nullptr;
        Node(array<int,K> _pt): pt(_pt) {}
    };

    Node* root = nullptr;
    vector<array<int,K>> data;

    Node* build(int l,int r,int d){
        if(l > r) return nullptr;
        int m=(l+r)>>1;
        nth_element(data.begin()+l, data.begin()+m, data.begin()+r+1, [&](const array<int,K>&a, const array<int,K>&b){ return a[d]<b[d]; });
        Node* node = new Node(data[m]);
        node->l = build(l,m-1,(d+1)%K);
        node->r = build(m+1,r,(d+1)%K);
        return node;
    }

    void buildTree(){
        root = build(0,data.size()-1,0);
    }

    void insert(Node*& node, array<int,K> pt, int d){
        if(!node){ node = new Node(pt); return; }
        if(pt[d] < node->pt[d]) insert(node->l, pt, (d+1)%K);
        else insert(node->r, pt, (d+1)%K);
    }

    void insert(array<int,K> pt){
        data.push_back(pt);
        insert(root, pt, 0);
    }

    int dist2(const array<int,K>&a, const array<int,K>&b){
        int res = 0;
        for(int i = 0; i < K; i++) res += (a[i]-b[i])*(a[i]-b[i]);
        return res;
    }

    void knn(Node* node, array<int,K>& target, int k, int d, priority_queue<pair<int,array<int,K>>>& pq){
        if(!node) return;
        int d2 = dist2(node->pt, target);
        pq.push({d2, node->pt});
        if((int)pq.size() > k) pq.pop();
        int diff = target[d] - node->pt[d];
        if(diff < 0){
            knn(node->l, target, k, (d+1)%K, pq);
            if((int)pq.size()<k || diff*diff < pq.top().first) knn(node->r, target, k, (d+1)%K, pq);
        }else{
            knn(node->r, target, k, (d+1)%K, pq);
            if((int)pq.size()<k || diff*diff < pq.top().first) knn(node->l, target, k, (d+1)%K, pq);
        }
    }

    vector<array<int,K>> knn(array<int,K> target, int k){
        priority_queue<pair<int,array<int,K>>> pq;
        knn(root, target, k, 0, pq);
        vector<array<int,K>> res;
        while(!pq.empty()) res.push_back(pq.top().second), pq.pop();
        reverse(res.begin(), res.end());
        return res;
    }

    // NOTE: KDTree deletion is complex; here we just rebuild tree for simplicity
    void erase(array<int,K> pt){
        data.erase(remove(data.begin(), data.end(), pt), data.end());
        root = build(0, data.size()-1, 0);
    }
}kdtree;
// mobius inversion apply (placeholder)
const int MAXN = 305;
int mu[MAXN];
void calcMobius() {
    for (int i = 1; i < MAXN; i++) mu[i] = 1;
    for (int i = 2; i < MAXN; i++) {
        if (mu[i] == 1) {
            for (int j = i; j < MAXN; j += i) mu[j] *= -i;
            for (int j = i * i; j < MAXN; j += i * i) mu[j] = 0;
        }
    }
    for (int i = 1; i < MAXN; i++) if (mu[i] == i) mu[i] = 1; else if (mu[i] == -i) mu[i] = -1; else if (mu[i] < 0) mu[i] = 1; else if (mu[i] > 0) mu[i] = -1;
}

void mobius2D(vector<vector<long long>>& f, vector<vector<long long>>& g, int n, int m) {
    calcMobius();
    g.assign(n+1, vector<long long>(m+1, 0));
    for (int x = 1; x <= n; x++)
        for (int y = 1; y <= m; y++)
            for (int d1 = 1; d1 * d1 <= x; ++d1) if (x % d1 == 0)
                for (int d2 = 1; d2 * d2 <= y; ++d2) if (y % d2 == 0) {
                    int u1 = d1, u2 = d2;
                    int v1 = x/d1, v2 = y/d2;
                    g[x][y] += mu[v1] * mu[v2] * f[u1][u2];
                    if (d1 * d1 != x) {
                        u1 = x/d1; v1 = d1;
                        g[x][y] += mu[v1] * mu[v2] * f[u1][u2];
                    }
                    if (d2 * d2 != y) {
                        u2 = y/d2; v2 = d2;
                        g[x][y] += mu[v1] * mu[v2] * f[u1][u2];
                    }
                    if (d1*d1!=x && d2*d2!=y) {
                        u1 = x/d1; u2 = y/d2;
                        v1 = d1; v2 = d2;
                        g[x][y] += mu[v1] * mu[v2] * f[u1][u2];
                    }
                }
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

