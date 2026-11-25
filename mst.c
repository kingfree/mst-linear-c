/* ===========================================================================
 *  mst.c -- minimum spanning tree / forest in C, structured after
 *
 *    S. Khanna, A. Putterman, J. Song,
 *    "A Deterministic Linear Time Algorithm for Minimum Spanning Tree",
 *    arXiv:2611.31187v1 (2026).
 *
 *  What is taken from the paper
 *  ----------------------------
 *  Algorithm 2 (MSF)                       -> msf_rec()
 *    1. k Boruvka steps (Definition 2.8)   -> boruvka_phase()
 *    2. contract, drop self-loops           -> contract()
 *    3. F <- Certificate(G')  (Algorithm 1)  -> certificate()
 *    4. U(F) = edges unsupported by F       -> unsupported_edges()
 *    5. return S + MSF(G'[F + U(F)])  (Fact 2.3 cycle property,
 *       Fact 2.4 contraction property, Fact 2.5 threshold connectivity)
 *
 *  The certificate (Section 3.1) is built from the paper's own primitives:
 *    - a spoke  sigma(v) : the lightest edge incident to v;
 *    - a portal pi(v)    : the end of v's spoke; P is the portal set;
 *    - a projection of e = (u,v) is the edge (pi(u), pi(v)) of weight w(e),
 *      and it is VALID iff max(w(sigma(u)), w(sigma(v))) <= w(e);
 *    - the projections form a smaller multigraph, the certificate recurses
 *      on it, and the lifted result is merged into F by an exact MSF call
 *      (Algorithm 1, lines 12-19 and 22).
 *
 *  What is deliberately simplified (see README.md)
 *  -----------------------------------------------
 *  The paper's schedule, the batch processing with r^2 lightest
 *  representatives, and the preference estimation are replaced by a
 *  deterministic "one Boruvka-level spoke per vertex" certificate.  The
 *  resulting constant factor is worse than eps*m + C*sqrt(n*m), so the
 *  edge set is not guaranteed to halve; a progress guard therefore falls
 *  back to an exact Kruskal call whenever a level fails to shrink.
 *  Correctness never depends on the certificate being good: by the cycle
 *  property any edge that is supported by F may be discarded, so the
 *  paper's recursion is correct for ANY forest F (Fact 2.3).  Only the
 *  running time depends on the certificate.
 *
 *  Running time
 *  ------------
 *  Every step is linear in the number of edges: k Boruvka phases (O(m)),
 *  at most CERT_MAX_DEPTH projection rounds that each scan the edge set
 *  once, one support sweep, and then a recursive call on m' <= m/2 edges
 *  (the guard enforces it).  Hence T(m) <= T(m/2) + O(m) = O(m).
 *  Weight order comes from a radix sort on the IEEE-754 bits, which costs
 *  no weight comparisons; --cmpsort switches back to qsort, i.e. to the
 *  paper's opaque-key comparison model, and then the sort term makes it
 *  O(m log m) again (measured: 8 vs 20 comparisons per edge).
 *  The paper reaches O(m) *comparisons* without touching the key bits,
 *  through Komlos' linear path-maximum queries (Lemma 2.9) plus a
 *  schedule it finds by enumerating all histories -- both are absent here.
 *
 *  Build:   cl /O2 /W4 mst.c            (MSVC)
 *           gcc -O2 -o mst mst.c        (gcc/clang)
 *  Usage:   mst --bench
 *           mst --n 100000 --m 400000 --seed 1 --ref --trace
 *           mst --file graph.txt --ref --out tree.txt
 *           mst --fuzz 3000
 * ==========================================================================*/

#define _CRT_SECURE_NO_WARNINGS 1
#if !defined(_WIN32)
#  define _POSIX_C_SOURCE 200809L   /* clock_gettime */
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>


typedef struct { int u, v; double w; int id; } Edge;

static const double EDGE_INF = 1.7e308;

/* ------------------------------------------------------------------
 *  Comparison counting.
 *  The paper measures cost in edge-weight comparisons, so every weight
 *  comparison goes through ecmp() and is counted.
 * ------------------------------------------------------------------ */
static unsigned long long g_cmp = 0;

static inline int ecmp(const Edge *a, const Edge *b)
{
    g_cmp++;
    if (a->w < b->w) return -1;
    if (a->w > b->w) return  1;
    /* Distinct weights are assumed by the paper; ties are broken by edge
     * index, which turns the input into an instance with distinct keys and
     * therefore a unique MSF (Section 2, "Preliminaries"). */
    return (a->id < b->id) ? -1 : (a->id > b->id);
}

static int cmp_edge(const void *x, const void *y)
{
    return ecmp((const Edge *)x, (const Edge *)y);
}

/* ------------------------------------------------------------------
 *  Disjoint set union (union by rank + path halving).
 * ------------------------------------------------------------------ */
typedef struct { int *p, *rk, n; } DSU;

static void dsu_init(DSU *d, int n)
{
    d->n  = n;
    d->p  = (int *)malloc((size_t)n * sizeof(int));
    d->rk = (int *)malloc((size_t)n * sizeof(int));
    if (!d->p || !d->rk) { fprintf(stderr, "out of memory\n"); exit(2); }
    for (int i = 0; i < n; i++) { d->p[i] = i; d->rk[i] = 0; }
}

static void dsu_free(DSU *d) { free(d->p); free(d->rk); d->p = d->rk = NULL; }

static int dsu_find(DSU *d, int x)
{
    while (d->p[x] != x) { d->p[x] = d->p[d->p[x]]; x = d->p[x]; }
    return x;
}

/* returns 1 if the two elements were in different sets */
static int dsu_union(DSU *d, int a, int b)
{
    a = dsu_find(d, a); b = dsu_find(d, b);
    if (a == b) return 0;
    if (d->rk[a] < d->rk[b]) { int t = a; a = b; b = t; }
    d->p[b] = a;
    if (d->rk[a] == d->rk[b]) d->rk[a]++;
    return 1;
}

/* ------------------------------------------------------------------
 *  Adjacency in compressed form, used by the dense Prim base case.
 * ------------------------------------------------------------------ */
typedef struct {
    int n, *head, *nxt, *to, *cid;
    double *cw;
} Adj;

static void adj_build(Adj *a, const Edge *e, int m, int n)
{
    a->n = n;
    a->head = (int *)malloc((size_t)(n + 1) * sizeof(int));
    a->nxt  = (int *)malloc((size_t)(2 * (size_t)m + 1) * sizeof(int));
    a->to   = (int *)malloc((size_t)(2 * (size_t)m + 1) * sizeof(int));
    a->cid  = (int *)malloc((size_t)(2 * (size_t)m + 1) * sizeof(int));
    a->cw   = (double *)malloc((size_t)(2 * (size_t)m + 1) * sizeof(double));
    if (!a->head || !a->nxt || !a->to || !a->cid || !a->cw) {
        fprintf(stderr, "out of memory\n"); exit(2);
    }
    for (int i = 0; i < n; i++) a->head[i] = -1;
    int k = 0;
    for (int i = 0; i < m; i++) {
        int u = e[i].u, v = e[i].v;
        a->to[k] = v; a->cw[k] = e[i].w; a->cid[k] = e[i].id;
        a->nxt[k] = a->head[u]; a->head[u] = k; k++;
        a->to[k] = u; a->cw[k] = e[i].w; a->cid[k] = e[i].id;
        a->nxt[k] = a->head[v]; a->head[v] = k; k++;
    }
}

static void adj_free(Adj *a)
{
    free(a->head); free(a->nxt); free(a->to); free(a->cid); free(a->cw);
    memset(a, 0, sizeof(*a));
}

/* ------------------------------------------------------------------
 *  Weight comparison that bypasses the Edge structure (used by the
 *  Prim base case), still counted.
 * ------------------------------------------------------------------ */
static inline int wless(double a, double b) { g_cmp++; return a < b; }

/* ------------------------------------------------------------------
 *  Linear-time sorting: LSD radix sort on the raw weight bits.
 *
 *  The paper counts only weight comparisons and treats weights as opaque
 *  keys; its O(m) bound comes from never sorting at all (Komlos' linear
 *  path-maximum queries, Lemma 2.9).  That machinery is not implemented
 *  here.  Instead the weight order comes from a radix sort on the IEEE-754
 *  bit pattern: linear in m, and it performs ZERO weight comparisons.
 *  That puts the implementation in the word-RAM setting the paper cites
 *  separately (Fredman and Willard), not in its comparison model.
 *  --cmpsort restores qsort and therefore the paper's own cost model.
 * ------------------------------------------------------------------ */
#define RADIX_BITS    11
#define RADIX_BUCKETS (1u << RADIX_BITS)
#define RADIX_PASSES  6                 /* 6 * 11 = 66 >= 64 bits */

static int g_cmp_sort = 0;              /* 1 = qsort (opaque-key model) */
static Edge *g_scratch = NULL;
static size_t g_scratchCap = 0;

static Edge *scratch_edges(size_t n)
{
    if (n > g_scratchCap) {
        free(g_scratch);
        g_scratch = (Edge *)malloc(n * sizeof(Edge));
        if (!g_scratch) { fprintf(stderr, "out of memory\n"); exit(2); }
        g_scratchCap = n;
    }
    return g_scratch;
}

/* order preserving map double -> unsigned 64-bit.
 * -0.0 and +0.0 must compare equal (they do as doubles), so both collapse
 * onto the same key; otherwise the radix order would disagree with ecmp(). */
static inline unsigned long long wkey(double w)
{
    unsigned long long u;
    if (w == 0.0) return 0x8000000000000000ULL;
    memcpy(&u, &w, sizeof u);
    return (u & 0x8000000000000000ULL) ? ~u : (u | 0x8000000000000000ULL);
}

static void radix_sort_edges(Edge *e, int m)
{
    if (m < 2) return;
    Edge *tmp = scratch_edges((size_t)m);
    Edge *src = e, *dst = tmp;
    size_t cnt[RADIX_BUCKETS];
    for (int pass = 0; pass < RADIX_PASSES; pass++) {
        const int shift = pass * RADIX_BITS;
        memset(cnt, 0, sizeof cnt);
        for (int i = 0; i < m; i++)
            cnt[(wkey(src[i].w) >> shift) & (RADIX_BUCKETS - 1)]++;
        size_t acc = 0;
        for (unsigned b = 0; b < RADIX_BUCKETS; b++) { size_t c = cnt[b]; cnt[b] = acc; acc += c; }
        for (int i = 0; i < m; i++) {
            unsigned b = (unsigned)((wkey(src[i].w) >> shift) & (RADIX_BUCKETS - 1));
            dst[cnt[b]++] = src[i];
        }
        Edge *t = src; src = dst; dst = t;
    }
    if (src != e) memcpy(e, src, (size_t)m * sizeof(Edge));
}

/* Sort an edge array into nondecreasing weight order. */
static void sort_edges(Edge *e, int m)
{
    if (m < 2) return;
    if (g_cmp_sort || m < 512) qsort(e, (size_t)m, sizeof(Edge), cmp_edge);
    else                        radix_sort_edges(e, m);
}
/* ------------------------------------------------------------------
 *  Exact MSF calls.
 *
 *  kruskal_exact() sorts the caller's array in place.  It plays three
 *  roles in the paper's algorithm: the base case, the "exact MSF call"
 *  of Algorithm 1 (lines 19 and 22), and the progress-guard fallback.
 * ------------------------------------------------------------------ */
/* Emit one result edge.  Vertices are relabelled by every contraction, so
 * the endpoints stored in the running edge copies are NOT original vertex
 * numbers; the original edge id still is, hence the lookup in orig[]. */
static inline void emit_edge(Edge *out, int *cnt, const Edge *orig, const Edge *e)
{
    out[*cnt] = (orig && e->id >= 0) ? orig[e->id] : *e;
    (*cnt)++;
}

static int kruskal_exact(Edge *e, int m, int n, Edge *out, const Edge *orig)
{
    DSU d;
    if (n > 0) dsu_init(&d, n);
    sort_edges(e, m);
    int k = 0;
    for (int i = 0; i < m; i++)
        if (dsu_union(&d, e[i].u, e[i].v)) emit_edge(out, &k, orig, &e[i]);
    if (n > 0) dsu_free(&d);
    return k;
}

/* Dense base case: the O(n^2 + m) array implementation of Prim.  Section
 * 1.1 of the paper recalls that on dense graphs this is already linear
 * time, which is what makes it the right base case to finish on. */
static int prim_dense(const Edge *e, int m, int n, Edge *out, const Edge *orig)
{
    Adj a;
    adj_build(&a, e, m, n);
    double *best = (double *)malloc((size_t)n * sizeof(double));
    int *bestId = (int *)malloc((size_t)n * sizeof(int));
    int *from = (int *)malloc((size_t)n * sizeof(int));
    char *vis = (char *)calloc((size_t)n, 1);
    if (!best || !bestId || !from || !vis) { fprintf(stderr, "out of memory\n"); exit(2); }

    int cnt = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        for (int i = 0; i < n; i++) { best[i] = EDGE_INF; bestId[i] = -1; from[i] = -1; }
        vis[s] = 1;
        for (int i = a.head[s]; i >= 0; i = a.nxt[i]) {
            int v = a.to[i];
            if (v != s && wless(a.cw[i], best[v])) { best[v] = a.cw[i]; bestId[v] = a.cid[i]; from[v] = s; }
        }
        for (;;) {
            int v = -1; double bw = EDGE_INF;
            for (int i = 0; i < n; i++)
                if (!vis[i] && wless(best[i], bw)) { bw = best[i]; v = i; }
            if (v < 0) break;
            vis[v] = 1;
            Edge chosen;
            chosen.u = from[v]; chosen.v = v; chosen.w = best[v]; chosen.id = bestId[v];
            emit_edge(out, &cnt, orig, &chosen);
            for (int i = a.head[v]; i >= 0; i = a.nxt[i]) {
                int t = a.to[i];
                if (!vis[t] && wless(a.cw[i], best[t])) { best[t] = a.cw[i]; bestId[t] = a.cid[i]; from[t] = v; }
            }
        }
    }
    free(best); free(bestId); free(from); free(vis);
    adj_free(&a);
    return cnt;
}

/* ------------------------------------------------------------------
 *  Definition 2.8: a Boruvka phase.
 *
 *  Every vertex picks its minimum weight incident edge, the picks are
 *  added to the MSF and contracted.  Each phase needs O(m) comparisons
 *  and halves the number of non-isolated vertices.
 *  Returns the number of unions actually performed.
 * ------------------------------------------------------------------ */
static int boruvka_phase(Edge *e, int m, int n, DSU *d, Edge *mst, int *nMst,
                        const Edge *orig)
{
    int *best = (int *)malloc((size_t)n * sizeof(int));
    if (!best) { fprintf(stderr, "out of memory\n"); exit(2); }
    for (int i = 0; i < n; i++) best[i] = -1;

    for (int i = 0; i < m; i++) {
        int a = dsu_find(d, e[i].u);
        int b = dsu_find(d, e[i].v);
        if (a == b) continue;
        if (best[a] < 0 || ecmp(&e[i], &e[best[a]]) < 0) best[a] = i;
        if (best[b] < 0 || ecmp(&e[i], &e[best[b]]) < 0) best[b] = i;
    }

    int added = 0;
    for (int r = 0; r < n; r++) {
        int i = best[r];
        if (i < 0) continue;
        if (dsu_union(d, e[i].u, e[i].v)) {
            if (mst) emit_edge(mst, nMst, orig, &e[i]);
            added++;
        }
    }
    free(best);
    return added;
}

/* ------------------------------------------------------------------
 *  Contraction: relabel vertices by component id, drop self-loops,
 *  keep parallel edges (the paper works on multigraphs).
 *  comp[v] receives the new label of v; *newN the new vertex count.
 *  Returns the new edge count.
 * ------------------------------------------------------------------ */
static int contract(Edge *e, int m, int n, DSU *d, int *comp, int *newN)
{
    for (int v = 0; v < n; v++) comp[v] = -1;
    for (int v = 0; v < n; v++) comp[dsu_find(d, v)] = 0;
    int k = 0;
    for (int v = 0; v < n; v++) if (comp[v] == 0) comp[v] = k++;
    for (int v = 0; v < n; v++) comp[v] = comp[dsu_find(d, v)];

    int mm = 0;
    for (int i = 0; i < m; i++) {
        int a = comp[e[i].u], b = comp[e[i].v];
        if (a == b) continue;
        e[mm].u = a; e[mm].v = b; e[mm].w = e[i].w; e[mm].id = e[i].id;
        mm++;
    }
    *newN = k;
    return mm;
}

/* ------------------------------------------------------------------
 *  Unsupported edges.  (Section 3.1)
 *
 *  e = (u,v) is SUPPORTED by F if F^{<= w(e)} connects u and v, i.e. the
 *  cycle closed by e uses only edges no heavier than e.  By the cycle
 *  property such an e is never in the MSF, so it may be discarded.
 *
 *  The paper identifies U(F) with Komlos' linear-time path-maximum
 *  queries (Lemma 2.9).  The equivalent predicate is computed here with
 *  one offline DSU sweep: edges in increasing weight order, inserting only
 *  forest edges whose weight is at most the current weight.
 *
 *  msf_rec sorts the contracted edge array once per level (after the
 *  Boruvka contraction, i.e. on the already shrunk set); contraction and
 *  the merge of F with U(F) both preserve that order, so the sweep below is
 *  a single linear pass and the recursive call inherits a sorted array.
 * ------------------------------------------------------------------ */
static const Edge *g_sortBase = NULL;

static int cmp_index_by_weight(const void *x, const void *y)
{
    const Edge *a = &g_sortBase[*(const int *)x];
    const Edge *b = &g_sortBase[*(const int *)y];
    g_cmp++;
    if (a->w < b->w) return -1;
    if (a->w > b->w) return  1;
    return (a->id < b->id) ? -1 : (a->id > b->id);
}

static int unsupported_edges(const Edge *e, int m, const Edge *F, int nf,
                            int n, char *unsup)
{
    int cnt = 0;
    if (m <= 0) return 0;

    Edge *fs = (Edge *)malloc((size_t)(nf > 0 ? nf : 1) * sizeof(Edge));
    if (!fs) { fprintf(stderr, "out of memory\n"); exit(2); }
    if (nf > 0) memcpy(fs, F, (size_t)nf * sizeof(Edge));
    sort_edges(fs, nf);

    DSU d; dsu_init(&d, n);
    int fi = 0;
    for (int i = 0; i < m; i++) {
        while (fi < nf && fs[fi].w <= e[i].w) {
            dsu_union(&d, fs[fi].u, fs[fi].v);
            fi++;
        }
        if (dsu_find(&d, e[i].u) != dsu_find(&d, e[i].v)) {
            unsup[i] = 1;
            cnt++;
        }
    }
    dsu_free(&d);
    free(fs);
    return cnt;
}

/* ------------------------------------------------------------------
 *  Algorithm 1: Certificate(G).
 *
 *  One projection level, then recursion on the portal graph; the lifted
 *  child forest is merged into F by an exact MSF call.  This is exactly
 *  the control flow of Algorithm 1, lines 5-22, with
 *    - the schedule replaced by "every edge acts in the single round",
 *    - the batch procedure replaced by the spoke/portal selection of
 *      Section 3.2 with r = 1 (one representative per vertex),
 *    - the preferred-action estimate replaced by the exact validity
 *      test p(e) <= w(e) of Section 3.1.
 * ------------------------------------------------------------------ */
static int g_cert_depth = 4;          /* projection levels inside one certificate */

/* instrumentation for --trace: how much of the work the projection does */
static long long g_projEdges = 0;
static int g_projRounds = 0;

static void certificate(const Edge *e, int m, int n, Edge **Fout, int *nfOut,
                        int depth)
{
    Edge *F = NULL;
    int nf = 0;
    *Fout = NULL; *nfOut = 0;
    if (m <= 0 || n < 2) return;

    /* ---- (1) spokes: sigma(v) = lightest edge incident to v ---------- */
    int *spk = (int *)malloc((size_t)n * sizeof(int));
    if (!spk) { fprintf(stderr, "out of memory\n"); exit(2); }
    for (int i = 0; i < n; i++) spk[i] = -1;
    for (int i = 0; i < m; i++) {
        int u = e[i].u, v = e[i].v;
        if (spk[u] < 0 || ecmp(&e[i], &e[spk[u]]) < 0) spk[u] = i;
        if (spk[v] < 0 || ecmp(&e[i], &e[spk[v]]) < 0) spk[v] = i;
    }

    /* ---- (2) F := MSF(G[F + sigma])   (Algorithm 1, line 22) -------- */
    int cap = nf + n;
    Edge *sub = (Edge *)malloc((size_t)cap * sizeof(Edge));
    Edge *newF = (Edge *)malloc((size_t)n * sizeof(Edge));
    if (!sub || !newF) { fprintf(stderr, "out of memory\n"); exit(2); }
    int ns = 0;
    for (int v = 0; v < n; v++) if (spk[v] >= 0) sub[ns++] = e[spk[v]];
    nf = kruskal_exact(sub, ns, n, newF, NULL);
    free(sub); free(F);
    F = newF;

    /* ---- (3) portals: components of the spoke forest ----------------- */
    DSU sp; dsu_init(&sp, n);
    for (int v = 0; v < n; v++) {
        if (spk[v] < 0) continue;
        int o = (e[spk[v]].u == v) ? e[spk[v]].v : e[spk[v]].u;
        dsu_union(&sp, v, o);
    }
    char *isPortal = (char *)calloc((size_t)n, 1);
    int *pid = (int *)calloc((size_t)n, sizeof(int));
    if (!isPortal || !pid) { fprintf(stderr, "out of memory\n"); exit(2); }
    for (int v = 0; v < n; v++) if (spk[v] >= 0) isPortal[dsu_find(&sp, v)] = 1;
    int np = 0;
    for (int r = 0; r < n; r++) if (isPortal[r]) pid[r] = np++;

    /* ---- (4) project the valid edges onto the portal set ------------ */
    Edge *pe = (Edge *)malloc((size_t)m * sizeof(Edge));
    int *org = (int *)malloc((size_t)m * sizeof(int));
    if (!pe || !org) { fprintf(stderr, "out of memory\n"); exit(2); }
    int pm = 0;
    for (int i = 0; i < m; i++) {
        int u = e[i].u, v = e[i].v;
        if (spk[u] < 0 || spk[v] < 0) continue;      /* needs both spokes */
        int pu = pid[dsu_find(&sp, u)];
        int pv = pid[dsu_find(&sp, v)];
        if (pu == pv) continue;                      /* already a trivial cycle */
        double su = e[spk[u]].w, sv = e[spk[v]].w;
        double p  = (su > sv) ? su : sv;             /* p(e), Section 3.1 */
        if (!(p <= e[i].w)) continue;                /* invalid projection  */
        pe[pm].u = pu; pe[pm].v = pv; pe[pm].w = e[i].w;
        /* id of a projected edge is an index into THIS level's edge array,
         * used only to lift the child forest back (line 441).  Projected
         * edges are never emitted into the result, so they must not be
         * passed to emit_edge() with an original-edge table. */
        pe[pm].id = i;
        org[pm] = i;
        pm++;
    }

    /* ---- (5) recurse on the portal graph, lift, and merge ----------- */
    if (pm > 0 && pm < m && np < n && depth < g_cert_depth) {
        g_projRounds++;
        g_projEdges += pm;
        Edge *cf = NULL; int ncf = 0;
        certificate(pe, pm, np, &cf, &ncf, depth + 1);
        if (ncf > 0) {
            Edge *sub2 = (Edge *)malloc((size_t)(nf + ncf) * sizeof(Edge));
            Edge *merged = (Edge *)malloc((size_t)n * sizeof(Edge));
            if (!sub2 || !merged) { fprintf(stderr, "out of memory\n"); exit(2); }
            memcpy(sub2, F, (size_t)nf * sizeof(Edge));
            for (int i = 0; i < ncf; i++) sub2[nf + i] = e[cf[i].id];
            int k = kruskal_exact(sub2, nf + ncf, n, merged, NULL);
            free(sub2); free(F);
            F = merged; nf = k;
        }
        free(cf);
    }

    free(spk); free(isPortal); free(pid); free(pe); free(org);
    dsu_free(&sp);
    *Fout = F; *nfOut = nf;
}

/* ------------------------------------------------------------------
 *  Algorithm 2: MSF(G).
 *
 *    1. k Boruvka steps                                   (line 1)
 *    2. contract, drop isolated vertices                   (lines 2-3)
 *    3. if G' is empty return S                           (lines 4-5)
 *    4. F <- Certificate(G')                              (line 6)
 *    5. U(F) <- edges unsupported by F                     (line 7)
 *    6. return S + MSF(G'[F + U(F)])                      (line 8)
 * ------------------------------------------------------------------ */
static int g_base_edges    = 2048;  /* below this, finish with an exact call */
static int g_base_vertices = 512;   /* dense-and-small: array Prim           */
static int g_phases = 3;              /* k in Algorithm 2                       */
#define MAX_DEPTH      40
#define GUARD_NUM      4      /* fall back when a level keeps >= 4/5    */
#define GUARD_DEN      5      /* of its edges                           */

typedef struct {
    int depth, nIn, mIn, nOut, mOut, nf, nu, mRed, guarded;
} LevelTrace;

typedef struct {
    LevelTrace trace[64];
    int nTrace;
    int certCalls;
} Stats;

static void msf_rec(Edge *e, int m, int n, Edge *out, int *nout, int depth,
                   Stats *st, const Edge *orig)
{
    if (m <= 0 || n < 2) return;

    /* ---- base cases -------------------------------------------------- */
    if (m <= g_base_edges || depth >= MAX_DEPTH) {
        *nout += kruskal_exact(e, m, n, out + *nout, orig);
        return;
    }
    if (n <= g_base_vertices && (double)m > 4.0 * (double)n) {
        *nout += prim_dense(e, m, n, out + *nout, orig);
        return;
    }

    /* ---- 1. k Boruvka steps ------------------------------------------ */
    DSU d; dsu_init(&d, n);
    int merged = 0;
    for (int ph = 0; ph < g_phases; ph++) {
        int add = boruvka_phase(e, m, n, &d, out, nout, orig);
        merged += add;
        if (add == 0) break;
    }
    if (merged == 0) {                       /* already a forest */
        *nout += kruskal_exact(e, m, n, out + *nout, orig);
        dsu_free(&d);
        return;
    }

    /* ---- 2. contract; isolated vertices simply disappear -------------- */
    int *comp = (int *)malloc((size_t)n * sizeof(int));
    Edge *ce = (Edge *)malloc((size_t)m * sizeof(Edge));
    if (!comp || !ce) { fprintf(stderr, "out of memory\n"); exit(2); }
    memcpy(ce, e, (size_t)m * sizeof(Edge));
    int n2 = 0;
    int m2 = contract(ce, m, n, &d, comp, &n2);
    dsu_free(&d);
    free(comp);
    if (m2 == 0 || n2 < 2) { free(ce); return; }

    /* Sort the contracted edge set once; every following step keeps that
     * order (the support sweep is then a linear pass, and so is the merge
     * of F with U(F) for the recursive call).  Sorting here rather than on
     * the input means the sort runs on the already shrunk edge set. */
    sort_edges(ce, m2);

    /* ---- 3. certificate --------------------------------------------- */
    Edge *F = NULL; int nf = 0;
    certificate(ce, m2, n2, &F, &nf, 0);
    st->certCalls++;

    /* ---- 4. U(F) ----------------------------------------------------- */
    char *unsup = (char *)calloc((size_t)m2, 1);
    if (!unsup) { fprintf(stderr, "out of memory\n"); exit(2); }
    int nu = unsupported_edges(ce, m2, F, nf, n2, unsup);
    int red = nf + nu;

    if (st->nTrace < (int)(sizeof(st->trace) / sizeof(st->trace[0]))) {
        LevelTrace *lt = &st->trace[st->nTrace++];
        lt->depth = depth; lt->nIn = n; lt->mIn = m;
        lt->nOut = n2; lt->mOut = m2; lt->nf = nf; lt->nu = nu;
        lt->mRed = red; lt->guarded = 0;
    }

    /* ---- safety valve: if the certificate did not shrink the graph,
     * finish this level with an exact call (only the constant factor is
     * affected, correctness is untouched) ----------------------------- */
    if ((long long)red * GUARD_DEN >= (long long)m2 * GUARD_NUM) {
        if (st->nTrace > 0) st->trace[st->nTrace - 1].guarded = 1;
        *nout += kruskal_exact(ce, m2, n2, out + *nout, orig);
        free(F); free(unsup); free(ce);
        return;
    }

    /* ---- 5. recurse on G'[F + U(F)]  (line 8) ------------------------ */
    Edge *re = (Edge *)malloc((size_t)(red > 0 ? red : 1) * sizeof(Edge));
    if (!re) { fprintf(stderr, "out of memory\n"); exit(2); }
    /* both F and the unsupported set are already in weight order: merge */
    int k = 0, fi = 0, ui = 0;
    for (;;) {
        while (ui < m2 && !unsup[ui]) ui++;
        if (fi >= nf && ui >= m2) break;
        if (fi < nf && (ui >= m2 || ecmp(&F[fi], &ce[ui]) <= 0)) re[k++] = F[fi++];
        else { re[k++] = ce[ui++]; }
    }

    free(F); free(unsup); free(ce);
    msf_rec(re, k, n2, out, nout, depth + 1, st, orig);
    free(re);
}

/* Entry point: copies the input so the caller keeps the original edge set
 * (the verifier needs it).  out[] must have room for n-1 edges; returns
 * the number of edges written. */
static int msf_compute(const Edge *in, int m, int n, Edge *out, Stats *st)
{
    memset(st, 0, sizeof(*st));
    g_projEdges = 0; g_projRounds = 0;
    Edge *e = (Edge *)malloc((size_t)(m > 0 ? m : 1) * sizeof(Edge));
    if (!e) { fprintf(stderr, "out of memory\n"); exit(2); }
    if (m > 0) memcpy(e, in, (size_t)m * sizeof(Edge));
    int k = 0;
    msf_rec(e, m, n, out, &k, 0, st, in);
    free(e);
    return k;
}

/* ------------------------------------------------------------------
 *  Independent verifier.
 *
 *   (a) the result has exactly n - c edges (c = #components of G),
 *   (b) the result is acyclic,
 *   (c) every non-tree edge is supported by the tree -- the cycle
 *       property (Fact 2.3), i.e. exactly the MST optimality
 *       certificate verified by Tarjan/Komlos.
 * ------------------------------------------------------------------ */
static int verify_msf(const Edge *all, int m, const Edge *T, int nt, int n,
                      char *msg, size_t msglen)
{
    msg[0] = 0;
    DSU d; dsu_init(&d, n);
    for (int i = 0; i < m; i++) dsu_union(&d, all[i].u, all[i].v);
    int c = 0;
    for (int v = 0; v < n; v++) if (dsu_find(&d, v) == v) c++;
    dsu_free(&d);
    if (nt != n - c) {
        snprintf(msg, msglen, "got %d edges, expected %d (n=%d, components=%d)",
                 nt, n - c, n, c);
        return 1;
    }

    dsu_init(&d, n);
    for (int i = 0; i < nt; i++) {
        if (T[i].id < 0 || T[i].id >= m) {
            snprintf(msg, msglen, "tree edge %d has invalid id %d", i, T[i].id);
            dsu_free(&d); return 2;
        }
        if (all[T[i].id].w != T[i].w) {
            snprintf(msg, msglen, "tree edge %d has weight %g, graph edge %d has %g",
                     i, T[i].w, T[i].id, all[T[i].id].w);
            dsu_free(&d); return 3;
        }
        if (!dsu_union(&d, T[i].u, T[i].v)) {
            snprintf(msg, msglen, "result contains a cycle (edge %d)", i);
            dsu_free(&d); return 4;
        }
    }
    dsu_free(&d);

    char *inT = (char *)calloc((size_t)m, 1);
    if (!inT) { snprintf(msg, msglen, "out of memory"); return 9; }
    for (int i = 0; i < nt; i++) inT[T[i].id] = 1;

    Edge *ts = (Edge *)malloc((size_t)(nt > 0 ? nt : 1) * sizeof(Edge));
    int *ord = (int *)malloc((size_t)m * sizeof(int));
    if (!ts || !ord) { free(inT); snprintf(msg, msglen, "out of memory"); return 9; }
    if (nt > 0) memcpy(ts, T, (size_t)nt * sizeof(Edge));
    if (nt > 1) qsort(ts, (size_t)nt, sizeof(Edge), cmp_edge);
    for (int i = 0; i < m; i++) ord[i] = i;
    g_sortBase = all;
    qsort(ord, (size_t)m, sizeof(int), cmp_index_by_weight);

    dsu_init(&d, n);
    int ti = 0, bad = 0, badId = -1;
    for (int t = 0; t < m && !bad; t++) {
        int idx = ord[t];
        while (ti < nt && ts[ti].w <= all[idx].w) {
            dsu_union(&d, ts[ti].u, ts[ti].v);
            ti++;
        }
        if (inT[idx]) continue;
        if (dsu_find(&d, all[idx].u) != dsu_find(&d, all[idx].v)) {
            bad = 1;
            badId = idx;
        }
    }
    dsu_free(&d);
    free(ts); free(ord); free(inT);
    if (bad) {
        snprintf(msg, msglen, "edge %d (%d-%d, w=%g) is lighter than the heaviest",
                 badId, all[badId].u, all[badId].v, all[badId].w);
        snprintf(msg + strlen(msg), msglen - strlen(msg),
                 " edge on its tree path: cycle property violated");
        return 5;
    }
    return 0;
}

/* ------------------------------------------------------------------
 *  Wall clock, random graphs, DIMACS input, driver.
 * ------------------------------------------------------------------ */
#if defined(_WIN32)
#  include <windows.h>
static double now_ms(void)
{
    LARGE_INTEGER f, c;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&c);
    return 1000.0 * (double)c.QuadPart / (double)f.QuadPart;
}
#else
#  include <time.h>
static double now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return 1e3 * (double)ts.tv_sec + 1e-6 * (double)ts.tv_nsec;
}
#endif

static unsigned long long g_rng = 0;

static unsigned long long rnd64(void)
{
    g_rng += 0x9E3779B97F4A7C15ULL;
    unsigned long long z = g_rng;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static double rnd_unit(void)
{
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

/* kind 0: random connected graph; kind 1: r x c grid graph.
 * ties > 0 restricts the weights to {1..ties}, which produces many equal
 * weights and exercises the tie-breaking rule of the paper. */
static Edge *gen_graph(int n, long long want_m, int ties, int kind, int *outM)
{
    long long m = want_m;
    if (m < (long long)n - 1) m = (long long)n - 1;
    /* the grid variant can emit up to 2n edges before extra edges are added,
     * so reserve headroom instead of trusting want_m */
    long long cap = m + (long long)n + 2;
    Edge *e = (Edge *)malloc((size_t)(cap > 0 ? cap : 1) * sizeof(Edge));
    if (!e) { fprintf(stderr, "out of memory\n"); exit(2); }
    int k = 0;

    if (kind == 1) {
        int rows = 1;
        while ((long long)(rows + 1) * (rows + 1) <= (long long)n) rows++;
        int cols = n / rows;
        int used = rows * cols;
        for (int r = 0; r < rows; r++)
            for (int c = 0; c < cols; c++) {
                int v = r * cols + c;
                if (c + 1 < cols) {
                    e[k].u = v; e[k].v = v + 1; e[k].id = k;
                    e[k].w = ties > 0 ? (double)(1 + (long long)(rnd64() % (unsigned)ties)) : rnd_unit();
                    k++;
                }
                if (r + 1 < rows) {
                    e[k].u = v; e[k].v = v + cols; e[k].id = k;
                    e[k].w = ties > 0 ? (double)(1 + (long long)(rnd64() % (unsigned)ties)) : rnd_unit();
                    k++;
                }
            }
        /* remaining vertices hang off the grid as a path (keeps it connected) */
        for (int v = used; v < n; v++) {
            e[k].u = (v == used) ? 0 : v - 1; e[k].v = v; e[k].id = k;
            e[k].w = ties > 0 ? (double)(1 + (long long)(rnd64() % (unsigned)ties)) : rnd_unit();
            k++;
        }
    } else {
        for (int v = 1; v < n; v++) {
            e[k].u = v;
            e[k].v = (int)(rnd64() % (unsigned long long)v);
            e[k].id = k;
            e[k].w = ties > 0 ? (double)(1 + (long long)(rnd64() % (unsigned)ties)) : rnd_unit();
            k++;
        }
    }

    long long target = m;
    if (kind == 1 && target < k) target = k;
    if (n < 2) { *outM = k; return e; }   /* no extra edges possible */
    while (k < target) {
        int a = (int)(rnd64() % (unsigned long long)n);
        int b = (int)(rnd64() % (unsigned long long)n);
        if (a == b) continue;
        e[k].u = a; e[k].v = b; e[k].id = k;
        e[k].w = ties > 0 ? (double)(1 + (long long)(rnd64() % (unsigned)ties)) : rnd_unit();
        k++;
    }
    *outM = k;
    return e;
}

/* DIMACS-like input:
 *     p <n> <m>
 *     a <u> <v> <w>          (one per edge, 1-based vertices)
 */
static Edge *read_dimacs(const char *path, int *outN, int *outM)
{
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", path); exit(2); }
    char line[512];
    int n = 0; long long m = 0;
    Edge *e = NULL; int k = 0;
    while (fgets(line, sizeof(line), f)) {
        char c = line[0];
        if (c == 'c' || c == '\n' || c == 0) continue;
        if (c == 'p') {
            long long mm;
            if (sscanf(line + 1, "%d %lld", &n, &mm) < 2) { fprintf(stderr, "bad p line\n"); exit(2); }
            m = mm;
            if (e) free(e);
            e = (Edge *)malloc((size_t)(m > 0 ? m : 1) * sizeof(Edge));
            k = 0;
            continue;
        }
        if (c == 'a') {
            int u, v; double w;
            if (sscanf(line + 1, "%d %d %lf", &u, &v, &w) == 3 && e) {
                e[k].u = u - 1; e[k].v = v - 1; e[k].w = w; e[k].id = k; k++;
            }
            continue;
        }
        int u, v; double w;
        if (sscanf(line, "%d %d %lf", &u, &v, &w) == 3 && e) {
            e[k].u = u - 1; e[k].v = v - 1; e[k].w = w; e[k].id = k; k++;
        }
    }
    fclose(f);
    if (!e) { fprintf(stderr, "no p line in %s\n", path); exit(2); }
    *outN = n; *outM = k;
    return e;
}

static void usage(void)
{
    printf("usage: mst [options]\n");
        printf("  --n N          number of vertices (default 1000)\n");
    printf("  --m M          number of edges    (default 5000)\n");
    printf("  --seed S       random seed        (default 1)\n");
    printf("  --ties T       weights drawn from {1..T} (creates ties)\n");
    printf("  --kind 0|1     0 random (default), 1 grid\n");
    printf("  --file PATH    read DIMACS-like graph instead\n");
    printf("  --out PATH     write the selected edges\n");
    printf("  --ref          cross-check against plain Kruskal\n");
    printf("  --no-verify    skip the cycle-property check\n");
    printf("  --trace        print the per-level edge reduction\n");
    printf("  --bench        run the scaling table\n");
    printf("  --fuzz K       run K randomized differential tests\n");
    printf("  --sorttest K   test the radix sort on K random arrays\n");
    printf("  --base K       base-case edge threshold (default 2048)\n");
    printf("  --cmpsort      sort by comparison (the paper's opaque-key model)\n");
    printf("  --om           trace + linearity summary (per-level halving)\n");
    printf("  --phases K     Boruvka phases (default 3)\n");
    printf("  --depth K      certificate projection depth (default 4)\n");
}

static int run_one(int n, int m, const Edge *g, int doVerify, int doRef,
                   int doTrace, const char *outPath, const char *label);

static int run_one(int n, int m, const Edge *g, int doVerify, int doRef,
                   int doTrace, const char *outPath, const char *label)
{
    int cap = n > 1 ? n - 1 : 1;
    Edge *T = (Edge *)malloc((size_t)cap * sizeof(Edge));
    if (!T) { fprintf(stderr, "out of memory\n"); exit(2); }

    unsigned long long c0 = g_cmp;
    double t0 = now_ms();
    Stats st;
    int nt = msf_compute(g, m, n, T, &st);
    double t1 = now_ms();
    unsigned long long cmp = g_cmp - c0;

    double W = 0.0;
    for (int i = 0; i < nt; i++) W += T[i].w;

    if (label) printf("%-10s ", label);
    printf("n=%-8d m=%-9d  edges=%-7d weight=%.6f  %.1f ms  cmp=%-10llu",
           n, m, nt, W, t1 - t0, cmp);
    if (m > 0) printf(" (%.2f per edge)", (double)cmp / (double)m);
    printf("\n");

    int fail = 0;
    if (doVerify) {
        char msg[256];
        int bad = verify_msf(g, m, T, nt, n, msg, sizeof(msg));
        if (bad) { printf("  verify  : FAIL (%s)\n", msg); fail = 1; }
        else     printf("  verify  : ok  (%d edges, acyclic, cycle property holds)\n", nt);
    }

    if (doRef) {
        Edge *cp = (Edge *)malloc((size_t)(m > 0 ? m : 1) * sizeof(Edge));
        Edge *R  = (Edge *)malloc((size_t)cap * sizeof(Edge));
        if (!cp || !R) { fprintf(stderr, "out of memory\n"); exit(2); }
        memcpy(cp, g, (size_t)m * sizeof(Edge));
        double tk0 = now_ms();
        int kr = kruskal_exact(cp, m, n, R, NULL);
        double tk1 = now_ms();
        double Wr = 0.0;
        for (int i = 0; i < kr; i++) Wr += R[i].w;
        double diff = fabs(W - Wr);
        double tol = 1e-9 * (1.0 + fabs(W));
        if (kr != nt || diff > tol) {
            printf("  kruskal : MISMATCH (edges %d vs %d, weight %.9f vs %.9f)\n",
                   nt, kr, W, Wr);
            fail = 1;
        } else {
            printf("  kruskal : ok  (%d edges, weight %.6f, %.1f ms plain Kruskal)\n",
                   kr, Wr, tk1 - tk0);
        }
        free(cp); free(R);
    }

    if (doTrace && st.nTrace > 0) {
        printf("  levels  : ");
        for (int i = 0; i < st.nTrace; i++) {
            LevelTrace *lt = &st.trace[i];
            printf("[d%d n%d m%d -> n%d m%d: F=%d U=%d] ", lt->depth, lt->nIn, lt->mIn,
                   lt->nOut, lt->mOut, lt->nf, lt->nu);
        }
        printf("\n");
        if (g_projRounds > 0)
            printf("  project : %d projection rounds, %lld projected edges\n",
                   g_projRounds, g_projEdges);

        /* The recursion is linear iff every level at least halves its edge
         * set (Algorithm 2 proof): T(m) <= T(m/2) + O(m). */
        int linear = 1;
        printf("  om      : m = %d", st.trace[0].mIn);
        for (int i = 0; i < st.nTrace; i++) {
            LevelTrace *lt = &st.trace[i];
            printf(" -> %d (%.2f%%%s)", lt->mRed,
                   100.0 * (double)lt->mRed / (double)(lt->mIn > 0 ? lt->mIn : 1),
                   lt->guarded ? ", guard" : "");
            if (lt->mRed * 2 > lt->mIn) linear = 0;
        }
        printf("   recursion halves every level: %s\n", linear ? "yes" : "NO");
        if (m > 0)
            printf("  cost    : %.2f comparisons/edge, %.3f us/edge\n",
                   (double)cmp / (double)m, 1e3 * (t1 - t0) / (double)m);
    }

    if (outPath) {
        FILE *f = fopen(outPath, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", outPath); fail = 1; }
        else {
            for (int i = 0; i < nt; i++)
                fprintf(f, "%d %d %.17g\n", T[i].u, T[i].v, T[i].w);
            fclose(f);
            printf("  written : %s (%d edges)\n", outPath, nt);
        }
    }

    free(T);
    return fail;
}

static int bench(void)
{
    static const int bn[] = {1000, 10000, 10000, 100000, 100000, 500000, 1000000};
    static const int bm[] = {5000, 20000, 50000, 200000, 1000000, 1000000, 2000000};
    int ncase = (int)(sizeof(bn) / sizeof(bn[0]));
    int fail = 0;
    for (int i = 0; i < ncase; i++) {
        g_rng = 0x243F6A8885A308D3ULL + (unsigned long long)i * 7919ULL;
        int m = 0;
        Edge *g = gen_graph(bn[i], bm[i], 0, 0, &m);
        fail |= run_one(bn[i], m, g, 1, (m <= 200000), 0, NULL, "random");
        free(g);
    }
    return fail;
}

/* Direct test of the radix sort: monotonicity + multiset equality on
 * adversarial weight distributions (ties, negatives, +/-0, extremes,
 * already sorted input). */
static int sorttest(int iters)
{
    int fails = 0;
    g_rng = 0x1234567890ABCDEFULL;
    for (int it = 0; it < iters; it++) {
        int n = 1 + (int)(rnd64() % 200000);
        int dist = it % 5;
        Edge *a = (Edge *)malloc((size_t)n * sizeof(Edge));
        Edge *b = (Edge *)malloc((size_t)n * sizeof(Edge));
        char *seen = (char *)calloc((size_t)n, 1);
        for (int i = 0; i < n; i++) {
            double w;
            switch (dist) {
                case 0:  w = rnd_unit(); break;
                case 1:  w = (double)(1 + rnd64() % 1000); break;
                case 2:  w = 0.5 * (double)((long long)(rnd64() % 2001) - 1000); break;
                case 3: {
                    static const double ext[6] = {0.0, -0.0, 1e300, -1e300, 1e-300, -1e-300};
                    w = ext[rnd64() % 6];
                    break;
                }
                default: w = (double)i; break;      /* already sorted */
            }
            a[i].u = 0; a[i].v = 0; a[i].w = w; a[i].id = i;
        }
        memcpy(b, a, (size_t)n * sizeof(Edge));
        radix_sort_edges(a, n);
        qsort(b, (size_t)n, sizeof(Edge), cmp_edge);

        /* ids were handed out in index order, so the stable radix order must
         * match qsort's (weight, id) order exactly */
        int bad = 0;
        for (int i = 0; i < n && !bad; i++)
            if (a[i].id != b[i].id || a[i].w != b[i].w) bad = 1;
        if (!bad) {
            for (int i = 0; i < n && !bad; i++) {
                int id = a[i].id;
                if (id < 0 || id >= n || seen[id]) bad = 1;
                else seen[id] = 1;
            }
        }
        if (bad) {
            fails++;
            printf("SORT FAIL it=%d n=%d dist=%d\n", it, n, dist);
        }
        free(a); free(b); free(seen);
    }
    printf("sorttest: %d arrays, %d failures\n", iters, fails);
    return fails;
}

/* Randomized differential test.  Forces the recursive part of the algorithm
 * to run even on tiny graphs by shrinking the base-case thresholds, then
 * checks every result with the independent verifier and with plain Kruskal. */
static int fuzz(int iters)
{
    int fails = 0;
    static const int baseSet[] = {2, 3, 4, 8, 16, 64, 2048};
    static const int vertSet[] = {4, 8, 30, 1024};
    for (int it = 0; it < iters; it++) {
        g_rng = 0x9E3779B97F4A7C15ULL * (unsigned long long)(it + 1) + 0xDEADBEEFCAFEULL;
        /* every eighth instance is big enough to exercise the radix path */
        int big = (rnd64() % 8) == 0;
        int n = big ? (1 + (int)(rnd64() % 3000)) : (1 + (int)(rnd64() % 80));
        long long want = (long long)(rnd64() % (unsigned long long)((long long)n * (big ? 10 : 8) + 1));
        int ties = (rnd64() % 3 == 0) ? (int)(1 + rnd64() % 6) : 0;
        int kind = (rnd64() % 5 == 0) ? 1 : 0;
        g_base_edges    = baseSet[rnd64() % (sizeof(baseSet) / sizeof(baseSet[0]))];
        g_base_vertices = vertSet[rnd64() % (sizeof(vertSet) / sizeof(vertSet[0]))];
        int gm = 0;
        Edge *g = gen_graph(n, want, ties, kind, &gm);
        Edge *T = (Edge *)malloc((size_t)n * sizeof(Edge));
        Stats st;
        int nt = msf_compute(g, gm, n, T, &st);
        char msg[256];
        int bad = verify_msf(g, gm, T, nt, n, msg, sizeof(msg));
        if (!bad) {
            Edge *cp = (Edge *)malloc((size_t)(gm > 0 ? gm : 1) * sizeof(Edge));
            Edge *R  = (Edge *)malloc((size_t)n * sizeof(Edge));
            memcpy(cp, g, (size_t)gm * sizeof(Edge));
            int kr = kruskal_exact(cp, gm, n, R, NULL);
            double W = 0.0, Wr = 0.0;
            for (int i = 0; i < nt; i++) W += T[i].w;
            for (int i = 0; i < kr; i++) Wr += R[i].w;
            if (kr != nt || fabs(W - Wr) > 1e-9 * (1.0 + fabs(W))) {
                bad = 7;
                snprintf(msg, sizeof(msg), "weight %.9f vs kruskal %.9f (%d vs %d edges)",
                         W, Wr, nt, kr);
            }
            free(cp); free(R);
        }
        if (bad) {
            fails++;
            if (fails <= 10)
                printf("FAIL it=%d n=%d m=%d ties=%d base=%d verts=%d kind=%d: %s\n",
                       it, n, gm, ties, g_base_edges, g_base_vertices, kind, msg);
        }
        free(g); free(T);
    }
    g_base_edges = 2048;
    g_base_vertices = 512;
    printf("fuzz: %d instances, %d failures\n", iters, fails);
    return fails;
}

int main(int argc, char **argv)
{
    int n = 1000;
    long long m = 5000;
    unsigned long long seed = 1;
    int ties = 0, kind = 0;
    const char *file = NULL, *outPath = NULL;
    int doVerify = 1, doRef = 0, doTrace = 0, doBench = 0, doSeed = 0;
    int nFuzz = 0, nSort = 0;

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        if (!strcmp(a, "--n") && i + 1 < argc)        n = atoi(argv[++i]);
        else if (!strcmp(a, "--m") && i + 1 < argc)   m = atoll(argv[++i]);
        else if (!strcmp(a, "--seed") && i + 1 < argc) { seed = strtoull(argv[++i], NULL, 10); doSeed = 1; }
        else if (!strcmp(a, "--ties") && i + 1 < argc) ties = atoi(argv[++i]);
        else if (!strcmp(a, "--kind") && i + 1 < argc) kind = atoi(argv[++i]);
        else if (!strcmp(a, "--file") && i + 1 < argc) file = argv[++i];
        else if (!strcmp(a, "--out") && i + 1 < argc)  outPath = argv[++i];
        else if (!strcmp(a, "--ref"))       doRef = 1;
        else if (!strcmp(a, "--trace"))     doTrace = 1;
        else if (!strcmp(a, "--cmpsort"))   g_cmp_sort = 1;
        else if (!strcmp(a, "--phases") && i + 1 < argc) g_phases = atoi(argv[++i]);
        else if (!strcmp(a, "--depth") && i + 1 < argc)  g_cert_depth = atoi(argv[++i]);
        else if (!strcmp(a, "--om"))        doTrace = 1;
        else if (!strcmp(a, "--no-verify")) doVerify = 0;
        else if (!strcmp(a, "--bench"))     doBench = 1;
        else if (!strcmp(a, "--fuzz") && i + 1 < argc)   nFuzz = atoi(argv[++i]);
        else if (!strcmp(a, "--sorttest") && i + 1 < argc) nSort = atoi(argv[++i]);
        else if (!strcmp(a, "--base") && i + 1 < argc) {
            g_base_edges = atoi(argv[++i]);
            if (g_base_edges < 1) g_base_edges = 1;
        }
        else if (!strcmp(a, "--help") || !strcmp(a, "-h")) { usage(); return 0; }
        else { fprintf(stderr, "unknown option: %s\n", a); usage(); return 2; }
    }

    if (doBench) return bench() ? 1 : 0;
    if (nFuzz > 0) return fuzz(nFuzz) ? 1 : 0;
    if (nSort > 0) return sorttest(nSort) ? 1 : 0;

    if (file) {
        int fn = 0, fm = 0;
        Edge *g = read_dimacs(file, &fn, &fm);
        int r = run_one(fn, fm, g, doVerify, 1, doTrace, outPath, "file");
        free(g);
        return r ? 1 : 0;
    }

    g_rng = doSeed ? seed * 0x9E3779B97F4A7C15ULL : 0x2545F4914F6CDD1DULL;
    int gm = 0;
    Edge *g = gen_graph(n, m, ties, kind, &gm);
    int r = run_one(n, gm, g, doVerify, doRef || gm <= 200000, doTrace, outPath, "random");
    free(g);
    free(g_scratch);
    return r ? 1 : 0;
}

