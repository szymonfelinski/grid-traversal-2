#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <string.h>
#include <limits.h>

#define EXACT_LIMIT 16   // component size <= this -> run exact DP (safe & fast)
#define GREEDY_TRIES 150 // randomized greedy repeats for large components

typedef struct { int rows, cols; bool **blocked; } Grid;
typedef struct { int r, c; } Coord;

Grid *create_grid(int rows, int cols, int blocked_count, const int blocked_list[][2]) {
    if (rows <= 0 || cols <= 0) return NULL;
    Grid *g = (Grid*)malloc(sizeof(Grid));
    if (!g) { fprintf(stderr, "alloc grid failed\n"); exit(1); }
    g->rows = rows; g->cols = cols;
    g->blocked = (bool**)malloc((size_t)rows * sizeof(bool*));
    if (!g->blocked) { fprintf(stderr, "alloc rows failed\n"); free(g); exit(1); }
    for (int r = 0; r < rows; r++) {
        g->blocked[r] = (bool*)malloc((size_t)cols * sizeof(bool));
        if (!g->blocked[r]) { fprintf(stderr, "alloc row %d failed\n", r);
            for (int i = 0; i < r; i++) free(g->blocked[i]);
            free(g->blocked); free(g); exit(1);
        }
        for (int c = 0; c < cols; c++) g->blocked[r][c] = false;
    }
    if (blocked_list && blocked_count > 0) {
        for (int i = 0; i < blocked_count; i++) {
            int br = blocked_list[i][0], bc = blocked_list[i][1];
            if (br >= 0 && br < rows && bc >= 0 && bc < cols) g->blocked[br][bc] = true;
        }
    }
    return g;
}

void free_grid(Grid *g) {
    if (!g) return;
    for (int r = 0; r < g->rows; r++) free(g->blocked[r]);
    free(g->blocked);
    free(g);
}

void print_grid(const Grid *g) {
    if (!g) return;
    for (int r = 0; r < g->rows; r++) {
        for (int c = 0; c < g->cols; c++) putchar(g->blocked[r][c] ? '#' : '.');
        putchar('\n');
    }
}

void generate_blocked(Grid *g, int num_blocked) {
    if (!g || num_blocked <= 0) return;
    long long rows = g->rows, cols = g->cols;
    long long total = rows * cols;
    long long already = 0;
    for (int r = 0; r < g->rows; r++) for (int c = 0; c < g->cols; c++) if (g->blocked[r][c]) already++;
    long long avail = total - already;
    if (avail <= 0) return;
    if (num_blocked > avail) num_blocked = (int)avail;
    if (num_blocked == 0) return;

    if (avail <= 2000000 || num_blocked * 4 > avail) {
        int *free_idx = (int*)malloc((size_t)avail * sizeof(int));
        if (!free_idx) goto rej;
        int pos = 0;
        for (int r = 0; r < g->rows; r++) for (int c = 0; c < g->cols; c++)
            if (!g->blocked[r][c]) free_idx[pos++] = r * g->cols + c;
        for (int i = 0; i < num_blocked; i++) {
            int j = i + rand() % (pos - i);
            int tmp = free_idx[i]; free_idx[i] = free_idx[j]; free_idx[j] = tmp;
        }
        for (int i = 0; i < num_blocked; i++) {
            int idx = free_idx[i];
            g->blocked[idx / g->cols][idx % g->cols] = true;
        }
        free(free_idx); return;
    }
rej:
    int placed = 0, attempts = 0, max_attempts = num_blocked * 30 + 1000;
    while (placed < num_blocked && attempts < max_attempts) {
        int r = rand() % g->rows, c = rand() % g->cols;
        if (!g->blocked[r][c]) { g->blocked[r][c] = true; placed++; }
        attempts++;
    }
    if (placed >= num_blocked) return;
    for (int r = 0; r < g->rows && placed < num_blocked; r++)
        for (int c = 0; c < g->cols && placed < num_blocked; c++)
            if (!g->blocked[r][c]) { g->blocked[r][c] = true; placed++; }
}

/* ---------- connected component (BFS) ----------
   returns malloc'ed array of coords (size set in out_count). Caller frees it.
*/
Coord *find_largest_component(const Grid *g, int *out_count) {
    *out_count = 0;
    int R = g->rows, C = g->cols;
    unsigned char *seen = (unsigned char*)calloc((size_t)R * C, 1);
    if (!seen) { fprintf(stderr, "alloc failed\n"); exit(1); }
    int *qr = (int*)malloc((size_t)R * C * sizeof(int));
    int *qc = (int*)malloc((size_t)R * C * sizeof(int));
    if (!qr || !qc) { fprintf(stderr, "alloc failed\n"); exit(1); }

    Coord *best = NULL; int bestsz = 0;

    for (int r0 = 0; r0 < R; r0++) {
        for (int c0 = 0; c0 < C; c0++) {
            int idx0 = r0*C + c0;
            if (seen[idx0]) continue;
            if (g->blocked[r0][c0]) { seen[idx0] = 1; continue; }
            int qh = 0, qt = 0;
            qr[qt] = r0; qc[qt] = c0; qt++;
            seen[idx0] = 1;
            Coord *tmp = (Coord*)malloc(sizeof(Coord));
            int cap = 1, sz = 0;
            while (qh < qt) {
                int r = qr[qh], c = qc[qh]; qh++;
                if (sz >= cap) { cap *= 2; tmp = (Coord*)realloc(tmp, cap * sizeof(Coord)); if (!tmp){fprintf(stderr,"alloc\n");exit(1);} }
                tmp[sz++] = (Coord){r,c};
                int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
                for (int d = 0; d < 4; d++) {
                    int nr = r + dr[d], nc = c + dc[d];
                    if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
                    int idx = nr*C + nc;
                    if (seen[idx]) continue;
                    if (g->blocked[nr][nc]) { seen[idx] = 1; continue; }
                    seen[idx] = 1;
                    qr[qt] = nr; qc[qt] = nc; qt++;
                }
            }
            if (sz > bestsz) { if (best) free(best); best = tmp; bestsz = sz; } else free(tmp);
        }
    }
    free(qr); free(qc); free(seen);
    *out_count = bestsz;
    return best;
}

/* ---------- utility BFS from a source, returns dist array (malloc) and parent array (malloc).
   dist: INT_MAX for unreachable. parent: linear index of parent or -1.
   Caller must free both arrays.
*/
void bfs_grid(const Grid *g, int sr, int sc, int **out_dist, int **out_parent) {
    int R = g->rows, C = g->cols, total = R*C;
    int *dist = (int*)malloc(total * sizeof(int));
    int *parent = (int*)malloc(total * sizeof(int));
    if (!dist || !parent) { fprintf(stderr, "alloc failed\n"); exit(1); }
    for (int i = 0; i < total; i++) { dist[i] = INT_MAX; parent[i] = -1; }

    int *qr = (int*)malloc((size_t)total * sizeof(int));
    int *qc = (int*)malloc((size_t)total * sizeof(int));
    if (!qr || !qc) { fprintf(stderr, "alloc failed\n"); exit(1); }

    int qh = 0, qt = 0;
    dist[sr*C + sc] = 0;
    qr[qt] = sr; qc[qt] = sc; qt++;
    while (qh < qt) {
        int r = qr[qh], c = qc[qh]; qh++;
        int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
        for (int d = 0; d < 4; d++) {
            int nr = r + dr[d], nc = c + dc[d];
            if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
            if (g->blocked[nr][nc]) continue;
            int idx = nr*C + nc;
            if (dist[idx] == INT_MAX) {
                dist[idx] = dist[r*C + c] + 1;
                parent[idx] = r*C + c;
                qr[qt] = nr; qc[qt] = nc; qt++;
            }
        }
    }
    free(qr); free(qc);
    *out_dist = dist; *out_parent = parent;
}

/* ---------- exact solver for small components (EXACT_LIMIT) ----------
   - build pairwise distances between component nodes with BFS
   - DP over subsets: dp[mask][v] = min cost to visit mask and end at v
   - reconstruct node order then expand to full grid path using parents
*/
static int popcount_int(unsigned x) {
    #if defined(__GNUC__) || defined(__clang__)
        return __builtin_popcount(x);
    #else
        int c=0; while(x){c+=x&1; x>>=1;} return c;
    #endif
}

void run_exact(Grid *g, Coord *nodes, int n, int K) {
    int R = g->rows, C = g->cols, total = R*C;
    // BFS from each node to get distances and parents
    int **dists = (int**)malloc(n * sizeof(int*));
    int **parents = (int**)malloc(n * sizeof(int*));
    for (int i = 0; i < n; i++) bfs_grid(g, nodes[i].r, nodes[i].c, &dists[i], &parents[i]);

    // matrix of pairwise distances
    int INF = INT_MAX/4;
    int (*D)[EXACT_LIMIT] = malloc(n * sizeof(*D));
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
        int d = dists[i][ nodes[j].r * C + nodes[j].c ];
        D[i][j] = (d == INT_MAX ? INF : d);
    }

    int full = 1 << n;
    int *dp = (int*)malloc(full * n * sizeof(int));
    int *from = (int*)malloc(full * n * sizeof(int));
    if (!dp || !from) { fprintf(stderr, "alloc failed\n"); exit(1); }
    for (int m = 0; m < full; m++) for (int v = 0; v < n; v++) { dp[m*n + v] = INF; from[m*n + v] = -1; }

    for (int i = 0; i < n; i++) dp[(1<<i)*n + i] = 0;
    for (int mask = 1; mask < full; mask++) {
        for (int v = 0; v < n; v++) {
            if (!(mask & (1<<v))) continue;
            int cur = dp[mask*n + v];
            if (cur >= INF) continue;
            for (int u = 0; u < n; u++) if (!(mask & (1<<u))) {
                int w = D[v][u];
                if (w >= INF) continue;
                int nm = mask | (1<<u);
                int cand = cur + w;
                if (cand < dp[nm*n + u]) { dp[nm*n + u] = cand; from[nm*n + u] = v; }
            }
        }
    }

    // choose best mask with max popcount and cost <= K
    int best_mask = 0, best_end = -1, best_cnt = 0;
    for (int mask = 1; mask < full; mask++) {
        int pc = popcount_int((unsigned)mask);
        if (pc < best_cnt) continue;
        int mincost = INF, arg = -1;
        for (int v = 0; v < n; v++) if (mask & (1<<v)) {
            if (dp[mask*n + v] < mincost) { mincost = dp[mask*n + v]; arg = v; }
        }
        if (mincost <= K) {
            if (pc > best_cnt) { best_cnt = pc; best_mask = mask; best_end = arg; }
        }
    }

    if (best_cnt == 0) {
        // at least starting at some node uses 0 moves and visits 1 unique node
        // pick any reachable node
        for (int i = 0; i < n; i++) {
            printf("Path: (%d,%d)\nUnique squares visited: 1\n", nodes[i].r, nodes[i].c);
            // cleanup
            for (int i2 = 0; i2 < n; i2++) { free(dists[i2]); free(parents[i2]); }
            free(dists); free(parents); free(D); free(dp); free(from);
            return;
        }
    }

    // reconstruct node sequence
    int seqlen = best_cnt;
    int *seq = (int*)malloc(seqlen * sizeof(int));
    int mask = best_mask, v = best_end;
    for (int i = seqlen - 1; i >= 0; i--) {
        seq[i] = v;
        int pv = from[mask*n + v];
        mask ^= (1<<v);
        v = pv;
        if (v == -1 && i > 0) {
            // find starter in mask with dp==0
            for (int x = 0; x < n; x++) if (mask & (1<<x)) if (dp[mask*n + x] == 0) { v = x; break; }
        }
    }

    // expand node-sequence into full grid path using parents (BFS parents from each node)
    // collect coords dynamically
    int cap = 128; Coord *out = (Coord*)malloc(cap * sizeof(Coord)); int outsz = 0;
    // start at first node
    out[outsz++] = nodes[seq[0]];
    for (int i = 1; i < seqlen; i++) {
        int a = seq[i-1], b = seq[i];
        int *parent = parents[a]; // parents from BFS rooted at nodes[a]
        int cur = nodes[b].r * C + nodes[b].c;
        // reconstruct reversed chain from b to a
        int revcap = D[a][b] + 1;
        if (revcap <= 0) revcap = 1;
        Coord *rev = (Coord*)malloc(revcap * sizeof(Coord));
        int rsz = 0;
        while (true) {
            int rr = cur / C, cc = cur % C;
            rev[rsz++] = (Coord){rr, cc};
            if (cur == nodes[a].r * C + nodes[a].c) break;
            int p = parent[cur];
            if (p == -1) break; // shouldn't happen
            cur = p;
        }
        // append reversed (excluding first because it's already last in out)
        for (int j = rsz - 2; j >= 0; j--) {
            if (outsz >= cap) { cap *= 2; out = (Coord*)realloc(out, cap * sizeof(Coord)); if (!out){fprintf(stderr,"alloc\n");exit(1);} }
            out[outsz++] = rev[j];
        }
        free(rev);
    }

    // compute unique count from out (safe)
    int unique = 0;
    unsigned char *seen = (unsigned char*)calloc(total, 1);
    for (int i = 0; i < outsz; i++) {
        int idx = out[i].r * C + out[i].c;
        if (!seen[idx]) { seen[idx] = 1; unique++; }
    }
    // print
    printf("Path:");
    for (int i = 0; i < outsz; i++) printf(" (%d,%d)", out[i].r, out[i].c);
    printf("\nUnique squares visited: %d\n", unique);
    free(seen); free(out); free(seq);

    // cleanup
    for (int i = 0; i < n; i++) { free(dists[i]); free(parents[i]); }
    free(dists); free(parents); free(D); free(dp); free(from);
}

/* ---------- greedy + random-restarts solver ---------- */
/* Single greedy run:
   - start position chosen randomly among component nodes
   - prefer adjacent unvisited; if none, BFS to nearest unvisited (bounded by remaining moves)
   - mark all visited along path; stop when no reachable unvisited or K exhausted
*/
int bfs_find_nearest(const Grid *g, int sr, int sc, unsigned char *visited_flag, int R, int C,
                     int *out_path_r, int *out_path_c, int max_path_len, int max_depth) {
    // BFS to find nearest cell that is free and unvisited_flag==0
    int total = R * C;
    int *qr = (int*)malloc(total * sizeof(int));
    int *qc = (int*)malloc(total * sizeof(int));
    int *parent = (int*)malloc(total * sizeof(int));
    for (int i = 0; i < total; i++) parent[i] = -1;
    int qh = 0, qt = 0;
    qr[qt] = sr; qc[qt] = sc; qt++;
    int start_idx = sr*C + sc;
    unsigned char *seen = (unsigned char*)calloc(total, 1);
    seen[start_idx] = 1;
    while (qh < qt) {
        int r = qr[qh], c = qc[qh]; qh++;
        int idx = r*C + c;
        // check if this cell is unvisited (and free)
        if (!visited_flag[idx] && !g->blocked[r][c]) {
            // reconstruct path from sr,sc to r,c
            int path[1024]; int psz = 0;
            int cur = idx;
            while (cur != -1 && psz < max_path_len) { path[psz++] = cur; cur = parent[cur]; }
            // reverse and output
            int outsz = 0;
            for (int i = psz - 1; i >= 0; i--) {
                out_path_r[outsz] = path[i] / C; out_path_c[outsz] = path[i] % C; outsz++;
                if (outsz >= max_path_len) break;
            }
            free(qr); free(qc); free(parent); free(seen);
            return outsz;
        }
        if (max_depth >= 0 && parent[idx] != -1) { // estimate depth via parent chain
            int depth = 0; int cur = idx;
            while (parent[cur] != -1) { depth++; cur = parent[cur]; if (depth > max_depth) break; }
            if (depth > max_depth) continue;
        }
        int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
        for (int d = 0; d < 4; d++) {
            int nr = r + dr[d], nc = c + dc[d];
            if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
            if (g->blocked[nr][nc]) continue;
            int nidx = nr*C + nc;
            if (seen[nidx]) continue;
            seen[nidx] = 1;
            parent[nidx] = idx;
            qr[qt] = nr; qc[qt] = nc; qt++;
        }
    }
    free(qr); free(qc); free(parent); free(seen);
    return 0; // not found
}

void run_greedy_random(Grid *g, Coord *nodes, int n, int K, int tries) {
    int R = g->rows, C = g->cols, total = R*C;
    int best_unique = 0;
    int *best_path_r = NULL, *best_path_c = NULL, best_len = 0;

    // Pre-allocate buffers used per run
    int *path_r = (int*)malloc((K+1) * sizeof(int));
    int *path_c = (int*)malloc((K+1) * sizeof(int));
    int *tmp_r = (int*)malloc((K+1) * sizeof(int));
    int *tmp_c = (int*)malloc((K+1) * sizeof(int));
    unsigned char *visited_flag = (unsigned char*)malloc((size_t)total);
    if (!path_r || !path_c || !tmp_r || !tmp_c || !visited_flag) { fprintf(stderr,"alloc\n"); exit(1); }

    for (int t = 0; t < tries; t++) {
        // pick random start among nodes
        int s = rand() % n;
        int cr = nodes[s].r, cc = nodes[s].c;
        memset(visited_flag, 0, (size_t)total);
        int len = 0;
        path_r[len] = cr; path_c[len] = cc; len++;
        visited_flag[cr*C + cc] = 1;
        int unique = 1;
        for (int step = 0; step < K; step++) {
            // prefer adjacent unvisited
            bool moved = false;
            int dirs[4] = {0,1,2,3};
            // shuffle small array (Fisher-Yates)
            for (int i = 3; i > 0; i--) { int j = rand() % (i+1); int tmp = dirs[i]; dirs[i] = dirs[j]; dirs[j] = tmp; }
            for (int di = 0; di < 4; di++) {
                int d = dirs[di];
                int dr = (d==0?-1:(d==2?1:0)), dc = (d==1?1:(d==3?-1:0));
                int nr = cr + dr, nc = cc + dc;
                if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
                if (g->blocked[nr][nc]) continue;
                if (!visited_flag[nr*C + nc]) {
                    cr = nr; cc = nc;
                    path_r[len] = cr; path_c[len] = cc; len++;
                    visited_flag[cr*C + cc] = 1; unique++;
                    moved = true; break;
                }
            }
            if (moved) continue;
            // otherwise BFS to nearest unvisited (bounded by remaining steps)
            int remaining = K - step;
            int outsz = bfs_find_nearest(g, cr, cc, visited_flag, R, C, tmp_r, tmp_c, remaining+1, remaining);
            if (outsz <= 1) break; // no reachable unvisited (outsz==1 means only current cell)
            // follow path (skip tmp[0] = current)
            for (int i = 1; i < outsz && step < K; i++, step++) {
                cr = tmp_r[i]; cc = tmp_c[i];
                path_r[len] = cr; path_c[len] = cc; len++;
                if (!visited_flag[cr*C + cc]) { visited_flag[cr*C + cc] = 1; unique++; }
            }
            // step loop increments extra; adjust step variable to correct position
            // because outer loop will increment step again, subtract 1
            step--;
        }

        if (unique > best_unique) {
            // save
            if (best_path_r) free(best_path_r), free(best_path_c);
            best_unique = unique;
            best_len = len;
            best_path_r = (int*)malloc(len * sizeof(int));
            best_path_c = (int*)malloc(len * sizeof(int));
            for (int i = 0; i < len; i++) { best_path_r[i] = path_r[i]; best_path_c[i] = path_c[i]; }
        }
    }

    if (best_len == 0) {
        printf("Path: (none)\nUnique squares visited: 0\n");
    } else {
        printf("Path:");
        for (int i = 0; i < best_len; i++) printf(" (%d,%d)", best_path_r[i], best_path_c[i]);
        printf("\nUnique squares visited: %d\n", best_unique);
    }

    free(path_r); free(path_c); free(tmp_r); free(tmp_c); free(visited_flag);
    if (best_path_r) { free(best_path_r); free(best_path_c); }
}

/* ---------- top-level solver ---------- */
void solve_path(Grid *g, int K) {
    if (!g) return;
    int comp_size = 0;
    Coord *nodes = find_largest_component(g, &comp_size);
    if (!nodes || comp_size == 0) {
        printf("Path: (none)\nUnique squares visited: 0\n");
        if (nodes) free(nodes);
        return;
    }
    if (comp_size <= EXACT_LIMIT) {
        run_exact(g, nodes, comp_size, K);
        free(nodes);
    } else {
        run_greedy_random(g, nodes, comp_size, K, GREEDY_TRIES);
        free(nodes);
    }
}

/* ---------- original tests (kept) ---------- */
int main(void) {
    srand((unsigned)time(NULL)); // seed RNG

    // Test 1: Tiny 1x1, no blocks
    {
        Grid *g = create_grid(1, 1, 0, NULL);
        printf("Test 1 (1x1, no blocks):\n");
        print_grid(g);
        solve_path(g, 1);
        free_grid(g);
        printf("\n");
    }

    // Test 2: All blocked 2x2
    {
        int blocked2[][2] = {{0,0},{0,1},{1,0},{1,1}};
        Grid *g = create_grid(2, 2, 4, blocked2);
        printf("Test 2 (2x2, all blocked):\n");
        print_grid(g);
        solve_path(g, 10);
        free_grid(g);
        printf("\n");
    }

    // Test 3: Corridor 1x5
    {
        Grid *g = create_grid(1, 5, 0, NULL);
        printf("Test 3 (1x5 corridor):\n");
        print_grid(g);
        solve_path(g, 10);
        free_grid(g);
        printf("\n");
    }

    // Test 4: 5x5 no blocks
    {
        Grid *g = create_grid(5, 5, 0, NULL);
        printf("Test 4 (5x5, no blocks):\n");
        print_grid(g);
        solve_path(g, 30);
        free_grid(g);
        printf("\n");
    }

    // Test 5: 10x12 with 20 random blocked cells
    {
        Grid *g = create_grid(10, 12, 0, NULL);
        generate_blocked(g, 20);
        printf("Test 5 (10x12, 20 random blocks):\n");
        print_grid(g);
        solve_path(g, 100);
        free_grid(g);
        printf("\n");
    }

    return 0;
}
