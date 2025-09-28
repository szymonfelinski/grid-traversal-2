// main.c
// Portable C99
// Single-approach solver: randomized greedy with BFS-to-nearest fallback
// Clear, small helper functions. Tests included at the bottom.

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <limits.h>

#define GREEDY_TRIES 150

typedef struct { int rows, cols; bool **blocked; } Grid;
typedef struct { int r, c; } Coord;

/* --- grid management --- */

static Grid *grid_create(int rows, int cols, int blocked_count, const int blocked_list[][2]) {
    if (rows <= 0 || cols <= 0) return NULL;
    Grid *g = malloc(sizeof(Grid));
    if (!g) { perror("malloc"); exit(1); }
    g->rows = rows; g->cols = cols;
    g->blocked = malloc((size_t)rows * sizeof(bool*));
    if (!g->blocked) { perror("malloc"); exit(1); }
    for (int r = 0; r < rows; ++r) {
        g->blocked[r] = malloc((size_t)cols * sizeof(bool));
        if (!g->blocked[r]) { perror("malloc"); exit(1); }
        for (int c = 0; c < cols; ++c) g->blocked[r][c] = false;
    }
    if (blocked_list && blocked_count > 0) {
        for (int i = 0; i < blocked_count; ++i) {
            int br = blocked_list[i][0], bc = blocked_list[i][1];
            if (br >= 0 && br < rows && bc >= 0 && bc < cols) g->blocked[br][bc] = true;
        }
    }
    return g;
}

static void grid_free(Grid *g) {
    if (!g) return;
    for (int r = 0; r < g->rows; ++r) free(g->blocked[r]);
    free(g->blocked);
    free(g);
}

static void grid_print(const Grid *g) {
    if (!g) return;
    for (int r = 0; r < g->rows; ++r) {
        for (int c = 0; c < g->cols; ++c) putchar(g->blocked[r][c] ? '#' : '.');
        putchar('\n');
    }
}

/* --- random blocked placement --- */

static void grid_generate_blocked(Grid *g, int num_blocked) {
    if (!g || num_blocked <= 0) return;
    long long rows = g->rows, cols = g->cols;
    long long total = rows * cols;
    long long already = 0;
    for (int r = 0; r < g->rows; ++r)
        for (int c = 0; c < g->cols; ++c)
            if (g->blocked[r][c]) ++already;
    long long available = total - already;
    if (available <= 0) return;
    if (num_blocked > available) num_blocked = (int)available;

    if (available <= 2000000 || num_blocked * 4 > available) {
        int *free_idx = malloc((size_t)available * sizeof(int));
        if (!free_idx) goto rejection;
        int pos = 0;
        for (int r = 0; r < g->rows; ++r)
            for (int c = 0; c < g->cols; ++c)
                if (!g->blocked[r][c]) free_idx[pos++] = r * g->cols + c;
        for (int i = 0; i < num_blocked; ++i) {
            int j = i + rand() % (pos - i);
            int tmp = free_idx[i]; free_idx[i] = free_idx[j]; free_idx[j] = tmp;
        }
        for (int i = 0; i < num_blocked; ++i) {
            int idx = free_idx[i];
            g->blocked[idx / g->cols][idx % g->cols] = true;
        }
        free(free_idx);
        return;
    }

rejection:
    {
        int placed = 0, attempts = 0;
        int max_attempts = num_blocked * 30 + 1000;
        while (placed < num_blocked && attempts < max_attempts) {
            int r = rand() % g->rows, c = rand() % g->cols;
            if (!g->blocked[r][c]) { g->blocked[r][c] = true; ++placed; }
            ++attempts;
        }
        if (placed >= num_blocked) return;
        for (int r = 0; r < g->rows && placed < num_blocked; ++r)
            for (int c = 0; c < g->cols && placed < num_blocked; ++c)
                if (!g->blocked[r][c]) { g->blocked[r][c] = true; ++placed; }
    }
}

/* --- largest connected component (BFS) --- */

static Coord *find_largest_component(const Grid *g, int *out_count) {
    *out_count = 0;
    int R = g->rows, C = g->cols;
    unsigned char *seen = calloc((size_t)R * C, 1);
    if (!seen) { perror("calloc"); exit(1); }

    int *qr = malloc((size_t)R * C * sizeof(int));
    int *qc = malloc((size_t)R * C * sizeof(int));
    if (!qr || !qc) { perror("malloc"); exit(1); }

    Coord *best = NULL; int bestsz = 0;

    for (int r0 = 0; r0 < R; ++r0) {
        for (int c0 = 0; c0 < C; ++c0) {
            int idx0 = r0 * C + c0;
            if (seen[idx0]) continue;
            if (g->blocked[r0][c0]) { seen[idx0] = 1; continue; }

            int qh = 0, qt = 0;
            qr[qt] = r0; qc[qt] = c0; ++qt;
            seen[idx0] = 1;

            Coord *tmp = malloc(sizeof(Coord));
            int cap = 1, sz = 0;

            while (qh < qt) {
                int r = qr[qh], c = qc[qh]; ++qh;
                if (sz >= cap) { cap *= 2; tmp = realloc(tmp, cap * sizeof(Coord)); if (!tmp) { perror("realloc"); exit(1); } }
                tmp[sz++] = (Coord){r,c};
                int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
                for (int d = 0; d < 4; ++d) {
                    int nr = r + dr[d], nc = c + dc[d];
                    if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
                    int nidx = nr * C + nc;
                    if (seen[nidx]) continue;
                    if (g->blocked[nr][nc]) { seen[nidx] = 1; continue; }
                    seen[nidx] = 1;
                    qr[qt] = nr; qc[qt] = nc; ++qt;
                }
            }

            if (sz > bestsz) { if (best) free(best); best = tmp; bestsz = sz; } else free(tmp);
        }
    }

    free(qr); free(qc); free(seen);
    *out_count = bestsz;
    return best;
}

/* --- BFS to nearest unvisited cell and return path (as sequence of coords) --- */

static int bfs_to_nearest(const Grid *g, int sr, int sc, unsigned char *visited_flag,
                          int *out_r, int *out_c, int max_len) {
    int R = g->rows, C = g->cols, total = R * C;
    int *qr = malloc(total * sizeof(int));
    int *qc = malloc(total * sizeof(int));
    int *parent = malloc(total * sizeof(int));
    if (!qr || !qc || !parent) { perror("malloc"); exit(1); }
    for (int i = 0; i < total; ++i) parent[i] = -1;
    unsigned char *seen = calloc((size_t)total, 1);
    if (!seen) { perror("calloc"); exit(1); }

    int qh = 0, qt = 0;
    qr[qt] = sr; qc[qt] = sc; ++qt;
    seen[sr * C + sc] = 1;

    while (qh < qt) {
        int r = qr[qh], c = qc[qh]; ++qh;
        int idx = r * C + c;
        if (!visited_flag[idx] && !g->blocked[r][c]) {
            int path[1024], psz = 0;
            int cur = idx;
            while (cur != -1 && psz < max_len) { path[psz++] = cur; cur = parent[cur]; }
            int outsz = 0;
            for (int i = psz - 1; i >= 0 && outsz < max_len; --i) {
                out_r[outsz] = path[i] / C; out_c[outsz] = path[i] % C; ++outsz;
            }
            free(qr); free(qc); free(parent); free(seen);
            return outsz;
        }
        int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
        for (int d = 0; d < 4; ++d) {
            int nr = r + dr[d], nc = c + dc[d];
            if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
            if (g->blocked[nr][nc]) continue;
            int nidx = nr * C + nc;
            if (seen[nidx]) continue;
            seen[nidx] = 1;
            parent[nidx] = idx;
            qr[qt] = nr; qc[qt] = nc; ++qt;
        }
    }

    free(qr); free(qc); free(parent); free(seen);
    return 0;
}

/* --- randomized greedy solver --- */

static void greedy_random(Grid *g, Coord *nodes, int n, int K, int tries) {
    int R = g->rows, C = g->cols, total = R * C;
    int best_unique = 0;
    int *best_pr = NULL, *best_pc = NULL, best_len = 0;

    int *pr = malloc((K + 1) * sizeof(int));
    int *pc = malloc((K + 1) * sizeof(int));
    int *tmp_r = malloc((K + 1) * sizeof(int));
    int *tmp_c = malloc((K + 1) * sizeof(int));
    unsigned char *visited_flag = malloc((size_t)total);
    if (!pr || !pc || !tmp_r || !tmp_c || !visited_flag) { perror("malloc"); exit(1); }

    for (int t = 0; t < tries; ++t) {
        int s = rand() % n;
        int cr = nodes[s].r, cc = nodes[s].c;
        memset(visited_flag, 0, (size_t)total);
        int len = 0;
        pr[len] = cr; pc[len] = cc; ++len;
        visited_flag[cr * C + cc] = 1;
        int unique = 1;

        for (int step = 0; step < K; ++step) {
            bool moved = false;
            int dirs[4] = {0,1,2,3};
            for (int i = 3; i > 0; --i) { int j = rand() % (i + 1); int tmp = dirs[i]; dirs[i] = dirs[j]; dirs[j] = tmp; }
            for (int di = 0; di < 4; ++di) {
                int d = dirs[di];
                int dr = (d==0?-1:(d==2?1:0)), dc = (d==1?1:(d==3?-1:0));
                int nr = cr + dr, nc = cc + dc;
                if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
                if (g->blocked[nr][nc]) continue;
                if (!visited_flag[nr * C + nc]) {
                    cr = nr; cc = nc;
                    pr[len] = cr; pc[len] = cc; ++len;
                    visited_flag[cr * C + cc] = 1; ++unique;
                    moved = true; break;
                }
            }
            if (moved) continue;

            int remaining = K - step;
            int outsz = bfs_to_nearest(g, cr, cc, visited_flag, tmp_r, tmp_c, remaining + 1);
            if (outsz <= 1) break;
            for (int i = 1; i < outsz && step < K; ++i, ++step) {
                cr = tmp_r[i]; cc = tmp_c[i];
                pr[len] = cr; pc[len] = cc; ++len;
                if (!visited_flag[cr * C + cc]) { visited_flag[cr * C + cc] = 1; ++unique; }
            }
            --step;
        }

        if (unique > best_unique) {
            if (best_pr) { free(best_pr); free(best_pc); }
            best_unique = unique;
            best_len = len;
            best_pr = malloc(len * sizeof(int));
            best_pc = malloc(len * sizeof(int));
            for (int i = 0; i < len; ++i) { best_pr[i] = pr[i]; best_pc[i] = pc[i]; }
        }
    }

    if (!best_pr) {
        printf("Path: (none)\nUnique squares visited: 0\n");
    } else {
        printf("Path:");
        for (int i = 0; i < best_len; ++i) printf(" (%d,%d)", best_pr[i], best_pc[i]);
        printf("\nUnique squares visited: %d\n", best_unique);
        free(best_pr); free(best_pc);
    }

    free(pr); free(pc); free(tmp_r); free(tmp_c); free(visited_flag);
}

/* --- top-level solve: use greedy_random only --- */

static void solve_path(Grid *g, int K) {
    if (!g) return;
    int comp_size = 0;
    Coord *nodes = find_largest_component(g, &comp_size);
    if (!nodes || comp_size == 0) {
        if (nodes) free(nodes);
        printf("Path: (none)\nUnique squares visited: 0\n");
        return;
    }

    greedy_random(g, nodes, comp_size, K, GREEDY_TRIES);
    free(nodes);
}

/* --- tests --- */

int main(void) {
    srand((unsigned)time(NULL));

    // Test 1: Tiny 1x1
    {
        Grid *g = grid_create(1, 1, 0, NULL);
        printf("Test 1 (1x1):\n");
        grid_print(g);
        solve_path(g, 1);
        grid_free(g);
        printf("\n");
    }

    // Test 2: All blocked 2x2
    {
        int blocked2[][2] = {{0,0},{0,1},{1,0},{1,1}};
        Grid *g = grid_create(2, 2, 4, blocked2);
        printf("Test 2 (2x2 all blocked):\n");
        grid_print(g);
        solve_path(g, 10);
        grid_free(g);
        printf("\n");
    }

    // Test 3: Corridor 1x5
    {
        Grid *g = grid_create(1, 5, 0, NULL);
        printf("Test 3 (1x5 corridor):\n");
        grid_print(g);
        solve_path(g, 10);
        grid_free(g);
        printf("\n");
    }

    // Test 4: 5x5 no blocks
    {
        Grid *g = grid_create(5, 5, 0, NULL);
        printf("Test 4 (5x5 no blocks):\n");
        grid_print(g);
        solve_path(g, 30);
        grid_free(g);
        printf("\n");
    }

    // Test 5: 10x12 with 20 random blocked cells
    {
        Grid *g = grid_create(10, 12, 0, NULL);
        grid_generate_blocked(g, 20);
        printf("Test 5 (10x12, 20 random blocks):\n");
        grid_print(g);
        solve_path(g, 100);
        grid_free(g);
        printf("\n");
    }

    return 0;
}
