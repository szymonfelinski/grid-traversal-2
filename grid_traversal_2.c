#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>

#define GREEDY_TRIES 1

typedef struct { int rows, cols; bool **blocked; } Grid;
typedef struct { int r, c; } Coord;

static Grid *grid_create(int rows, int cols, int blocked_count, const int blocked_list[][2]) {
    if (rows <= 0 || cols <= 0) return NULL;
    Grid *g = malloc(sizeof(Grid));
    if (!g) { perror("malloc"); exit(1); }
    g->rows = rows; g->cols = cols;
    g->blocked = malloc(rows * sizeof(bool*));
    if (!g->blocked) { perror("malloc"); exit(1); }
    for (int r = 0; r < rows; ++r) {
        g->blocked[r] = malloc(cols * sizeof(bool));
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

static void grid_generate_blocked(Grid *g, int num_blocked) {
    if (!g || num_blocked <= 0) return;
    int R = g->rows, C = g->cols;
    long long available = 0;
    for (int r = 0; r < R; ++r)
        for (int c = 0; c < C; ++c)
            if (!g->blocked[r][c]) ++available;
    if (available <= 0) return;
    if (num_blocked >= (int)available) {
        for (int r = 0; r < R; ++r)
            for (int c = 0; c < C; ++c)
                if (!g->blocked[r][c]) g->blocked[r][c] = true;
        return;
    }
    int *free_idx = malloc(available * sizeof(int));
    if (!free_idx) {
        int placed = 0;
        for (int r = 0; r < R && placed < num_blocked; ++r)
            for (int c = 0; c < C && placed < num_blocked; ++c)
                if (!g->blocked[r][c]) { g->blocked[r][c] = true; ++placed; }
        return;
    }
    int pos = 0;
    for (int r = 0; r < R; ++r)
        for (int c = 0; c < C; ++c)
            if (!g->blocked[r][c]) free_idx[pos++] = r * C + c;
    for (int i = 0; i < num_blocked; ++i) {
        int j = i + rand() % (pos - i);
        int tmp = free_idx[i]; free_idx[i] = free_idx[j]; free_idx[j] = tmp;
    }
    for (int i = 0; i < num_blocked; ++i) {
        int idx = free_idx[i];
        int rr = idx / C, cc = idx % C;
        g->blocked[rr][cc] = true;
    }
    free(free_idx);
}

static Coord *collect_free_cells(const Grid *g, int *out_count) {
    int R = g->rows, C = g->cols, count = 0;
    for (int r = 0; r < R; ++r)
        for (int c = 0; c < C; ++c)
            if (!g->blocked[r][c]) ++count;
    if (count == 0) { *out_count = 0; return NULL; }
    Coord *arr = malloc(count * sizeof(Coord));
    if (!arr) { perror("malloc"); exit(1); }
    int pos = 0;
    for (int r = 0; r < R; ++r)
        for (int c = 0; c < C; ++c)
            if (!g->blocked[r][c]) { arr[pos].r = r; arr[pos].c = c; ++pos; }
    *out_count = count;
    return arr;
}

static inline bool has_unvisited_neighbor(const Grid *g, int r, int c, int R, int C, int *visited_epoch, int run_token) {
    const int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
    for (int d = 0; d < 4; ++d) {
        int nr = r + dr[d], nc = c + dc[d];
        if ((unsigned)nr >= (unsigned)R || (unsigned)nc >= (unsigned)C) continue;
        if (g->blocked[nr][nc]) continue;
        if (visited_epoch[nr * C + nc] != run_token) return true;
    }
    return false;
}

static int bfs_to_nearest_opt(const Grid *g,
                              int sr, int sc,
                              int *queue_r, int *queue_c, int *parent,
                              int *seen_epoch, int seen_token,
                              int *visited_epoch, int run_token,
                              int *out_r, int *out_c, int max_len)
{
    int R = g->rows, C = g->cols, total = R * C;
    int qh = 0, qt = 0;
    queue_r[qt] = sr; queue_c[qt] = sc; ++qt;
    seen_epoch[sr * C + sc] = seen_token;
    parent[sr * C + sc] = -1;

    while (qh < qt) {
        int r = queue_r[qh], c = queue_c[qh]; ++qh;
        int idx = r * C + c;
        if (visited_epoch[idx] != run_token && !g->blocked[r][c]) {
            int path[1024], psz = 0, cur = idx;
            while (cur != -1 && psz < max_len) { path[psz++] = cur; cur = parent[cur]; }
            int outsz = 0;
            for (int i = psz - 1; i >= 0 && outsz < max_len; --i) {
                out_r[outsz] = path[i] / C;
                out_c[outsz] = path[i] % C;
                ++outsz;
            }
            return outsz;
        }
        const int dr[4] = {-1,0,1,0}, dc[4] = {0,1,0,-1};
        for (int d = 0; d < 4; ++d) {
            int nr = r + dr[d], nc = c + dc[d];
            if (nr < 0 || nr >= R || nc < 0 || nc >= C) continue;
            if (g->blocked[nr][nc]) continue;
            int nidx = nr * C + nc;
            if (seen_epoch[nidx] == seen_token) continue;
            seen_epoch[nidx] = seen_token;
            parent[nidx] = idx;
            queue_r[qt] = nr; queue_c[qt] = nc; ++qt;
        }
    }
    return 0;
}

static void greedy_random(Grid *g, Coord *nodes, int n, int K, int tries) {
    if (n <= 0) { printf("Path: (none)\nUnique squares visited: 0\n"); return; }
    int R = g->rows, C = g->cols, total = R * C;
    int best_unique = 0;
    int *best_pr = NULL, *best_pc = NULL, best_len = 0;
    int *pr = malloc((K + 1) * sizeof(int));
    int *pc = malloc((K + 1) * sizeof(int));
    int *tmp_r = malloc((K + 1) * sizeof(int));
    int *tmp_c = malloc((K + 1) * sizeof(int));
    int *queue_r = malloc(total * sizeof(int));
    int *queue_c = malloc(total * sizeof(int));
    int *parent = malloc(total * sizeof(int));
    int *seen_epoch = calloc(total, sizeof(int));
    int *visited_epoch = calloc(total, sizeof(int));
    if (!pr || !pc || !tmp_r || !tmp_c || !queue_r || !queue_c || !parent || !seen_epoch || !visited_epoch) {
        perror("malloc"); exit(1);
    }
    int run_token = 1, seen_token_base = 1000000;
    for (int t = 0; t < tries; ++t) {
        int s = rand() % n;
        int cr = nodes[s].r, cc = nodes[s].c;
        ++run_token;
        if (run_token == 0) { memset(visited_epoch, 0, total * sizeof(int)); run_token = 1; }
        int len = 0;
        pr[len] = cr; pc[len] = cc; ++len;
        visited_epoch[cr * C + cc] = run_token;
        int unique = 1, rem = K;
        while (rem > 0) {
            bool moved = false;
            int dirs[4] = {0,1,2,3};
            for (int i = 3; i > 0; --i) { int j = rand() % (i+1); int tmp = dirs[i]; dirs[i] = dirs[j]; dirs[j] = tmp; }
            for (int di = 0; di < 4; ++di) {
                int d = dirs[di];
                int dr = (d==0?-1:(d==2?1:0)), dc = (d==1?1:(d==3?-1:0));
                int nr = cr + dr, nc = cc + dc;
                if ((unsigned)nr >= (unsigned)R || (unsigned)nc >= (unsigned)C) continue;
                if (g->blocked[nr][nc]) continue;
                int nidx = nr * C + nc;
                if (visited_epoch[nidx] != run_token) {
                    cr = nr; cc = nc;
                    pr[len] = cr; pc[len] = cc; ++len;
                    visited_epoch[nidx] = run_token; ++unique;
                    --rem;
                    moved = true;
                    break;
                }
            }
            if (moved) continue;
            int seen_token = ++seen_token_base;
            int outsz = bfs_to_nearest_opt(g, cr, cc, queue_r, queue_c, parent, seen_epoch, seen_token,
                                           visited_epoch, run_token, tmp_r, tmp_c, rem + 1);
            if (outsz <= 1) break;
            for (int i = 1; i < outsz && rem > 0; ++i, --rem) {
                cr = tmp_r[i]; cc = tmp_c[i];
                pr[len] = cr; pc[len] = cc; ++len;
                int idx = cr * C + cc;
                if (visited_epoch[idx] != run_token) {
                    visited_epoch[idx] = run_token; ++unique;
                }
            }
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
    free(pr); free(pc); free(tmp_r); free(tmp_c);
    free(queue_r); free(queue_c); free(parent); free(seen_epoch); free(visited_epoch);
}

static void solve_path(Grid *g, int K) {
    if (!g) return;
    int free_count = 0;
    Coord *nodes = collect_free_cells(g, &free_count);
    if (!nodes || free_count == 0) {
        if (nodes) free(nodes);
        printf("Path: (none)\nUnique squares visited: 0\n");
        return;
    }
    greedy_random(g, nodes, free_count, K, GREEDY_TRIES);
    free(nodes);
}

int main(void) {
    srand((unsigned)time(NULL));
    {
        Grid *g = grid_create(1, 1, 0, NULL);
        printf("Test 1 (1x1):\n");
        grid_print(g);
        solve_path(g, 1);
        grid_free(g);
        printf("\n");
    }
    {
        int blocked2[][2] = {{0,0},{0,1},{1,0},{1,1}};
        Grid *g = grid_create(2, 2, 4, blocked2);
        printf("Test 2 (2x2 all blocked):\n");
        grid_print(g);
        solve_path(g, 10);
        grid_free(g);
        printf("\n");
    }
    {
        Grid *g = grid_create(1, 5, 0, NULL);
        printf("Test 3 (1x5 corridor):\n");
        grid_print(g);
        solve_path(g, 10);
        grid_free(g);
        printf("\n");
    }
    {
        Grid *g = grid_create(5, 5, 0, NULL);
        printf("Test 4 (5x5 no blocks):\n");
        grid_print(g);
        solve_path(g, 30);
        grid_free(g);
        printf("\n");
    }
    {
        Grid *g = grid_create(100000, 10000, 0, NULL);
        grid_generate_blocked(g, 10000000);
        printf("Test 5 (100000x10000, 1,000,000 random blocks):\n");
        solve_path(g, 400000);
        grid_free(g);
        printf("\n");
    }
    return 0;
}
