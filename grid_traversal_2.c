// main.c
// Portable C99 - grid with generate_blocked integrated (works with bool **blocked)

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <string.h>

// Grid struct: rows, cols, and blocked[row][col] boolean (true = blocked)
typedef struct {
    int rows, cols;
    bool **blocked;
} Grid;

/* Create a new grid of size rows x cols.
 * blocked_list may be NULL when blocked_count == 0.
 * blocked_list entries are assumed 0-based (row, col).
 */
Grid *create_grid(int rows, int cols, int blocked_count, const int blocked_list[][2]) {
    if (rows <= 0 || cols <= 0) return NULL;
    Grid *g = (Grid*)malloc(sizeof(Grid));
    if (!g) { fprintf(stderr, "alloc grid failed\n"); exit(1); }
    g->rows = rows;
    g->cols = cols;
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

// Print grid: '.' free, '#' blocked
void print_grid(const Grid *g) {
    if (!g) return;
    for (int r = 0; r < g->rows; r++) {
        for (int c = 0; c < g->cols; c++) putchar(g->blocked[r][c] ? '#' : '.');
        putchar('\n');
    }
}

// Robust random-block generator that matches Grid struct (bool **blocked).
// If num_blocked > available free cells, it blocks all available.
void generate_blocked(Grid *g, int num_blocked) {
    if (!g || num_blocked <= 0) return;
    long long rows = g->rows;
    long long cols = g->cols;
    long long total = rows * cols;

    // Count already blocked
    long long already = 0;
    for (int r = 0; r < g->rows; r++) {
        for (int c = 0; c < g->cols; c++) if (g->blocked[r][c]) already++;
    }
    long long available = total - already;
    if (available <= 0) return;
    if (num_blocked > available) num_blocked = (int)available;
    if (num_blocked == 0) return;

    // Strategy: if we need to block a large portion or available is small, build free-list and sample exactly.
    // Otherwise use rejection sampling (fast for sparse blocking).
    if (available <= 2000000 || num_blocked * 4 > available) {
        // Build an array of free cell linear indices (size = available)
        int *free_idx = (int*)malloc((size_t)available * sizeof(int));
        if (!free_idx) {
            // fallback to rejection sampling if malloc fails
            goto rejection;
        }
        int pos = 0;
        for (int r = 0; r < g->rows; r++) {
            for (int c = 0; c < g->cols; c++) {
                if (!g->blocked[r][c]) {
                    free_idx[pos++] = r * g->cols + c;
                }
            }
        }
        // Partial Fisher-Yates: select first num_blocked elements by swapping
        for (int i = 0; i < num_blocked; i++) {
            int j = i + rand() % (pos - i); // random in [i, pos-1]
            int tmp = free_idx[i]; free_idx[i] = free_idx[j]; free_idx[j] = tmp;
        }
        // Mark selected as blocked
        for (int i = 0; i < num_blocked; i++) {
            int idx = free_idx[i];
            int rr = idx / g->cols;
            int cc = idx % g->cols;
            g->blocked[rr][cc] = true;
        }
        free(free_idx);
        return;
    }

rejection:
    // Rejection sampling (good when num_blocked << available)
    int placed = 0;
    int attempts = 0;
    int max_attempts = num_blocked * 30 + 1000; // safety limit
    while (placed < num_blocked && attempts < max_attempts) {
        int r = rand() % g->rows;
        int c = rand() % g->cols;
        if (!g->blocked[r][c]) { g->blocked[r][c] = true; placed++; }
        attempts++;
    }
    if (placed >= num_blocked) return;

    // If we didn't place enough due to improbable collisions, finish by scanning free cells
    for (int r = 0; r < g->rows && placed < num_blocked; r++) {
        for (int c = 0; c < g->cols && placed < num_blocked; c++) {
            if (!g->blocked[r][c]) { g->blocked[r][c] = true; placed++; }
        }
    }
}

// Solve path (greedy) — moves up to movement_points and tries to maximize unique visited cells.
// This is the same solver previously used; it prints the path then the unique count.
void solve_path(Grid *g, int movement_points) {
    if (!g) return;
    int rows = g->rows, cols = g->cols;
    // Find any unblocked start
    int sr = -1, sc = -1;
    for (int r = 0; r < rows && sr < 0; r++) for (int c = 0; c < cols; c++)
        if (!g->blocked[r][c]) { sr = r; sc = c; break; }
    if (sr < 0) { printf("Path: (none)\nUnique squares visited: 0\n"); return; }

    // visited array
    bool **visited = (bool**)malloc((size_t)rows * sizeof(bool*));
    if (!visited) { fprintf(stderr, "alloc visited rows failed\n"); exit(1); }
    for (int r = 0; r < rows; r++) {
        visited[r] = (bool*)malloc((size_t)cols * sizeof(bool));
        if (!visited[r]) { fprintf(stderr, "alloc visited row failed\n"); exit(1); }
        for (int c = 0; c < cols; c++) visited[r][c] = false;
    }

    int max_path_len = movement_points + 1;
    int *path_r = (int*)malloc((size_t)max_path_len * sizeof(int));
    int *path_c = (int*)malloc((size_t)max_path_len * sizeof(int));
    if (!path_r || !path_c) { fprintf(stderr, "alloc path arrays failed\n"); exit(1); }

    int cr = sr, cc = sc;
    visited[cr][cc] = true;
    path_r[0] = cr; path_c[0] = cc;
    int pathLen = 1;
    int unique_count = 1;

    int dr[4] = {-1,0,1,0};
    int dc[4] = {0,1,0,-1};

    for (int step = 0; step < movement_points; step++) {
        bool moved = false;
        // prefer unvisited neighbors
        for (int d = 0; d < 4; d++) {
            int nr = cr + dr[d], nc = cc + dc[d];
            if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) {
                if (!g->blocked[nr][nc] && !visited[nr][nc]) {
                    cr = nr; cc = nc;
                    visited[cr][cc] = true;
                    path_r[pathLen] = cr; path_c[pathLen] = cc; pathLen++;
                    unique_count++;
                    moved = true;
                    break;
                }
            }
        }
        if (moved) continue;
        // else try to move to a visited neighbor that has an unvisited neighbor (backtrack towards unexplored)
        for (int d = 0; d < 4 && !moved; d++) {
            int nr = cr + dr[d], nc = cc + dc[d];
            if (nr >= 0 && nr < rows && nc >= 0 && nc < cols) {
                if (!g->blocked[nr][nc] && visited[nr][nc]) {
                    for (int d2 = 0; d2 < 4; d2++) {
                        int r2 = nr + dr[d2], c2 = nc + dc[d2];
                        if (r2 >= 0 && r2 < rows && c2 >= 0 && c2 < cols) {
                            if (!g->blocked[r2][c2] && !visited[r2][c2]) {
                                cr = nr; cc = nc;
                                path_r[pathLen] = cr; path_c[pathLen] = cc; pathLen++;
                                moved = true;
                                break;
                            }
                        }
                    }
                }
            }
        }
        if (!moved) break; // no productive move
    }

    // Print result
    printf("Path:");
    for (int i = 0; i < pathLen; i++) printf(" (%d,%d)", path_r[i], path_c[i]);
    printf("\nUnique squares visited: %d\n", unique_count);

    // cleanup
    for (int r = 0; r < rows; r++) free(visited[r]);
    free(visited);
    free(path_r);
    free(path_c);
}

int main(void) {
    srand((unsigned)time(NULL)); // seed RNG once

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
