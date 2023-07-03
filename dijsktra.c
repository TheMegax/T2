/////////////////////////////////////////////////////////////////////
// Carlos Hernandez
// All rights reserved
/////////////////////////////////////////////////////////////////////

//#include "heap.h"
#include "node.h"
#include "include.h"
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <unistd.h>


gnode* graph_node;
unsigned num_gnodes;
unsigned adjacent_table[MAXNODES][MAXNEIGH];
unsigned pred_adjacent_table[MAXNODES][MAXNEIGH];
unsigned goal, start;
gnode* start_state;
gnode* goal_state;

unsigned long long int stat_expansions = 0;
unsigned long long int stat_generated = 0;

void read_adjacent_table(const char* filename) {
	FILE* f;
	int i, ori, dest, dist, t;
	f = fopen(filename, "r");
	int num_arcs = 0;
	if (f == NULL) 	{
		printf("Cannot open file %s.\n", filename);
		exit(1);
	}
	fscanf(f, "%d %d", &num_gnodes, &num_arcs);
	fscanf(f, "\n");
	
	//printf("%d %d\n", num_gnodes, num_arcs);
	
	for (i = 0; i < num_gnodes; i++)
		adjacent_table[i][0] = 0;

	for (i = 0; i < num_arcs; i++) {
		fscanf(f, "%d %d %d %d\n", &ori, &dest, &dist, &t);
		adjacent_table[ori - 1][0]++;
		adjacent_table[ori - 1][adjacent_table[ori - 1][0] * 3 - 2] = dest - 1;
		adjacent_table[ori - 1][adjacent_table[ori - 1][0] * 3 - 1] = dist;
		adjacent_table[ori - 1][adjacent_table[ori - 1][0] * 3] = t;

		pred_adjacent_table[dest - 1][0]++;
		pred_adjacent_table[dest - 1][pred_adjacent_table[dest - 1][0] * 3 - 2] = ori - 1;
		pred_adjacent_table[dest - 1][pred_adjacent_table[dest - 1][0] * 3 - 1] = dist;
		pred_adjacent_table[dest - 1][pred_adjacent_table[dest - 1][0] * 3] = t;
		//printf("%d %d %d %d\n", ori, dest, dist, t);
	}
	fclose(f);
}

void new_graph() {
	int y;
	if (graph_node == NULL) {
		graph_node = (gnode*) calloc(num_gnodes, sizeof(gnode));
		for (y = 0; y < num_gnodes; ++y) 		{
			graph_node[y].id = y;
			graph_node[y].gmin = LARGE;
			graph_node[y].h1 = LARGE; // almacena la distancia minima desde star
			graph_node[y].h2 = LARGE;// almacena la tiempo minimo desde star
			graph_node[y].gopfirst = NULL;
		}
	}
}

// --------------------------    Binary Heap for Dijkstra  -----------------------------------------
#define HEAPSIZEDIJ 500000
gnode* heap_dij[HEAPSIZEDIJ];
unsigned long int heapsize_dij = 0;
unsigned long int stat_percolations = 0;

// ---------------------------------------------------------------
void percolatedown_dij(int hole, gnode* tmp) {
  int child;

  if (heapsize_dij != 0) {
    for (; 2 * hole <= heapsize_dij; hole = child) {
      child = 2 * hole;
      if (child != heapsize_dij && heap_dij[child + 1]->key < heap_dij[child]->key)
        ++child;
      if (heap_dij[child]->key < tmp->key) {
        heap_dij[hole] = heap_dij[child];
        heap_dij[hole]->heapindex = hole;
        ++stat_percolations;
      }
      else
        break;
    } // end for
    heap_dij[hole] = tmp;
    heap_dij[hole]->heapindex = hole;
  }
}
/* --------------------------------------------------------------- */
void percolateup_dij(int hole, gnode* tmp) {
  if (heapsize_dij != 0) {
    for (; hole > 1 && tmp->key < heap_dij[hole / 2]->key; hole /= 2) {
      heap_dij[hole] = heap_dij[hole / 2];
      heap_dij[hole]->heapindex = hole;
      ++stat_percolations;
    }
    heap_dij[hole] = tmp;
    heap_dij[hole]->heapindex = hole;
  }
}
/* --------------------------------------------------------------- */
void percolateupordown_dij(int hole, gnode* tmp) {
  if (heapsize_dij != 0) {
    if (hole > 1 && heap_dij[hole / 2]->key > tmp->key)
      percolateup_dij(hole, tmp);
    else
      percolatedown_dij(hole, tmp);
  }
}
/* --------------------------------------------------------------- */
void insertheap_dij(gnode* thiscell) {

  if (thiscell->heapindex == 0)
    percolateup_dij(++heapsize_dij, thiscell);
  else
    percolateupordown_dij(thiscell->heapindex, heap_dij[thiscell->heapindex]);
}
/* --------------------------------------------------------------- */
void deleteheap_dij(gnode* thiscell) {
  if (thiscell->heapindex != 0) {
    percolateupordown_dij(thiscell->heapindex, heap_dij[heapsize_dij--]);
    thiscell->heapindex = 0;
  }
}
/* --------------------------------------------------------------- */
gnode* topheap_dij() {
  if (heapsize_dij == 0)
    return NULL;
  return heap_dij[1];
}
/* --------------------------------------------------------------- */
void emptyheap_dij() {
  int i;

  for (i = 1; i <= heapsize_dij; ++i)
    heap_dij[i]->heapindex = 0;
  heapsize_dij = 0;
}

/* --------------------------------------------------------------- */
gnode* popheap_dij() {
  gnode* thiscell;

  if (heapsize_dij == 0)
    return NULL;
  thiscell = heap_dij[1];
  thiscell->heapindex = 0;
  percolatedown_dij(1, heap_dij[heapsize_dij--]);
  return thiscell;
}

int sizeheap_dij() {
  return heapsize_dij;
}

gnode* posheap_dij(int i) {
  return heap_dij[i];
}

// ---------------------------------------------------------------------------------------



void initialize_parameters() {
	start_state = &graph_node[start-1];
    goal_state = &graph_node[goal-1];
    stat_generated = 0;
    stat_expansions = 0;
    stat_percolations = 0;
}

int backward_dijkstra(int dim) {
	int i;
	for (i = 0; i < num_gnodes; ++i)
        graph_node[i].key = LARGE;
	emptyheap_dij();
	goal_state->key = 0;
    goal_state->parent = NULL;
	insertheap_dij(goal_state);
 	
    while (topheap_dij() != NULL) {
        gnode* n;
        gnode* pred;
        short d;
        n = popheap_dij();
        if (dim == 1)
            n->h1 = n->key;
        else
            n->h2 = n->key;
        if (n == start_state)
        	break;
        ++stat_expansions;
        for (d = 1; d < pred_adjacent_table[n->id][0] * 3; d += 3) {
            pred = &graph_node[pred_adjacent_table[n->id][d]];
            stat_generated++;
            int new_weight = n->key + pred_adjacent_table[n->id][d + dim];
            if (pred->key > new_weight) {
                pred->key = new_weight;
                pred->parent = n;
                insertheap_dij(pred);
            }
        }
    }
    return 1;
}

int random_ranged(int min, int max) {
    return (rand() % (max - min + 1)) + min;
}

void print_path() {
    gnode* n = start_state;
    while (n != NULL){
        printf("%lld",n->id+1);
        n = n->parent;
        if (n != NULL) {
            printf(",");
        }
    }
    printf("\n");
}

char* get_path() {
    gnode* n = start_state;
    int path_length = 0;

    // Calculate the length of the path
    while (n != NULL) {
        path_length += snprintf(NULL, 0, "%lld", n->id + 1);
        if (n->parent != NULL) {
            path_length++; // Account for the comma
        }
        n = n->parent;
    }

    // Allocate memory for the char array
    char* path = (char*)malloc((path_length + 1) * sizeof(char));
    if (path == NULL) {
        fprintf(stderr, "Memory allocation failed.\n");
        exit(1);
    }

    // Construct the path in the char array
    char* current_position = path;
    n = start_state;
    while (n != NULL) {
        int written = snprintf(current_position, path_length + 1, "%lld", n->id + 1);
        if (written < 0 || written > path_length) {
            fprintf(stderr, "Error constructing the path.\n");
            free(path);
            exit(1);
        }
        current_position += written;
        if (n->parent != NULL) {
            *current_position = ',';
            current_position++;
        }
        n = n->parent;
    }
    *current_position = '\0'; // Null-terminate the string

    return path;
}

int* generar_arreglo(int n) {
    int* arr = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) {
        arr[i] = 0;
    }
    return arr;
}

/* ------------------------------------------------------------------------------*/
int main() {
    srand(time(0));

    for (int j = 0; j <= 1; j++) {
        unsigned long long min_dist;
        unsigned long long min_time;
        unsigned long long sum_dist_min = 0;
        unsigned long long sum_time_min = 0;
        unsigned long long sum_gen_states_dist = 0;
        unsigned long long sum_exp_states_dist = 0;
        unsigned long long sum_percolations_dist = 0;
        unsigned long long sum_gen_states_time = 0;
        unsigned long long sum_exp_states_time = 0;
        unsigned long long sum_percolations_time = 0;

        FILE *raw_file;
        FILE *gen_paths_distance;
        FILE *gen_paths_time;
        if (j == 0) {
            read_adjacent_table("BAY-road-d.txt");
            raw_file = fopen("BAY_raw.csv", "w");
            gen_paths_distance = fopen("BAY_gen_paths_distance.txt", "w");
            gen_paths_time = fopen("BAY_gen_paths_time.txt", "w");
        }
        else {
            read_adjacent_table("NY-road-d.txt");
            raw_file = fopen("NY_raw.csv", "w");
            gen_paths_distance = fopen("NY_gen_paths_distance.txt", "w");
            gen_paths_time = fopen("NY_gen_paths_time.txt", "w");
        }

        char header[215] = "Nodo Inicial,Nodo Final,Distancia Min,Tiempo Min,Estados Generados (Distancia),Estados Expandidos (Distancia),Percolaciones (Distancia),Estados Generados (Tiempo),Estados Expandidos (Tiempo),Percolaciones (Tiempo)\n";
        printf("%s", header);
        fprintf(raw_file, "%s", header);
        for (int i = 0; i < 1000; i++) {
            char* path;
            start = random_ranged(1, num_gnodes);
            goal = random_ranged(1, num_gnodes);
            new_graph();
            initialize_parameters();

            //Dijkstra for distance
            backward_dijkstra(1);
            min_dist = start_state->h1;
            sum_dist_min += min_dist;
            path = get_path();
            if (i != 0) {
                fprintf(gen_paths_distance, "\n");
            }
            fprintf(gen_paths_distance, "%s", path);

            unsigned long long int percolations_dist = stat_percolations;
            unsigned long long int generated_dist = stat_generated;
            unsigned long long int expansions_dist = stat_expansions;

            sum_gen_states_dist += generated_dist;
            sum_exp_states_dist += expansions_dist;
            sum_percolations_dist += percolations_dist;

            initialize_parameters();

            //Dijkstra for travel time
            backward_dijkstra(2);
            min_time = start_state->h2;
            sum_time_min += min_time;
            path = get_path();
            if (i != 0) {
                fprintf(gen_paths_time, "\n");
            }
            fprintf(gen_paths_time, "%s", path);

            unsigned long long int percolations_time = stat_percolations;
            unsigned long long int generated_time = stat_generated;
            unsigned long long int expansions_time = stat_expansions;

            sum_gen_states_time += generated_time;
            sum_exp_states_time += expansions_time;
            sum_percolations_time += percolations_time;

            char output[255];

            sprintf(output, "%lld,%lld,%llu,%llu,%llu,%llu,%llu,%llu,%llu,%llu\n",
                    start_state->id+1,
                    goal_state->id+1,
                    min_dist,
                    min_time,
                    generated_dist,
                    expansions_dist,
                    percolations_dist,
                    generated_time,
                    expansions_time,
                    percolations_time);

            printf("%s", output);
            fprintf(raw_file, "%s", output);
        }
        fclose(raw_file);
        fclose(gen_paths_distance);
        fclose(gen_paths_time);

        unsigned long long prom_dist_min = sum_dist_min / 1000;
        unsigned long long prom_time_min = sum_time_min / 1000;
        unsigned long long prom_gen_states = sum_gen_states_dist / 1000;
        unsigned long long prom_exp_states = sum_exp_states_dist / 1000;
        unsigned long long prom_percolations = sum_percolations_dist / 1000;

        printf("Promedio Distancia Minima: %llu\n", prom_dist_min);
        printf("Promedio Tiempo Minimo: %llu\n", prom_time_min);
        printf("Promedio Estados Generados: %llu\n", prom_gen_states);
        printf("Promedio Estados Expandidos: %llu\n", prom_exp_states);
        printf("Promedio Percolaciones: %llu\n", prom_percolations);
    }

    printf("\n");
    // Leer archivos generados y conseguir frecuencia de números
    FILE *report = fopen("Reporte.txt", "w");
    for (int i = 0; i < 4; i++) {
        FILE *file;
        int *nums;
        int nums_size;
        char type[100];
        switch (i) {
            case 0:
                file = fopen("BAY_gen_paths_distance.txt", "r");
                nums_size = 321270;
                strncpy(type, "BAY Distancia", 100);
                break;
            case 1:
                file = fopen("BAY_gen_paths_time.txt", "r");
                nums_size = 321270;
                strncpy(type, "BAY Tiempo", 100);
                break;
            case 2:
                file = fopen("NY_gen_paths_distance.txt", "r");
                nums_size = 264346;
                strncpy(type, "NY Distancia", 100);
                break;
            case 3:
                file = fopen("NY_gen_paths_time.txt", "r");
                nums_size = 264346;
                strncpy(type, "NY Tiempo", 100);
                break;
        }
        nums = generar_arreglo(nums_size);

        char buffer[8192]; // Buffer to store the line
        while (fgets(buffer, sizeof(buffer), file) != NULL) {
            char *pt;

            pt = strtok (buffer,",");
            while (pt != NULL) {
                int a = atoi(pt);
                if (a > nums_size) {
                    printf("Error %d\n", a);
                }
                else {
                    nums[a-1] += 1;
                }
                pt = strtok (NULL, ",");
            }
        }

        int max = 0;
        int rep;
        for (int j = 0; j < nums_size; j++) {
            if (nums[j] > max) {
                max = j;
            }
        }
        rep = nums[max];

        char output[255];
        sprintf(output, "Nodo max %s: %d, con %d repeticiones\n", type, max+1, rep);
        printf("%s", output);
        fprintf(report, "%s", output);
        fclose(file);
    }
    fclose(report);
    return 0;
}
