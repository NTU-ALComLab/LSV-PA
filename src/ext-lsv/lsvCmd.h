#include <stdio.h>
#include <stdlib.h>

typedef struct Cut_t_       Cut_t;
struct Cut_t_
{
    int              cut_size;
    int*             cut_nodes;
};

void print_cut(Cut_t* cut){
    for(int i = 0; i < cut->cut_size; i++){
        printf("%d ", cut->cut_nodes[i]);
    }
    printf("\n");
    return;
}

// Find index of nodeID in id_to_index array (hash map)
int find_index(int* id_to_index, int array_size, int node_id) {
    int index = -1;
    for(int i=array_size - 1; i>=0; i--){
      if(id_to_index[i] == node_id){
        index = i;
        break;
      }
    }
    return index;
  }

  // Comparison function for qsort
int compareInt(const void *a, const void *b) {
    int ia = *(int *)a;
    int ib = *(int *)b;
    return (ia - ib);
}

// Create a new cut
Cut_t* new_cut(int* nodes, int size){
    Cut_t* cut = (Cut_t*)malloc(sizeof(Cut_t));
    cut->cut_nodes = (int*)malloc(sizeof(int)*size);
    
    int cutSize = 1;
    qsort(nodes, size, sizeof(int), compareInt);
    // Remove duplicates
    cut->cut_nodes[0] = nodes[0];
    // Add nodes to cut
    for(int i = 1; i < size; i++){
        if(cut->cut_nodes[cutSize-1] == nodes[i]){
            continue;
        }
        else{
            cut->cut_nodes[cutSize] = nodes[i];
            cutSize++;
        }
    }
    cut->cut_size = cutSize;
    return cut;
}
Cut_t* new_cut(int* nodes_1, int size_1, int* nodes_2, int size_2){
    int* nodes = (int*)malloc(sizeof(int)*(size_1+size_2));

    // Merge two arrays
    for(int i = 0; i < size_1; i++){
        nodes[i] = nodes_1[i];
    }
    for(int i = 0; i < size_2; i++){
        nodes[size_1+i] = nodes_2[i];
    }
    // Create new cut
    Cut_t* cut = new_cut(nodes, size_1+size_2);
    free(nodes);
    return cut;
}
Cut_t* new_cut(Cut_t* cut1, Cut_t* cut2){
    return new_cut(cut1->cut_nodes, cut1->cut_size, cut2->cut_nodes, cut2->cut_size);
}
// Copy a cut
Cut_t* copy_cut(Cut_t* cut){
    Cut_t* new_cut = (Cut_t*)malloc(sizeof(Cut_t));
    new_cut->cut_size = cut->cut_size;
    new_cut->cut_nodes = (int*)malloc(sizeof(int)*cut->cut_size);
    for(int i = 0; i < cut->cut_size; i++){
        new_cut->cut_nodes[i] = cut->cut_nodes[i];
    }
    return new_cut;
}   

// Free a cut
void free_cut(Cut_t* cut){
    if(cut == NULL){
        return;
    }
    // if(cut->cut_nodes == NULL){
    //     printf("[free]cut->cut_nodes == NULL\n");
    // }
    else{
        free(cut->cut_nodes);
        cut->cut_nodes = NULL;
    }
    free(cut);
    return;
}
void free_cuts(Cut_t** cuts, int size){
    if(cuts == NULL){
        return;
    }
    for(int i = 0; i < size; i++){
        free_cut(cuts[i]);
    }
    if(cuts != NULL){
        free(cuts);
        cuts = NULL;
    }
    return;
}

