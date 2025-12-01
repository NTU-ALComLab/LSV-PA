#include "stdlib.h"

typedef struct Cut_t_       Cut_t;
struct Cut_t_
{
    int              cut_size;
    int*             cut_nodes;
};

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
// Reference: https://www.geeksforgeeks.org/c-program-to-sort-an-array-in-ascending-order/
void selection_sort(int* nodes, int size){
    for(int i = 0; i < size-1; i++){
      int min_idx = i;
      // Find the minimum element in the remaining
      // unsorted array
      for (int j = i + 1; j < size; j++) {
          if (nodes[j] < nodes[min_idx]) {
              min_idx = j;
          }
      }
      // Swap the found minimum element with the first
      // element
      int temp = nodes[min_idx];
      nodes[min_idx] = nodes[i];
      nodes[i] = temp;
    }
    return;
}
int compare(const void* a, const void* b){
    return *(int*)a - *(int*)b;
}
Cut_t* new_cut(int* nodes, int size){
    Cut_t* cut = (Cut_t*)malloc(sizeof(Cut_t));
    cut->cut_nodes = (int*)malloc(sizeof(int)*size);
    
    int cutSize = 1;
    // selection_sort(nodes, size);
    qsort(nodes, size, sizeof(int), compare);
    cut->cut_nodes[0] = nodes[0];
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
    for(int i = 0; i < size_1; i++){
        nodes[i] = nodes_1[i];
        // printf("%d ", nodes[i]);
    }
    for(int i = 0; i < size_2; i++){
        nodes[size_1+i] = nodes_2[i];
        // printf("%d ", nodes[size_1+i]);
    }
    Cut_t* cut = new_cut(nodes, size_1+size_2);
    // printf("\n");
    // for(int i = 0; i < cut->cut_size; i++){
    //     printf("%d ", cut->cut_nodes[i]);
    // }
    // printf("cut_size = %d\n", cut->cut_size);
    free(nodes);
    // printf("free nodes\n");
    return cut;
}
Cut_t* new_cut(Cut_t* cut1, Cut_t* cut2){
    return new_cut(cut1->cut_nodes, cut1->cut_size, cut2->cut_nodes, cut2->cut_size);
}
Cut_t* copy_cut(Cut_t* cut){
    Cut_t* new_cut = (Cut_t*)malloc(sizeof(Cut_t));
    new_cut->cut_size = cut->cut_size;
    new_cut->cut_nodes = (int*)malloc(sizeof(int)*cut->cut_size);
    for(int i = 0; i < cut->cut_size; i++){
        new_cut->cut_nodes[i] = cut->cut_nodes[i];
    }
    return new_cut;
}   
void free_cut(Cut_t* cut){
    if(cut == NULL){
        return;
    }
    // printf("[free]pcut = %p\n", cut);
    if(cut->cut_nodes == NULL){
        printf("[free]cut->cut_nodes == NULL\n");
    }
    else{
        // printf("[free]pcut = %p\n", cut->cut_nodes);
        free(cut->cut_nodes);
        cut->cut_nodes = NULL;
    }
    // printf("[free]pcut = %p\n", cut);
    free(cut);
    return;
}
void free_cuts(Cut_t** cuts, int size){
    if(cuts == NULL){
        return;
    }
    // printf("[free]size = %d, pcut = %p, %d\n", size, cuts, cuts);
    for(int i = 0; i < size; i++){
        free_cut(cuts[i]);
    }
    // printf("free cut[]\n");
    if(cuts != NULL){
        // printf("[free]pcut = %p, %d\n", cuts, cuts);
        free(cuts);
        cuts = NULL;
    }
    // printf("after free cuts\n");
    return;
}
void print_cut(Cut_t* cut){
    for(int i = 0; i < cut->cut_size; i++){
        printf("%d ", cut->cut_nodes[i]);
    }
    printf("\n");
    return;
}

int cut_equal(Cut_t* cut1, Cut_t* cut2){
    if(cut1->cut_size != cut2->cut_size){
        return 0;
    }
    for(int i = 0; i < cut1->cut_size; i++){
        if(cut1->cut_nodes[i] != cut2->cut_nodes[i]){
            return 0;
        }
    }
    return 1;
}
int cut_compare(const void* cut_1, const void* cut_2){
    Cut_t* cut1 = (Cut_t*)cut_1;
    Cut_t* cut2 = (Cut_t*)cut_2;
    if(cut1->cut_size != cut2->cut_size){
        return cut1->cut_size - cut2->cut_size;
    }
    for(int i = 0; i < cut1->cut_size; i++){
        if(cut1->cut_nodes[i] != cut2->cut_nodes[i]){
            return cut1->cut_nodes[i] - cut2->cut_nodes[i];
        }
    }
    return 0;
}
void sort_cut(Cut_t** cuts, int size){
    // selection_sort
    for(int i=0; i<size-1; i++){
        int min_idx = i;
        for(int j=i+1; j<size; j++){
            if(cut_compare(cuts[j], cuts[min_idx]) < 0){
                min_idx = j;
            }
        }
        Cut_t* temp = cuts[min_idx];
        cuts[min_idx] = cuts[i];
        cuts[i] = temp;
    }
    return;
}
// is cut1 a subset of cut2
int cut_subset(const Cut_t* cut1, const Cut_t* cut2){
    if(cut1->cut_size > cut2->cut_size){
        return 0;
    }
    int i = 0;
    int j = 0;
    while(i < cut1->cut_size && j < cut2->cut_size){
        if(cut1->cut_nodes[i] == cut2->cut_nodes[j]){
            i++;
            j++;
        }
        else{
            j++;
        }
    }
    if(i == cut1->cut_size){
        return 1;
    }
    return 0;
}
void remove_subset_cut(Cut_t** cuts, int& size){
    Cut_t** new_cuts = (Cut_t**)malloc(sizeof(Cut_t*)*size);

    int i = 0;
    new_cuts[0] = copy_cut(cuts[0]);
    for(int j = 1; j < size; j++){
        int flag = 0;
        for(int k = 0; k <= i; k++){
            // printf("before cut_subset\n");
            if(cut_subset(new_cuts[k], cuts[j])){
                // printf("in cut_subset\n");
                // print_cut(new_cuts[k]);
                // print_cut(cuts[j]);
                flag = 1;
                break;
            }
        }
        if(flag == 0){
            i++;
            new_cuts[i] = copy_cut(cuts[j]);
        }
    }
    // printf("After remove_subset_cut\n");
    // free_cuts(cuts, size);
    // printf("After free_cuts\n");
    size = i+1;
    for(int j = 0; j < size; j++){
        cuts[j] = new_cuts[j];
    }
    // free_cuts(new_cuts, size);
    // cuts = new_cuts;
    return;
}
Cut_t** cut_sort_and_eliminate(Cut_t** cuts, int& size, int k_feasible){
    
    // printf("Before sort cutsize: ");
    // for(int j = 0; j < size; j++){
    //     printf("%d ", cuts[j]->cut_size);
    // }
    // printf("\n");
    // qsort(cuts, size, sizeof(Cut_t*), cut_compare);
    sort_cut(cuts, size);
    // printf("Before remove_subset_cut\n");
    remove_subset_cut(cuts, size);
    // printf("After remove_subset_cut");
    // for(int j = 0; j < size; j++){
    //     printf("%d ", cuts[j]->cut_size);
    // }
    // printf("\n");
    // eliminate duplicate cuts
    int i = 0;
    for(int j = 1; j < size; j++){
        if(cuts[j]->cut_size > k_feasible){
            free_cut(cuts[j]);
            continue;
        }
        if(cut_compare(cuts[i], cuts[j]) != 0){
            i++;
            cuts[i] = cuts[j];
        }
        else{
            free_cut(cuts[j]);
        }
    }
    if(cuts[0]->cut_size > k_feasible){
        free_cut(cuts[0]);
        size = 0;
        free(cuts);
        return NULL;
    }
    size = i+1;
    return cuts;
}