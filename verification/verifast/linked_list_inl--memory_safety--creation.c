
#include "linked_list--memory_safety.h"
//#include <stddef.h>

//@ #include "list_ext.gh"

/*@
lemma void aws_linked_list_node_next_chunk_distinct(struct aws_linked_list_node* a,
                                                                                    struct aws_linked_list_node* b);
requires a->next |-> ?a_next &*& b->next |-> ?b_next;
ensures  a->next |-> a_next &*& b->next |-> b_next &*& a != b;
@*/

struct aws_linked_list_node* create_node(struct aws_linked_list_node* prev,
                                                                struct aws_linked_list_node* next)
//@ requires true;
//@ ensures aws_linked_list_node(result, prev, next);
{
    struct aws_linked_list_node* node = malloc(sizeof(struct aws_linked_list_node));
    if (node == NULL) abort();
    node->prev = prev;
    node->next = next;
    //@ close aws_linked_list_node(node, prev, next);
    return node;
}

struct aws_linked_list* create_empty_list()
//@ requires true;
//@ ensures aws_linked_list(result, 0);
{
    struct aws_linked_list* list = malloc(sizeof(struct aws_linked_list));
    if (list == NULL) abort();
    
    list->head.prev = NULL;
    list->head.next = &(list->tail);
    
    list->tail.prev = &(list->head);
    list->tail.next = NULL;
    
    //@ close aws_linked_list(list, 0);
    return list;
}


struct aws_linked_list* create_nonempty_list()
//@ requires true;
//@ ensures aws_linked_list(result, 2);
{
    struct aws_linked_list* list = malloc(sizeof(struct aws_linked_list));
    if (list == NULL) abort();
    
    struct aws_linked_list_node* head = &(list->head);
    struct aws_linked_list_node* tail = &(list->tail);
   
    struct aws_linked_list_node* node1 = create_node(head, NULL);
    //@ open aws_linked_list_node(node1, _, _);
    struct aws_linked_list_node* node2 = create_node(node1, tail);
    //@ open aws_linked_list_node(node2, _, _);
    //@ aws_linked_list_node_next_chunk_distinct(node2, tail);
    //@ close aws_linked_list_node(node2, node1, tail);
    node1->next = node2;
    //@ close aws_linked_list_node(node1, &(list->head), node2);
    //@ close node_list(node2, node1, node2, &(list->tail));
    //@ close node_list(node1, &(list->head), node2, &(list->tail));
    
    list->head.prev = NULL;
    list->head.next = node1;
    
    list->tail.prev = node2;
    list->tail.next = NULL;
    
    //@ close aws_linked_list(list, 2);
    return list;
}