#ifndef AWS_COMMON_LINKED_LIST_H
#define AWS_COMMON_LINKED_LIST_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

#include <stddef.h>

struct aws_linked_list_node {
    struct aws_linked_list_node *next;
    struct aws_linked_list_node *prev;
};

struct aws_linked_list {
    struct aws_linked_list_node head;
    struct aws_linked_list_node tail;
};




/*@
// The below predicates describe well-formed doubly linked lists and nodes.
// -------------------------------------------------------------------------------------------

// Standard representation of a node using a struct-specific malloc block.
// Created when allocating memory by using 
// malloc(sizeof(struct aws_linked_list_node)).
predicate aws_linked_list_node(struct aws_linked_list_node* node,
                               struct aws_linked_list_node* prev,
                               struct aws_linked_list_node* next) =
	node->prev |-> prev &*&
	node->next |-> next &*&
	malloc_block_aws_linked_list_node(node);

predicate aws_linked_list_node_raw(struct aws_linked_list_node* node,
                               struct aws_linked_list_node* prev,
                               struct aws_linked_list_node* next) =
	node->prev |-> prev &*&
	node->next |-> next &*&
        malloc_block(node, sizeof(struct aws_linked_list_node)) &*&
	struct_aws_linked_list_node_padding(node);
	
predicate aws_linked_list_node_bytes(struct aws_linked_list_node* node,
                               list<char> bytes) =
	chars((void*) node, sizeof(struct aws_linked_list_node), bytes) &*&
        malloc_block(node, sizeof(struct aws_linked_list_node));


predicate node_list(struct aws_linked_list_node* startNode,
                    struct aws_linked_list_node* startPrev,
                    struct aws_linked_list_node* lastNode,
                    struct aws_linked_list_node* tail) =
	aws_linked_list_node(startNode, startPrev, ?next) &*&
	startNode == lastNode
		? next == tail
		: node_list(next, startNode, lastNode, tail);

predicate aws_linked_list(struct aws_linked_list* list, int length) =
	length >= 0 &*&
	aws_linked_list_node_next(&(list->head), ?headNext) &*&   // list->head.next
	aws_linked_list_node_prev(&(list->head), NULL) &*&        // list->head.prev
	aws_linked_list_node_next(&(list->tail), NULL) &*&        // list->tail.next
	aws_linked_list_node_prev(&(list->tail), ?tailPrev) &*&   // list->tail.prev
	length == 0 
		? (headNext == &(list->tail) &*& tailPrev == &(list->head))
		:
		node_list(headNext, &(list->head), tailPrev, &(list->tail));
@*/



/*@
// The below predicates describe doubly linked lists and nodes that are
// unvalidated and therefore potentially malformed.
// -------------------------------------------------------------------------------------------
predicate_ctor unvalidated_list_node(list<struct aws_linked_list_node*> all_nodes)
                                                        (struct aws_linked_list_node* node) =
    node != NULL &*&
    malloc_block_aws_linked_list_node(node) &*&
    mem(node, all_nodes) == true &*&
    node->prev |-> ?prev &*&
    node->next |-> ?next &*&
    (prev != NULL ? mem(prev, all_nodes) == true : true) &*&
    (next != NULL ? mem(next, all_nodes) == true : true);




predicate unvalidated_list(struct aws_linked_list* list,
                                        struct aws_linked_list_node* head,
                                        struct aws_linked_list_node* tail,
                                        list<struct aws_linked_list_node*> all_nodes) = 
    list != NULL &*& head != NULL &*& tail != NULL &*&
    &(list->head) == head &*& &(list->tail) == tail &*&
    mem(head, all_nodes) == true &*&
    mem(tail, all_nodes) == true &*&
    foreach(all_nodes, unvalidated_list_node(all_nodes));
    
    
predicate fix_nodes(struct aws_linked_list_node* a, struct aws_linked_list_node* b) = true;
@*/



/*@
// Consider the code
// struct T { ... };
// struct T* tp = ...;
// Depending of how memory for the new  struct instance has been allocated, it can be represented by
// one of the following chunk combination (which are equivalent):
// 1.) malloc_block_T(tp)
// 2.) malloc_block(tp, sizeof(struct T) &*& struct_T_padding(node)
// The following lemmas convert beteen these representations.

lemma void generic_malloc_block_to_malloc_block_aws_linked_list_node(struct aws_linked_list_node* node);
requires malloc_block(node, sizeof(struct aws_linked_list_node)) &*&
              struct_aws_linked_list_node_padding(node);
ensures malloc_block_aws_linked_list_node(node);

lemma void malloc_block_aws_linked_list_node_to_generic_malloc_block(struct aws_linked_list_node* node);
requires malloc_block_aws_linked_list_node(node);
ensures malloc_block(node, sizeof(struct aws_linked_list_node)) &*&
              struct_aws_linked_list_node_padding(node);
@*/

/*@
// conversion between aws_linked_list_node(node, prev, next) and 
// aws_linked_list_node_raw(node, prev, next)
lemma void aws_linked_list_node_to_aws_linked_list_node_raw(struct aws_linked_list_node* node)
requires aws_linked_list_node(node, ?prev, ?next);
ensures aws_linked_list_node_raw(node, prev, next);
{
    open aws_linked_list_node(node, _, _);
    malloc_block_aws_linked_list_node_to_generic_malloc_block(node);
    close aws_linked_list_node_raw(node, _, _);
}

lemma void aws_linked_list_node_raw_to_aws_linked_list_node(struct aws_linked_list_node* node)
requires aws_linked_list_node_raw(node, ?prev, ?next);
ensures aws_linked_list_node(node, prev, next);
{
    open aws_linked_list_node_raw(node, _, _);
    generic_malloc_block_to_malloc_block_aws_linked_list_node(node);
    close aws_linked_list_node(node, _, _);
}

lemma void aws_linked_list_node_to_bytes(struct aws_linked_list_node* node)
requires aws_linked_list_node(node, ?prev, ?next);
ensures aws_linked_list_node_bytes(node, ?bytes);
{
    open aws_linked_list_node(node, _, _);
    malloc_block_aws_linked_list_node_to_generic_malloc_block(node);
    open_struct(node);
    close aws_linked_list_node_bytes(node, ?bytes);
}

lemma void bytes_to_aws_linked_list_node(struct aws_linked_list_node* node)
requires aws_linked_list_node_bytes(node, ?bytes);
ensures aws_linked_list_node(node, ?prev, ?next) &*&
             all_eq(bytes, 0) == true ? (prev == NULL &*& next == NULL) : true;
{
    open aws_linked_list_node_bytes(node, bytes);
//    close_struct(node);
//    generic_malloc_block_to_malloc_block_aws_linked_list_node(node);
    if (all_eq(bytes, 0))
    {
    	close_struct_zero(node);
    }
    else
    {
    	close_struct(node);
    }
    generic_malloc_block_to_malloc_block_aws_linked_list_node(node);
    close aws_linked_list_node(node, _, _);
}
@*/


AWS_EXTERN_C_BEGIN

/**
 * Set node's next and prev pointers to NULL.
 */
AWS_STATIC_IMPL void aws_linked_list_node_reset(struct aws_linked_list_node *node);
//@ requires aws_linked_list_node(node, ?prev, ?next);
//@ ensures aws_linked_list_node(node, NULL, NULL);

/**
 * These functions need to be defined first as they are used in pre
 * and post conditions.
 */

/**
 * Tests if the list is empty.
 */
AWS_STATIC_IMPL bool aws_linked_list_empty(const struct aws_linked_list *list);

/**
 * Checks that a linked list is valid.
 */
AWS_STATIC_IMPL bool aws_linked_list_is_valid(const struct aws_linked_list *list);
/**
 * Checks that the prev of the next pointer of a node points to the
 * node. As this checks whether the [next] connection of a node is
 * bidirectional, it returns false if used for the list tail.
 */
AWS_STATIC_IMPL bool aws_linked_list_node_next_is_valid(const struct aws_linked_list_node *node);
/*@ requires fix_nodes(?next, ?next_prev) &*&
                     (node != NULL
                         ? node->next |-> next &*&
                            (next != NULL 
                                ? next->prev |-> next_prev 
                                : true)
                         : true);
@*/
/*@ ensures  fix_nodes(next, next_prev) &*&
                     (node != NULL
                         ? node->next |-> next &*&
                            (next != NULL 
                                ? next->prev |-> next_prev 
                                : true)
                         : true);
@*/

/**
 * Checks that the next of the prev pointer of a node points to the
 * node. Similarly to the above, this returns false if used for the
 * head of a list.
 */
AWS_STATIC_IMPL bool aws_linked_list_node_prev_is_valid(const struct aws_linked_list_node *node);
/**
 * Checks that a linked list satisfies double linked list connectivity
 * constraints. This check is O(n) as it traverses the whole linked
 * list to ensure that tail is reachable from head (and vice versa)
 * and that every connection is bidirectional.
 *
 * Note: This check *cannot* go into an infinite loop, because we
 * ensure that the connection to the next node is
 * bidirectional. Therefore, if a node's [a] a.next is a previous node
 * [b] in the list, b.prev != &a and so this check would fail, thus
 * terminating the loop.
 */
AWS_STATIC_IMPL bool aws_linked_list_is_valid_deep(const struct aws_linked_list *list);
//@ requires unvalidated_list(list, ?head, ?tail, ?all_nodes);
//@ ensures unvalidated_list(list, head, tail, all_nodes);

/**
 * Initializes the list. List will be empty after this call.
 */
AWS_STATIC_IMPL void aws_linked_list_init(struct aws_linked_list *list);
//@ requires aws_linked_list(list, ?length);
/*@ ensures aws_linked_list(list, 0) &*&
                    length == 0 ? true
                    	: node_list(_, _, _, _);
@*/

/**
 * Returns an iteration pointer for the first element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_begin(const struct aws_linked_list *list);

/**
 * Returns an iteration pointer for one past the last element in the list.
 */
AWS_STATIC_IMPL const struct aws_linked_list_node *aws_linked_list_end(const struct aws_linked_list *list);

/**
 * Returns a pointer for the last element in the list.
 * Used to begin iterating the list in reverse. Ex:
 *   for (i = aws_linked_list_rbegin(list); i != aws_linked_list_rend(list); i = aws_linked_list_prev(i)) {...}
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_rbegin(const struct aws_linked_list *list);

/**
 * Returns the pointer to one before the first element in the list.
 * Used to end iterating the list in reverse.
 */
AWS_STATIC_IMPL const struct aws_linked_list_node *aws_linked_list_rend(const struct aws_linked_list *list);

/**
 * Returns the next element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_next(const struct aws_linked_list_node *node);

/**
 * Returns the previous element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_prev(const struct aws_linked_list_node *node);

/**
 * Inserts to_add immediately after after.
 */
AWS_STATIC_IMPL void aws_linked_list_insert_after(
    struct aws_linked_list_node *after,
    struct aws_linked_list_node *to_add);
/*@ requires aws_linked_list_node(after, ?prefix, ?suffix) &*& aws_linked_list_node(to_add, _, _) 
                     &*& aws_linked_list_node(suffix, after, ?suffix_rest);
@*/
/*@ ensures aws_linked_list_node(after, prefix, to_add) &*& aws_linked_list_node(to_add, after, suffix) 
                    &*& aws_linked_list_node(suffix, to_add, suffix_rest);
@*/
/**
 * Swaps the order two nodes in the linked list.
 */
AWS_STATIC_IMPL void aws_linked_list_swap_nodes(struct aws_linked_list_node *a, struct aws_linked_list_node *b);

/**
 * Inserts to_add immediately before before.
 */
AWS_STATIC_IMPL void aws_linked_list_insert_before(
    struct aws_linked_list_node *before,
    struct aws_linked_list_node *to_add);

/**
 * Removes the specified node from the list (prev/next point to each other) and
 * returns the next node in the list.
 */
AWS_STATIC_IMPL void aws_linked_list_remove(struct aws_linked_list_node *node);
/*@ requires aws_linked_list_node(node, ?prev, ?next) &*&
                     aws_linked_list_node(prev, ?prefix, node) &*&
                     aws_linked_list_node(next, node, ?suffix);
@*/
/*@ ensures aws_linked_list_node(node, NULL, NULL) &*&
                     aws_linked_list_node(prev, prefix, next) &*&
                     aws_linked_list_node(next, prev, suffix);
@*/

/**
 * Append new_node.
 */
AWS_STATIC_IMPL void aws_linked_list_push_back(struct aws_linked_list *list, struct aws_linked_list_node *node);

/**
 * Returns the element in the back of the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_back(const struct aws_linked_list *list);

/**
 * Returns the element in the back of the list and removes it
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_pop_back(struct aws_linked_list *list);

/**
 * Prepend new_node.
 */
AWS_STATIC_IMPL void aws_linked_list_push_front(struct aws_linked_list *list, struct aws_linked_list_node *node);
/**
 * Returns the element in the front of the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_front(const struct aws_linked_list *list);
/**
 * Returns the element in the front of the list and removes it
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_pop_front(struct aws_linked_list *list);

AWS_STATIC_IMPL void aws_linked_list_swap_contents(
    struct aws_linked_list *AWS_RESTRICT a,
    struct aws_linked_list *AWS_RESTRICT b);

/**
 * Remove all nodes from one list, and add them to the back of another.
 *
 * Example: if dst={1,2} and src={3,4}, they become dst={1,2,3,4} and src={}
 */
AWS_STATIC_IMPL void aws_linked_list_move_all_back(
    struct aws_linked_list *AWS_RESTRICT dst,
    struct aws_linked_list *AWS_RESTRICT src);

/**
 * Remove all nodes from one list, and add them to the front of another.
 *
 * Example: if dst={2,1} and src={4,3}, they become dst={4,3,2,1} and src={}
 */
AWS_STATIC_IMPL void aws_linked_list_move_all_front(
    struct aws_linked_list *AWS_RESTRICT dst,
    struct aws_linked_list *AWS_RESTRICT src);

#ifndef VERIFAST /*VF_refacotring: VF identifies this as a potential recursive inclusion. */
	#ifndef AWS_NO_STATIC_IMPL
	#    include <aws/common/linked_list_inl.c>
	#endif /* AWS_NO_STATIC_IMPL */
#endif
AWS_EXTERN_C_END

#endif /* AWS_COMMON_LINKED_LIST_H */
