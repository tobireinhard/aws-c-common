#ifndef AWS_COMMON_LINKED_LIST_INL
#define AWS_COMMON_LINKED_LIST_INL

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <aws/common/linked_list.h>
#include <stddef.h>

AWS_EXTERN_C_BEGIN


/*@
// The below predicates describe well-formed doubly linked lists and nodes.
// -------------------------------------------------------------------------------------------
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

lemma void aws_linked_list_node_to_byes(struct aws_linked_list_node* node)
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


/*@
// Lemmas to reason about lists
// -------------------------------------------------------------------------------------------
lemma void mem_after_remove<t>(t m, t r, list<t> ts);
requires m != r &*& mem(m, ts) == true;
ensures mem(m, remove(r, ts)) == true;
@*/




/**
 * Set node's next and prev pointers to NULL.
 */
AWS_STATIC_IMPL void aws_linked_list_node_reset(struct aws_linked_list_node *node) 
//@ requires aws_linked_list_node(node, ?prev, ?next);
//@ ensures aws_linked_list_node(node, NULL, NULL);
{
//    AWS_PRECONDITION(node != NULL);
    
    #ifdef VERIFAST /*VF_refacotring: No support for: 
                                                            1.) dereferencing pointer inside macro argument
                                                            2.) taking the size of a variable or a pointer */
        // -> maually resolve macro & overcome syntax restrictions
/*
        do
        {
            memset(node, 0, sizeof(struct aws_linked_list_node));
        } while (0)
*/
	int x = 0;
	do
	//@ invariant true;
	{
		x = 13;
	} while(0);
	//@ assert x == 13;
	
	
	do
	//@ invariant aws_linked_list_node(node, _, _);
	{
		//@ aws_linked_list_node_to_byes(node);
		//@ open aws_linked_list_node_bytes(node, _);
		memset(node, 0, sizeof(struct aws_linked_list_node));
		//@ close aws_linked_list_node_bytes(node, _);
		//@ bytes_to_aws_linked_list_node(node);
        } while(0);
//    	AWS_POSTCONDITION(AWS_IS_ZEROED(node_val));
    #else
    	AWS_ZERO_STRUCT(*node);
    	AWS_POSTCONDITION(AWS_IS_ZEROED(*node));
    #endif
}

/**
 * These functions need to be defined first as they are used in pre
 * and post conditions.
 */

/**
 * Tests if the list is empty.
 */
AWS_STATIC_IMPL bool aws_linked_list_empty(const struct aws_linked_list *list) {
    AWS_PRECONDITION(list);
    return list->head.next == &list->tail;
}

/**
 * Checks that a linked list is valid.
 */
AWS_STATIC_IMPL bool aws_linked_list_is_valid(const struct aws_linked_list *list) {
    if (list && list->head.next && list->head.prev == NULL && list->tail.prev && list->tail.next == NULL) {
#if (AWS_DEEP_CHECKS == 1)
        return aws_linked_list_is_valid_deep(list);
#else
        return true;
#endif
    }
    return false;
}

/**
 * Checks that the prev of the next pointer of a node points to the
 * node. As this checks whether the [next] connection of a node is
 * bidirectional, it returns false if used for the list tail.
 */
AWS_STATIC_IMPL bool aws_linked_list_node_next_is_valid(const struct aws_linked_list_node *node) 
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
{
    return node && node->next && node->next->prev == node;
}

/**
 * Checks that the next of the prev pointer of a node points to the
 * node. Similarly to the above, this returns false if used for the
 * head of a list.
 */
AWS_STATIC_IMPL bool aws_linked_list_node_prev_is_valid(const struct aws_linked_list_node *node) {
    return node && node->prev && node->prev->next == node;
}



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
AWS_STATIC_IMPL bool aws_linked_list_is_valid_deep(const struct aws_linked_list *list) 
//@ requires unvalidated_list(list, ?head, ?tail, ?all_nodes);
//@ ensures unvalidated_list(list, head, tail, all_nodes);
{
    if (!list) {
        return false;
    }
    /* This could go into an infinite loop for a circular list */
    const struct aws_linked_list_node *temp = &list->head;
    /* Head must reach tail by following next pointers */
    bool head_reaches_tail = false;
    /* By satisfying the above and that edges are bidirectional, we
     * also guarantee that tail reaches head by following prev
     * pointers */
    
    //@ open unvalidated_list(list, head, tail, all_nodes);
    //@ foreach_remove(head, all_nodes);
    //@ foreach_unremove(head, all_nodes);
    //@ close unvalidated_list(list, head, tail, all_nodes);
    
    while (temp) 
    /*@ invariant unvalidated_list(list, head, tail, all_nodes) &*&
                          (temp != NULL 
                              ? mem(temp, all_nodes) == true 
                              : true
                          );
    @*/
    {
        //@ open unvalidated_list(list, head, tail, all_nodes);
        //@ foreach_remove(temp, all_nodes);
        /*@
        if(temp != tail) {
//            struct aws_linked_list_node* next;
            struct aws_linked_list_node* next_prev;
            open unvalidated_list_node(all_nodes)(temp);
            assert temp->next |-> ?next;
            if (next == temp) {
                assert next != NULL;
                assert temp->prev |-> ?prev;
                next_prev = prev;
            } else if (next != NULL) {
                assert mem(next, all_nodes) == true;
                assert next != temp;
                mem_after_remove(next, temp, all_nodes);
                assert next != temp;
                foreach_remove(next, remove(temp, all_nodes));
                open unvalidated_list_node(all_nodes)(next);
                assert next->prev |-> ?next_prev';
                next_prev = next_prev';
            } else {
                next_prev = NULL;
            }
            close fix_nodes(next, next_prev);
        }
        @*/
        if (temp == &list->tail) {
            head_reaches_tail = true;
            //@ foreach_unremove(temp, all_nodes);
            //@ close unvalidated_list(list, head, tail, all_nodes);
            break;
        } else if (!aws_linked_list_node_next_is_valid(temp)) {
            /* Next and prev pointers should connect the same nodes */

            //@ open fix_nodes(_, _);
            /*@
            if (temp->next != temp && temp->next != NULL) {
                assert mem(temp->next, all_nodes) == true;
                close unvalidated_list_node(all_nodes)(temp->next);
                foreach_unremove(temp->next, remove(temp, all_nodes));
            }
            @*/
            //@ close unvalidated_list_node(all_nodes)(temp);
            //@ foreach_unremove(temp, all_nodes);
            //@ close unvalidated_list(list, head, tail, all_nodes);

            
            return false;
        }
        
        //@ open fix_nodes(_, _);
        /*@
        if (temp->next != temp && temp->next != NULL) {
            assert mem(temp->next, all_nodes) == true;
            close unvalidated_list_node(all_nodes)(temp->next);
            foreach_unremove(temp->next, remove(temp, all_nodes));
        }
        @*/
            
        //@ struct aws_linked_list_node* old_temp = temp;
        temp = temp->next;
        //@ close unvalidated_list_node(all_nodes)(old_temp);
        //@ foreach_unremove(old_temp, all_nodes);
        //@ close unvalidated_list(list, head, tail, all_nodes);
    }
    
    return head_reaches_tail;
}

/**
 * Initializes the list. List will be empty after this call.
 */
AWS_STATIC_IMPL void aws_linked_list_init(struct aws_linked_list *list) 
//@ requires aws_linked_list(list, ?length);
/*@ ensures aws_linked_list(list, 0) &*&
                    length == 0 ? true
                    	: node_list(_, _, _, _);
@*/
{
//    AWS_PRECONDITION(list);
    //@ open aws_linked_list(list, length);
    list->head.next = &list->tail;
    list->head.prev = NULL;
    list->tail.prev = &list->head;
    list->tail.next = NULL;
    //@ close aws_linked_list(list, 0);
//    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
//    AWS_POSTCONDITION(aws_linked_list_empty(list));
}

/**
 * Returns an iteration pointer for the first element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_begin(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    struct aws_linked_list_node *rval = list->head.next;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(rval == list->head.next);
    return rval;
}

/**
 * Returns an iteration pointer for one past the last element in the list.
 */
AWS_STATIC_IMPL const struct aws_linked_list_node *aws_linked_list_end(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    const struct aws_linked_list_node *rval = &list->tail;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(rval == &list->tail);
    return rval;
}

/**
 * Returns a pointer for the last element in the list.
 * Used to begin iterating the list in reverse. Ex:
 *   for (i = aws_linked_list_rbegin(list); i != aws_linked_list_rend(list); i = aws_linked_list_prev(i)) {...}
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_rbegin(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    struct aws_linked_list_node *rval = list->tail.prev;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(rval == list->tail.prev);
    return rval;
}

/**
 * Returns the pointer to one before the first element in the list.
 * Used to end iterating the list in reverse.
 */
AWS_STATIC_IMPL const struct aws_linked_list_node *aws_linked_list_rend(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    const struct aws_linked_list_node *rval = &list->head;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(rval == &list->head);
    return rval;
}

/**
 * Returns the next element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_next(const struct aws_linked_list_node *node) {
    AWS_PRECONDITION(aws_linked_list_node_next_is_valid(node));
    struct aws_linked_list_node *rval = node->next;
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(node));
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(rval));
    AWS_POSTCONDITION(rval == node->next);
    return rval;
}

/**
 * Returns the previous element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_prev(const struct aws_linked_list_node *node) {
    AWS_PRECONDITION(aws_linked_list_node_prev_is_valid(node));
    struct aws_linked_list_node *rval = node->prev;
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(node));
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(rval));
    AWS_POSTCONDITION(rval == node->prev);
    return rval;
}

/**
 * Inserts to_add immediately after after.
 */
AWS_STATIC_IMPL void aws_linked_list_insert_after(
    struct aws_linked_list_node *after,
    struct aws_linked_list_node *to_add)
/*@ requires aws_linked_list_node(after, ?prefix, ?suffix) &*& aws_linked_list_node(to_add, _, _) 
                     &*& aws_linked_list_node(suffix, after, ?suffix_rest);
@*/
/*@ ensures aws_linked_list_node(after, prefix, to_add) &*& aws_linked_list_node(to_add, after, suffix) 
                    &*& aws_linked_list_node(suffix, to_add, suffix_rest);
@*/
{
//    AWS_PRECONDITION(aws_linked_list_node_next_is_valid(after));
//    AWS_PRECONDITION(to_add != NULL);
    //@ open aws_linked_list_node(to_add, _, _);
    //@ open aws_linked_list_node(after, _, _);
    //@ open aws_linked_list_node(suffix, _, _);
    to_add->prev = after;
    to_add->next = after->next;
    after->next->prev = to_add;
    after->next = to_add;
    //@ close aws_linked_list_node(after, prefix, to_add);
    //@ close aws_linked_list_node(to_add, after, suffix);
    //@ close aws_linked_list_node(suffix, to_add, suffix_rest);
//    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(after));
//    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(to_add));
//    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(to_add));
//    AWS_POSTCONDITION(after->next == to_add);
}

/**
 * Swaps the order two nodes in the linked list.
 */
AWS_STATIC_IMPL void aws_linked_list_swap_nodes(struct aws_linked_list_node *a, struct aws_linked_list_node *b) {
    AWS_PRECONDITION(aws_linked_list_node_prev_is_valid(a));
    AWS_PRECONDITION(aws_linked_list_node_next_is_valid(a));
    AWS_PRECONDITION(aws_linked_list_node_prev_is_valid(b));
    AWS_PRECONDITION(aws_linked_list_node_next_is_valid(b));

    if (a == b) {
        return;
    }

    /* snapshot b's value to avoid clobbering its next/prev pointers if a/b are adjacent */
    struct aws_linked_list_node tmp = *b;
    a->prev->next = b;
    a->next->prev = b;

    tmp.prev->next = a;
    tmp.next->prev = a;

    tmp = *a;
    *a = *b;
    *b = tmp;

    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(a));
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(a));
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(b));
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(b));
}

/**
 * Inserts to_add immediately before before.
 */
AWS_STATIC_IMPL void aws_linked_list_insert_before(
    struct aws_linked_list_node *before,
    struct aws_linked_list_node *to_add) {
    AWS_PRECONDITION(aws_linked_list_node_prev_is_valid(before));
    AWS_PRECONDITION(to_add != NULL);
    to_add->next = before;
    to_add->prev = before->prev;
    before->prev->next = to_add;
    before->prev = to_add;
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(before));
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(to_add));
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(to_add));
    AWS_POSTCONDITION(before->prev == to_add);
}

/**
 * Removes the specified node from the list (prev/next point to each other) and
 * returns the next node in the list.
 */
AWS_STATIC_IMPL void aws_linked_list_remove(struct aws_linked_list_node *node)
/*@ requires aws_linked_list_node(node, ?prev, ?next) &*&
                     aws_linked_list_node(prev, ?prefix, node) &*&
                     aws_linked_list_node(next, node, ?suffix);
@*/
/*@ ensures aws_linked_list_node(node, NULL, NULL) &*&
                     aws_linked_list_node(prev, prefix, next) &*&
                     aws_linked_list_node(next, prev, suffix);
@*/
{
//    AWS_PRECONDITION(aws_linked_list_node_prev_is_valid(node));
//    AWS_PRECONDITION(aws_linked_list_node_next_is_valid(node));
    //@ open aws_linked_list_node(node, _, _);
    //@ open aws_linked_list_node(prev, _, _);
    //@ open aws_linked_list_node(next, _, _);
    node->prev->next = node->next;
    node->next->prev = node->prev;
    //@ close aws_linked_list_node(node, prev, next);
    aws_linked_list_node_reset(node);
    //@ close aws_linked_list_node(prev, prefix, next);
    //@ close aws_linked_list_node(next, prev, suffix);
//    AWS_POSTCONDITION(node->next == NULL && node->prev == NULL);
}

/**
 * Append new_node.
 */
AWS_STATIC_IMPL void aws_linked_list_push_back(struct aws_linked_list *list, struct aws_linked_list_node *node) {
//    AWS_PRECONDITION(aws_linked_list_is_valid(list));
//    AWS_PRECONDITION(node != NULL);
    aws_linked_list_insert_before(&list->tail, node);
//    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
//    AWS_POSTCONDITION(list->tail.prev == node, "[node] is the new last element of [list]");
}

/**
 * Returns the element in the back of the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_back(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    AWS_PRECONDITION(!aws_linked_list_empty(list));
    struct aws_linked_list_node *rval = list->tail.prev;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(rval));
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(rval));
    return rval;
}

/**
 * Returns the element in the back of the list and removes it
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_pop_back(struct aws_linked_list *list) {
    AWS_PRECONDITION(!aws_linked_list_empty(list));
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    struct aws_linked_list_node *back = aws_linked_list_back(list);
    aws_linked_list_remove(back);
    AWS_POSTCONDITION(back->next == NULL && back->prev == NULL);
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    return back;
}

/**
 * Prepend new_node.
 */
AWS_STATIC_IMPL void aws_linked_list_push_front(struct aws_linked_list *list, struct aws_linked_list_node *node) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    AWS_PRECONDITION(node != NULL);
    aws_linked_list_insert_before(list->head.next, node);
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(list->head.next == node, "[node] is the new first element of [list]");
}

/**
 * Returns the element in the front of the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_front(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    AWS_PRECONDITION(!aws_linked_list_empty(list));
    struct aws_linked_list_node *rval = list->head.next;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(aws_linked_list_node_prev_is_valid(rval));
    AWS_POSTCONDITION(aws_linked_list_node_next_is_valid(rval));
    return rval;
}

/**
 * Returns the element in the front of the list and removes it
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_pop_front(struct aws_linked_list *list) {
    AWS_PRECONDITION(!aws_linked_list_empty(list));
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    struct aws_linked_list_node *front = aws_linked_list_front(list);
    aws_linked_list_remove(front);
    AWS_POSTCONDITION(front->next == NULL && front->prev == NULL);
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    return front;
}

AWS_STATIC_IMPL void aws_linked_list_swap_contents(
    struct aws_linked_list *AWS_RESTRICT a,
    struct aws_linked_list *AWS_RESTRICT b) {

    AWS_PRECONDITION(aws_linked_list_is_valid(a));
    AWS_PRECONDITION(aws_linked_list_is_valid(b));
    AWS_PRECONDITION(a != b);
    struct aws_linked_list_node *a_first = a->head.next;
    struct aws_linked_list_node *a_last = a->tail.prev;

    /* Move B's contents into A */
    if (aws_linked_list_empty(b)) {
        aws_linked_list_init(a);
    } else {
        a->head.next = b->head.next;
        a->head.next->prev = &a->head;
        a->tail.prev = b->tail.prev;
        a->tail.prev->next = &a->tail;
    }

    /* Move A's old contents into B */
    if (a_first == &a->tail) {
        aws_linked_list_init(b);
    } else {
        b->head.next = a_first;
        b->head.next->prev = &b->head;
        b->tail.prev = a_last;
        b->tail.prev->next = &b->tail;
    }
    AWS_POSTCONDITION(aws_linked_list_is_valid(a));
    AWS_POSTCONDITION(aws_linked_list_is_valid(b));
}

AWS_STATIC_IMPL void aws_linked_list_move_all_back(
    struct aws_linked_list *AWS_RESTRICT dst,
    struct aws_linked_list *AWS_RESTRICT src) {

    AWS_PRECONDITION(aws_linked_list_is_valid(src));
    AWS_PRECONDITION(aws_linked_list_is_valid(dst));
    AWS_PRECONDITION(dst != src);

    if (!aws_linked_list_empty(src)) {
        /* splice src nodes into dst, between the back and tail nodes */
        struct aws_linked_list_node *dst_back = dst->tail.prev;
        struct aws_linked_list_node *src_front = src->head.next;
        struct aws_linked_list_node *src_back = src->tail.prev;

        dst_back->next = src_front;
        src_front->prev = dst_back;

        dst->tail.prev = src_back;
        src_back->next = &dst->tail;

        /* reset src */
        src->head.next = &src->tail;
        src->tail.prev = &src->head;
    }

    AWS_POSTCONDITION(aws_linked_list_is_valid(src));
    AWS_POSTCONDITION(aws_linked_list_is_valid(dst));
}

AWS_STATIC_IMPL void aws_linked_list_move_all_front(
    struct aws_linked_list *AWS_RESTRICT dst,
    struct aws_linked_list *AWS_RESTRICT src) {

    AWS_PRECONDITION(aws_linked_list_is_valid(src));
    AWS_PRECONDITION(aws_linked_list_is_valid(dst));
    AWS_PRECONDITION(dst != src);

    if (!aws_linked_list_empty(src)) {
        /* splice src nodes into dst, between the head and front nodes */
        struct aws_linked_list_node *dst_front = dst->head.next;
        struct aws_linked_list_node *src_front = src->head.next;
        struct aws_linked_list_node *src_back = src->tail.prev;

        dst->head.next = src_front;
        src_front->prev = &dst->head;

        src_back->next = dst_front;
        dst_front->prev = src_back;

        /* reset src */
        src->head.next = &src->tail;
        src->tail.prev = &src->head;
    }

    AWS_POSTCONDITION(aws_linked_list_is_valid(src));
    AWS_POSTCONDITION(aws_linked_list_is_valid(dst));
}

AWS_EXTERN_C_END

#endif /* AWS_COMMON_LINKED_LIST_INL */
