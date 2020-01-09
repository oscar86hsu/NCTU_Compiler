#ifndef __LIST_H
#define __LIST_H

#include <stdbool.h>
#include <stddef.h>

typedef void (*FreeFPtr)(void *);

typedef struct __ListNode {
    void *data;
    struct __ListNode *next;
} ListNode;

typedef struct __List {
    ListNode *head;
    ListNode **IndirectTail;
    size_t _size;

    FreeFPtr freeData;
    ListNode *(*begin)(struct __List *self);
    void *(*front)(struct __List *self);
    void (*pushFront)(struct __List *self, void *data);
    void (*pushBack)(struct __List *self, void *data);
    void *(*popFront)(struct __List *self);
    size_t (*size)(const struct __List *self);
} List;

List *newList(FreeFPtr freeData);
void freeList(List *q);

#define DEREF_LIST_NODE(node) node->data
#define ITER_NEXT_LIST_NODE(node) node = node->next
#define LIST_FOR_EACH(node, head)                                              \
    for (node = (head); node != NULL; node = node->next)

#endif /* __LIST_H */
