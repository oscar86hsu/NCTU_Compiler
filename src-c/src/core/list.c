#include <core/list.h>
#include <core/utils.h>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/************************
 * Function Definition
 ************************/
static ListNode *begin(List *self) { return self->head; }

static void *front(List *self) {
    if (self->_size == 0) {
        return NULL;
    } else {
        return self->head->data;
    }
}

static inline void *newNode(void *data) {
    ListNode *node = (ListNode *)myMalloc(sizeof(ListNode));
    node->data = data;
    node->next = NULL;
    return node;
}

static void pushFront(List *self, void *data) {
    ListNode *NewNode = newNode(data);
    NewNode->next = self->head;
    self->head = NewNode;
    if (self->_size == 0) {
        self->IndirectTail = &NewNode->next;
    }
    ++self->_size;
}

static void pushBack(List *self, void *data) {
    ListNode *NewNode = newNode(data);
    *(self->IndirectTail) = NewNode;
    self->IndirectTail = &NewNode->next;
    ++self->_size;
}

static void *popFront(List *self) {
    if (self->_size == 0) {
        return NULL;
    }

    ListNode *ptr;
    void *retval;

    ptr = self->head;
    self->head = self->head->next;
    if (--self->_size == 0) {
        self->IndirectTail = &self->head;
    }
    retval = ptr->data;
    free(ptr);
    return retval;
}

static size_t size(const List *self) { return self->_size; }

List *newList(FreeFPtr freeData) {
    List *l = (List *)myMalloc(sizeof(List));

    if (l != NULL) {
        l->head = NULL;
        l->IndirectTail = &l->head;
        l->_size = 0U;
        l->freeData = freeData;
        l->begin = begin;
        l->front = front;
        l->pushFront = pushFront;
        l->pushBack = pushBack;
        l->popFront = popFront;
        l->size = size;
    }
    return l;
}

void freeList(List *l) {
    if (l == NULL) {
        return;
    }

    ListNode *next;

    while (l->head != NULL) {
        next = l->head->next;
        l->freeData(l->head->data);
        free(l->head);
        l->head = next;
    }
    free(l);
}
