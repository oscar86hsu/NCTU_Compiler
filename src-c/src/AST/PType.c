#include "AST/PType.h"
#include "core/list.h"
#include "core/utils.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const size_t kBufferSize = 1024;
const char *kTypeString[] = {"void", "integer", "real", "boolean", "string"};

static void setDimensions(PType *this, List *dims) {
    freeList(this->dimensions);
    this->dimensions = dims;
}

static PrimitiveType getPrimitiveType(const PType *this) { return this->type; }

static int writeOriginalPTypeDimensionString(char *buffer, size_t size,
                                             const Dimension *dim) {
    return snprintf(buffer, size, "[%ld...%ld]", dim->lower_bound,
                    dim->upper_bound);
}

static int writeCompactPTypeDimensionString(char *buffer, size_t size,
                                            const Dimension *dim) {
    return snprintf(buffer, size, "[%ld]", dim->upper_bound - dim->lower_bound);
}

static const char *getPTypeString(const PType *this, bool compactOrNot) {
    static char buffer[kBufferSize];

    if (this->type_string != NULL) {
        return this->type_string;
    }

    int position = snprintf(buffer, kBufferSize, "%s", kTypeString[this->type]);

    if (this->dimensions->size(this->dimensions) != 0u) {
        position += snprintf(buffer + position, kBufferSize - position, " ");

        int (*writePTypeString)(char *, size_t, const Dimension *);

        if (compactOrNot) {
            writePTypeString = writeCompactPTypeDimensionString;
        } else {
            writePTypeString = writeOriginalPTypeDimensionString;
        }

        ListNode *node;
        LIST_FOR_EACH(node, this->dimensions->begin(this->dimensions)) {
            if (position >= kBufferSize - 1u) {
                break;
            }

            Dimension *dimension = DEREF_LIST_NODE(node);
            position += writePTypeString(buffer + position,
                                         kBufferSize - position, dimension);
        }
    }

    ((PType *)this)->type_string = strndup(buffer, kBufferSize);
    return this->type_string;
}

static bool isVoid(const PType *this) { return this->type == VOID_TYPE; }

static bool isInteger(const PType *this) {
    return (this->type == INTEGER_TYPE &&
            this->dimensions->size(this->dimensions) == 0u);
}

static bool isReal(const PType *this) {
    return (this->type == REAL_TYPE &&
            this->dimensions->size(this->dimensions) == 0u);
}

static bool isBool(const PType *this) {
    return (this->type == BOOL_TYPE &&
            this->dimensions->size(this->dimensions) == 0u);
}

static bool isString(const PType *this) {
    return (this->type == STRING_TYPE &&
            this->dimensions->size(this->dimensions) == 0u);
}

static bool isScalar(const PType *this) {
    return this->type != VOID_TYPE &&
           this->dimensions->size(this->dimensions) == 0u;
}

static bool compare(const PType *this, const PType *ptype) {
    // See if basic type is different
    if (this->type != ptype->type &&
        !(this->type == INTEGER_TYPE && ptype->type == REAL_TYPE) &&
        !(this->type == REAL_TYPE && ptype->type == INTEGER_TYPE)) {
        return false;
    }

    // See if both of them are scalar
    if (this->dimensions->size(this->dimensions) == 0 &&
        ptype->dimensions->size(ptype->dimensions) == 0) {
        return true;
    }

    if (this->dimensions->size(this->dimensions) !=
        ptype->dimensions->size(ptype->dimensions)) {
        return false;
    }

    ListNode *dim1_node;
    ListNode *dim2_node = ptype->dimensions->begin(ptype->dimensions);
    LIST_FOR_EACH(dim1_node, this->dimensions->begin(this->dimensions)) {
        Dimension *dim1 = DEREF_LIST_NODE(dim1_node);
        Dimension *dim2 = DEREF_LIST_NODE(dim2_node);
        if ((dim1->upper_bound - dim1->lower_bound) !=
            (dim2->upper_bound - dim2->lower_bound)) {
            return false;
        }
        ITER_NEXT_LIST_NODE(dim2_node);
    }
    return true;
}

PType *newPType(PrimitiveType type) {
    PType *p = (PType *)myMalloc(sizeof(PType));
    p->type = type;
    p->dimensions = newList(free);
    p->type_string = NULL;
    p->setDimensions = setDimensions;
    p->getPrimitiveType = getPrimitiveType;
    p->getPTypeString = getPTypeString;
    p->isVoid = isVoid;
    p->isInteger = isInteger;
    p->isReal = isReal;
    p->isBool = isBool;
    p->isString = isString;
    p->isScalar = isScalar;
    p->compare = compare;
    return p;
}

void freePType(PType *ptype) {
    if (ptype == NULL) {
        return;
    }

    freeList(ptype->dimensions);
    free(ptype->type_string);
    free(ptype);
}

PType *copyPType(const PType *ptype) {
    PType *p = newPType(ptype->type);

    p->dimensions = newList(free);

    ListNode *node;
    LIST_FOR_EACH(node, ptype->dimensions->begin(ptype->dimensions)) {
        Dimension *dimension = DEREF_LIST_NODE(node);
        concatenateDimensions(p->dimensions, dimension->lower_bound,
                              dimension->upper_bound);
    }
    return p;
}

void concatenateDimensions(List *list, int64_t lower_bound,
                           int64_t upper_bound) {
    Dimension *dimension = (Dimension *)myMalloc(sizeof(Dimension));
    dimension->lower_bound = lower_bound;
    dimension->upper_bound = upper_bound;
    list->pushBack(list, dimension);
}
