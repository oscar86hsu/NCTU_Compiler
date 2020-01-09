#ifndef __P_TYPE_H
#define __P_TYPE_H

#include <stdbool.h>
#include <stdint.h>

struct __List;

extern const char *kTypeString[];

typedef enum __PrimitiveType {
    VOID_TYPE,
    INTEGER_TYPE,
    REAL_TYPE,
    BOOL_TYPE,
    STRING_TYPE
} PrimitiveType;

typedef struct __Dimension {
    int64_t lower_bound;
    int64_t upper_bound;
} Dimension;

typedef struct __PType {
    PrimitiveType type;
    struct __List *dimensions;
    // mutable
    char *type_string;

    void (*setDimensions)(struct __PType *this, struct __List *dimensions);
    PrimitiveType (*getPrimitiveType)(const struct __PType *this);

    // Logical constness, it may construct the string at the first call, but it
    // does not affect the status of object (changing the type or dimensions)
    const char *(*getPTypeString)(const struct __PType *this,
                                  bool compactOrNot);

    bool (*isVoid)(const struct __PType *this);
    bool (*isInteger)(const struct __PType *this);
    bool (*isReal)(const struct __PType *this);
    bool (*isBool)(const struct __PType *this);
    bool (*isString)(const struct __PType *this);
    bool (*isScalar)(const struct __PType *this);
    bool (*compare)(const struct __PType *this, const struct __PType *ptype);
} PType;

PType *newPType(PrimitiveType);
void freePType(PType *);
PType *copyPType(const PType *type);

void concatenateDimensions(struct __List *, int64_t, int64_t);

#endif
