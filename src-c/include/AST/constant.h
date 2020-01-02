#ifndef __CONSTANT_H
#define __CONSTANT_H

#include "AST/PType.h"

#include <stdint.h>

typedef struct __Constant {
    PType *ptype;
    union ConstantValue {
        int32_t integer;
        double real;
        bool boolean;
        char *string;
    } value;

    PrimitiveType (*getPrimitiveType)(const struct __Constant *);
    const char *(*getConstantValueString)(const struct __Constant *);
    // TODO: compare type with another constant object
} Constant;

Constant *newConstant(PType *, union ConstantValue);
void freeConstant(Constant *);
Constant *copyConstant(const Constant *);

#endif
