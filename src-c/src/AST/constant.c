#include "AST/constant.h"
#include "core/utils.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern const char *kTFString[]; // from ast.c

static const size_t kBufferSize = 1024;

static PrimitiveType getPrimitiveType(const Constant *this) {
    return this->ptype->getPrimitiveType(this->ptype);
}

static const char *getConstantValueString(const Constant *this) {
    static char buffer[kBufferSize];

    switch (this->ptype->getPrimitiveType(this->ptype)) {
    case INTEGER_TYPE:
        snprintf(buffer, kBufferSize, "%d", this->value.integer);
        break;
    case REAL_TYPE:
        snprintf(buffer, kBufferSize, "%f", this->value.real);
        break;
    case BOOL_TYPE:
        snprintf(buffer, kBufferSize, "%s", kTFString[this->value.boolean]);
        break;
    case STRING_TYPE:
        snprintf(buffer, kBufferSize, "\"%s\"", this->value.string);
        break;
    case VOID_TYPE:
    default:
        snprintf(buffer, 1, "");
        break;
    }

    return buffer;
}

Constant *newConstant(PType *type, union ConstantValue value) {
    Constant *constant = (Constant *)myMalloc(sizeof(Constant));
    constant->ptype = type;
    constant->value = value;
    constant->getPrimitiveType = getPrimitiveType;
    constant->getConstantValueString = getConstantValueString;
    return constant;
}

void freeConstant(Constant *constant) {
    if (constant == NULL) {
        return;
    }

    if (constant->ptype->type == STRING_TYPE) {
        free(constant->value.string);
    }
    freePType(constant->ptype);
    free(constant);
}

Constant *copyConstant(const Constant *constant) {
    if (constant == NULL) {
        return NULL;
    }

    union ConstantValue value;
    if (constant->ptype->type == STRING_TYPE) {
        value.string = strdup(constant->value.string);
    } else {
        value = constant->value;
    }
    return newConstant(copyPType(constant->ptype), value);
}
