#ifndef __EXPRESSION_H
#define __EXPRESSION_H

#include "AST/ast.h"

#define EXPRESSION_NODE_MEMBERS                                                \
    ANONYMOUS_AST_NODE;                                                        \
    PType *type

#define ANONYMOUS_EXPRESSION_NODE                                              \
    struct {                                                                   \
        EXPRESSION_NODE_MEMBERS;                                               \
    }

struct __ExpressionNode;

typedef struct __ExpressionNode {
    EXPRESSION_NODE_MEMBERS;
} ExpressionNode;

void setExpressionNode(ExpressionNode *node, uint32_t line, uint32_t col,
                       AcceptFPtr accept, DestructFPtr free, PType *type);

#endif
