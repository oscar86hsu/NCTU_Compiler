#ifndef __CONSTANT_VALUE_NODE_H
#define __CONSTANT_VALUE_NODE_H

#include "AST/ast.h"
#include "AST/expression.h"

struct __AstNodeVisitor;

typedef struct __ConstantValueNode {
    ANONYMOUS_EXPRESSION_NODE;

    Constant *constant;
} ConstantValueNode;

AstNode *newConstantValueNode(uint32_t line, uint32_t col, Constant *constant);
AstNode *copyConstantValueNode(AstNode *node);
void freeConstantValueNode(void *node);

#endif
