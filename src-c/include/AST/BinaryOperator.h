#ifndef __BINARY_OPERATOR_H
#define __BINARY_OPERATOR_H

#include "AST/ast.h"
#include "AST/expression.h"

#include <stdint.h>

struct __AstNodeVisitor;

typedef struct __BinaryOperatorNode {
    ANONYMOUS_EXPRESSION_NODE;

    Operator op;
    AstNode *left;
    AstNode *right;
} BinaryOperatorNode;

AstNode *newBinaryOperatorNode(uint32_t line, uint32_t col, Operator op,
                               AstNode *left, AstNode *right);
void freeBinaryOperatorNode(void *node);

void visitChildOfBinaryOperatorNode(BinaryOperatorNode *node,
                                    struct __AstNodeVisitor *visitor);

#endif
