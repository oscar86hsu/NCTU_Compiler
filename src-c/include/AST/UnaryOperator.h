#ifndef __UnaryOperator_H
#define __UnaryOperator_H

#include "AST/ast.h"
#include "AST/expression.h"

#include <stdint.h>

struct __AstNodeVisitor;

typedef struct __UnaryOperatorNode {
    ANONYMOUS_EXPRESSION_NODE;

    Operator op;
    AstNode *operand;
} UnaryOperatorNode;

AstNode *newUnaryOperatorNode(uint32_t line, uint32_t col, Operator op,
                              AstNode *operand);
void freeUnaryOperatorNode(void *node);

void visitChildOfUnaryOperatorNode(UnaryOperatorNode *node,
                                   struct __AstNodeVisitor *visitor);

#endif
