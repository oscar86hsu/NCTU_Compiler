#include "AST/UnaryOperator.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitUnaryOperatorNode(visitor, (UnaryOperatorNode *)this);
}

static void destruct(AstNode *this) {
    UnaryOperatorNode *node = (UnaryOperatorNode *)this;
    freePType(node->type);
    node->operand->free(node->operand);
    free(node);
}

AstNode *newUnaryOperatorNode(uint32_t line, uint32_t col, Operator op,
                              AstNode *operand) {
    UnaryOperatorNode *node =
        (UnaryOperatorNode *)myMalloc(sizeof(UnaryOperatorNode));
    setExpressionNode((ExpressionNode *)node, line, col, accept, destruct,
                      NULL);
    node->op = op;
    node->operand = operand;

    return (AstNode *)node;
}

void freeUnaryOperatorNode(void *node) { destruct(node); }

void visitChildOfUnaryOperatorNode(UnaryOperatorNode *node,
                                   AstNodeVisitor *visitor) {
    node->operand->accept(node->operand, visitor);
}
