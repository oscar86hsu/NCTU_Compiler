#include "AST/BinaryOperator.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitBinaryOperatorNode(visitor, (BinaryOperatorNode *)this);
}

static void destruct(AstNode *this) {
    BinaryOperatorNode *node = (BinaryOperatorNode *)this;
    freePType(node->type);
    node->left->free(node->left);
    node->right->free(node->right);
    free(node);
}

AstNode *newBinaryOperatorNode(uint32_t line, uint32_t col, Operator op,
                               AstNode *left, AstNode *right) {
    BinaryOperatorNode *node =
        (BinaryOperatorNode *)myMalloc(sizeof(BinaryOperatorNode));
    setExpressionNode((ExpressionNode *)node, line, col, accept, destruct,
                      NULL);
    node->op = op;
    node->left = left;
    node->right = right;

    return (AstNode *)node;
}

void freeBinaryOperatorNode(void *node) { destruct(node); }

void visitChildOfBinaryOperatorNode(BinaryOperatorNode *node,
                                    AstNodeVisitor *visitor) {
    node->left->accept(node->left, visitor);
    node->right->accept(node->right, visitor);
}
