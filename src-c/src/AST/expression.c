#include "AST/expression.h"

void setExpressionNode(ExpressionNode *node, uint32_t line, uint32_t col,
                       AcceptFPtr accept, DestructFPtr free, PType *type) {
    setAstNode((AstNode *)node, line, col, accept, free);
    node->type = type;
}
