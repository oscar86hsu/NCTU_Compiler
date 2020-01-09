#include "AST/FunctionCall.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitFunctionCallNode(visitor, (FunctionCallNode *)this);
}

static void destruct(AstNode *this) {
    FunctionCallNode *node = (FunctionCallNode *)this;
    freePType(node->type);
    free(node->name);
    freeList(node->args);
    free(node);
}

AstNode *newFunctionCallNode(uint32_t line, uint32_t col, char *name,
                             ExpressionNodeList args) {
    FunctionCallNode *node =
        (FunctionCallNode *)myMalloc(sizeof(FunctionCallNode));
    setExpressionNode((ExpressionNode *)node, line, col, accept, destruct,
                      NULL);
    node->name = name;
    node->args = (args) ? args : newList((FreeFPtr)freeAstNode);

    return (AstNode *)node;
}

void freeFunctionCallNode(void *node) { destruct(node); }

void visitChildOfFunctionCallNode(FunctionCallNode *node,
                                  AstNodeVisitor *visitor) {
    visitAstNodeList(node->args, visitor);
}
