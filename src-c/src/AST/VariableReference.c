#include "AST/VariableReference.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitVariableReferenceNode(visitor, (VariableReferenceNode *)this);
}

static void destruct(AstNode *this) {
    VariableReferenceNode *node = (VariableReferenceNode *)this;
    freePType(node->type);
    free(node->name);
    freeList(node->indices);
    free(node);
}

AstNode *newVariableReferenceNode(uint32_t line, uint32_t col, char *name,
                                  ExpressionNodeList indices) {
    VariableReferenceNode *node =
        (VariableReferenceNode *)myMalloc(sizeof(VariableReferenceNode));
    setExpressionNode((ExpressionNode *)node, line, col, accept, destruct,
                      NULL);
    node->name = name;
    node->indices = (indices) ? indices : newList((FreeFPtr)freeAstNode);

    return (AstNode *)node;
}

void freeVariableReferenceNode(void *node) { destruct(node); }

void visitChildOfVariableReferenceNode(VariableReferenceNode *node,
                                       AstNodeVisitor *visitor) {
    visitAstNodeList(node->indices, visitor);
}
