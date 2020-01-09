#include "AST/return.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitReturnNode(visitor, (ReturnNode *)this);
}

static void destruct(AstNode *this) {
    ReturnNode *node = (ReturnNode *)this;
    node->retval->free(node->retval);
    free(node);
}

AstNode *newReturnNode(uint32_t line, uint32_t col, AstNode *retval) {
    ReturnNode *node = (ReturnNode *)myMalloc(sizeof(ReturnNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->retval = retval;

    return (AstNode *)node;
}

void freeReturnNode(void *node) { destruct(node); }

void visitChildOfReturnNode(ReturnNode *node, AstNodeVisitor *visitor) {
    node->retval->accept(node->retval, visitor);
}
