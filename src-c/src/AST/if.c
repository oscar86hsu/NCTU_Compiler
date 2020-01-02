#include "AST/if.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitIfNode(visitor, (IfNode *)this);
}

static void destruct(AstNode *this) {
    IfNode *node = (IfNode *)this;
    node->condition->free(node->condition);
    freeList(node->body_statements);
    freeList(node->else_statements);
    free(node);
}

AstNode *newIfNode(uint32_t line, uint32_t col, AstNode *condition,
                   StatementNodeList body_statements,
                   StatementNodeList else_statements) {
    IfNode *node = (IfNode *)myMalloc(sizeof(IfNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->condition = condition;
    node->body_statements =
        (body_statements) ? body_statements : newList((FreeFPtr)freeAstNode);
    node->else_statements =
        (else_statements) ? else_statements : newList((FreeFPtr)freeAstNode);

    return (AstNode *)node;
}

void freeIfNode(void *node) { destruct(node); }

void visitChildOfIfNode(IfNode *node, AstNodeVisitor *visitor) {
    node->condition->accept(node->condition, visitor);
    visitAstNodeList(node->body_statements, visitor);
    visitAstNodeList(node->else_statements, visitor);
}
