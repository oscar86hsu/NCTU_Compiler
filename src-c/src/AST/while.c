#include "AST/while.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitWhileNode(visitor, (WhileNode *)this);
}

static void destruct(AstNode *this) {
    WhileNode *node = (WhileNode *)this;
    node->condition->free(node->condition);
    freeList(node->body_statements);
    free(node);
}

AstNode *newWhileNode(uint32_t line, uint32_t col, AstNode *condition,
                      StatementNodeList body_statements) {
    WhileNode *node = (WhileNode *)myMalloc(sizeof(WhileNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->condition = condition;
    node->body_statements =
        (body_statements) ? body_statements : newList((FreeFPtr)freeAstNode);

    return (AstNode *)node;
}

void freeWhileNode(void *node) { destruct(node); }

void visitChildOfWhileNode(WhileNode *node, AstNodeVisitor *visitor) {
    node->condition->accept(node->condition, visitor);
    visitAstNodeList(node->body_statements, visitor);
}
