#include "AST/assignment.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitAssignmentNode(visitor, (AssignmentNode *)this);
}

static void destruct(AstNode *this) {
    AssignmentNode *node = (AssignmentNode *)this;
    node->lvalue->free(node->lvalue);
    node->expr->free(node->expr);
    free(node);
}

AstNode *newAssignmentNode(uint32_t line, uint32_t col, AstNode *lvalue,
                           AstNode *expr) {
    AssignmentNode *node = (AssignmentNode *)myMalloc(sizeof(AssignmentNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->lvalue = lvalue;
    node->expr = expr;

    return (AstNode *)node;
}

void freeAssignmentNode(void *node) { destruct(node); }

void visitChildOfAssignmentNode(AssignmentNode *node, AstNodeVisitor *visitor) {
    node->lvalue->accept(node->lvalue, visitor);
    node->expr->accept(node->expr, visitor);
}
