#include "AST/for.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitForNode(visitor, (ForNode *)this);
}

static void destruct(AstNode *this) {
    ForNode *node = (ForNode *)this;
    node->loop_var_decl->free(node->loop_var_decl);
    node->initial_statement->free(node->initial_statement);
    node->condition->free(node->condition);
    freeList(node->body_statements);
    free(node);
}

AstNode *newForNode(uint32_t line, uint32_t col, uint32_t lower_bound,
                    uint32_t upper_bound, AstNode *loop_var_decl,
                    AstNode *initial_statement, AstNode *condition,
                    StatementNodeList body_statements) {
    ForNode *node = (ForNode *)myMalloc(sizeof(ForNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->lower_bound = lower_bound;
    node->upper_bound = upper_bound;
    node->loop_var_decl = loop_var_decl;
    node->initial_statement = initial_statement;
    node->condition = condition;
    node->body_statements =
        (body_statements) ? body_statements : newList((FreeFPtr)freeAstNode);

    return (AstNode *)node;
}

void freeForNode(void *node) { destruct(node); }

void visitChildOfForNode(ForNode *node, AstNodeVisitor *visitor) {
    node->loop_var_decl->accept(node->loop_var_decl, visitor);
    node->initial_statement->accept(node->initial_statement, visitor);
    node->condition->accept(node->condition, visitor);
    visitAstNodeList(node->body_statements, visitor);
}
