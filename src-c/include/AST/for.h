#ifndef __FOR_H
#define __FOR_H

#include "AST/ast.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *StatementNodeList;

typedef struct __ForNode {
    ANONYMOUS_AST_NODE;

    uint32_t lower_bound;
    uint32_t upper_bound;
    AstNode *loop_var_decl;
    AstNode *initial_statement;
    AstNode *condition;
    StatementNodeList body_statements;
} ForNode;

AstNode *newForNode(uint32_t line, uint32_t col, uint32_t lower_bound,
                    uint32_t upper_bound, AstNode *loop_var_decl,
                    AstNode *initial_statement, AstNode *condition,
                    StatementNodeList body_statements);
void freeForNode(void *node);

void visitChildOfForNode(ForNode *node, struct __AstNodeVisitor *visitor);

#endif
