#ifndef __WHILE_H
#define __WHILE_H

#include "AST/ast.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *StatementNodeList;

typedef struct __WhileNode {
    ANONYMOUS_AST_NODE;

    AstNode *condition;
    StatementNodeList body_statements;
} WhileNode;

AstNode *newWhileNode(uint32_t line, uint32_t col, AstNode *condition,
                      StatementNodeList body_statements);
void freeWhileNode(void *node);

void visitChildOfWhileNode(WhileNode *node, struct __AstNodeVisitor *visitor);

#endif
