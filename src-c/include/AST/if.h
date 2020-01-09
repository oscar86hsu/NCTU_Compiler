#ifndef __IF_H
#define __IF_H

#include "AST/ast.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *StatementNodeList;

typedef struct __IfNode {
    ANONYMOUS_AST_NODE;

    AstNode *condition;
    StatementNodeList body_statements;
    StatementNodeList else_statements;
} IfNode;

AstNode *newIfNode(uint32_t line, uint32_t col, AstNode *condition,
                   StatementNodeList body_statements,
                   StatementNodeList else_statements);
void freeIfNode(void *node);

void visitChildOfIfNode(IfNode *node, struct __AstNodeVisitor *visitor);

#endif
