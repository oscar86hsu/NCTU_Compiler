#ifndef __VARIABLE_H
#define __VARIABLE_H

#include "AST/ast.h"

struct __AstNodeVisitor;

typedef struct __VariableNode {
    ANONYMOUS_AST_NODE;

    char *name;
    PType *type;
    AstNode *constant;
} VariableNode;

AstNode *newVariableNode(uint32_t line, uint32_t col, char *name, PType *type,
                         AstNode *constant);
void freeVariableNode(void *node);

void visitChildOfVariableNode(VariableNode *node,
                              struct __AstNodeVisitor *visitor);

#endif
