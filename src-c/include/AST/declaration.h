#ifndef __DECLARATION_H
#define __DECLARATION_H

#include "AST/ast.h"

struct __List;
struct __AstNodeVisitor;

typedef struct __List *VariableNodeList;

typedef struct __DeclarationNode {
    ANONYMOUS_AST_NODE;

    VariableNodeList vars;
} DeclarationNode;

AstNode *newDeclarationNode(uint32_t line, uint32_t col, VariableNodeList vars);
void freeDeclarationNode(void *node);

void visitChildOfDeclarationNode(DeclarationNode *node,
                                 struct __AstNodeVisitor *visitor);

#endif
