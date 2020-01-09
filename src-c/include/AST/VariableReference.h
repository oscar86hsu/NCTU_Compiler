#ifndef __VARIABLE_REFERENCE_H
#define __VARIABLE_REFERENCE_H

#include "AST/ast.h"
#include "AST/expression.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *ExpressionNodeList;

typedef struct __VariableReferenceNode {
    ANONYMOUS_EXPRESSION_NODE;

    char *name;
    ExpressionNodeList indices;
} VariableReferenceNode;

AstNode *newVariableReferenceNode(uint32_t line, uint32_t col, char *name,
                                  ExpressionNodeList indices);
void freeVariableReferenceNode(void *node);

void visitChildOfVariableReferenceNode(VariableReferenceNode *node,
                                       struct __AstNodeVisitor *visitor);

#endif
