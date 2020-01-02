#ifndef __FUNCTION_CALL_H
#define __FUNCTION_CALL_H

#include "AST/ast.h"
#include "AST/expression.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *ExpressionNodeList;

typedef struct __FunctionCallNode {
    ANONYMOUS_EXPRESSION_NODE;

    char *name;
    ExpressionNodeList args;
} FunctionCallNode;

AstNode *newFunctionCallNode(uint32_t line, uint32_t col, char *name,
                             ExpressionNodeList args);
void freeFunctionCallNode(void *node);

void visitChildOfFunctionCallNode(FunctionCallNode *node,
                                  struct __AstNodeVisitor *visitor);

#endif
