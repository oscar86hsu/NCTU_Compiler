#ifndef __RETURN_H
#define __RETURN_H

#include "AST/ast.h"

#include <stdint.h>

struct __AstNodeVisitor;

typedef struct __ReturnNode {
    ANONYMOUS_AST_NODE;

    AstNode *retval;
} ReturnNode;

AstNode *newReturnNode(uint32_t line, uint32_t col, AstNode *retval);
void freeReturnNode(void *node);

void visitChildOfReturnNode(ReturnNode *node, struct __AstNodeVisitor *visitor);

#endif
