#ifndef __READ_H
#define __READ_H

#include "AST/ast.h"

#include <stdint.h>

struct __AstNodeVisitor;

typedef struct __ReadNode {
    ANONYMOUS_AST_NODE;

    AstNode *target;
} ReadNode;

AstNode *newReadNode(uint32_t line, uint32_t col, AstNode *target);
void freeReadNode(void *node);

void visitChildOfReadNode(ReadNode *node, struct __AstNodeVisitor *visitor);

#endif
