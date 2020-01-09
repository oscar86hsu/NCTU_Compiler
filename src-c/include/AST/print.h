#ifndef __PRINT_H
#define __PRINT_H

#include "AST/ast.h"

#include <stdint.h>

struct __AstNodeVisitor;

typedef struct __PrintNode {
    ANONYMOUS_AST_NODE;

    AstNode *target;
} PrintNode;

AstNode *newPrintNode(uint32_t line, uint32_t col, AstNode *target);
void freePrintNode(void *node);

void visitChildOfPrintNode(PrintNode *node, struct __AstNodeVisitor *visitor);

#endif
