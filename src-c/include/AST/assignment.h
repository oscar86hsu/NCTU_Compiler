#ifndef __ASSIGNMENT_H
#define __ASSIGNMENT_H

#include "AST/ast.h"

#include <stdint.h>

struct __AstNodeVisitor;

typedef struct __AssignmentNode {
    ANONYMOUS_AST_NODE;

    AstNode *lvalue;
    AstNode *expr;
} AssignmentNode;

AstNode *newAssignmentNode(uint32_t line, uint32_t col, AstNode *lvalue,
                           AstNode *expr);
void freeAssignmentNode(void *node);

void visitChildOfAssignmentNode(AssignmentNode *node,
                                struct __AstNodeVisitor *visitor);

#endif
