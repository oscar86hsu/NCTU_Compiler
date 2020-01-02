#include "AST/read.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitReadNode(visitor, (ReadNode *)this);
}

static void destruct(AstNode *this) {
    ReadNode *node = (ReadNode *)this;
    node->target->free(node->target);
    free(node);
}

AstNode *newReadNode(uint32_t line, uint32_t col, AstNode *target) {
    ReadNode *node = (ReadNode *)myMalloc(sizeof(ReadNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->target = target;

    return (AstNode *)node;
}

void freeReadNode(void *node) { destruct(node); }

void visitChildOfReadNode(ReadNode *node, AstNodeVisitor *visitor) {
    node->target->accept(node->target, visitor);
}
