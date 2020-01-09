#include "AST/print.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitPrintNode(visitor, (PrintNode *)this);
}

static void destruct(AstNode *this) {
    PrintNode *node = (PrintNode *)this;
    node->target->free(node->target);
    free(node);
}

AstNode *newPrintNode(uint32_t line, uint32_t col, AstNode *target) {
    PrintNode *node = (PrintNode *)myMalloc(sizeof(PrintNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->target = target;

    return (AstNode *)node;
}

void freePrintNode(void *node) { destruct(node); }

void visitChildOfPrintNode(PrintNode *node, AstNodeVisitor *visitor) {
    node->target->accept(node->target, visitor);
}
