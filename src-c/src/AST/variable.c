#include "AST/variable.h"
#include "AST/ConstantValue.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitVariableNode(visitor, (VariableNode *)this);
}

static void destruct(AstNode *this) {
    VariableNode *node = (VariableNode *)this;
    free(node->name);
    freePType(node->type);
    if (node->constant) {
        node->constant->free(node->constant);
    }
    free(node);
}

AstNode *newVariableNode(uint32_t line, uint32_t col, char *name, PType *type,
                         AstNode *constant) {
    VariableNode *node = (VariableNode *)myMalloc(sizeof(VariableNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->name = name;
    node->type = type;
    node->constant = constant;
    return (AstNode *)node;
}

void freeVariableNode(void *node) { destruct(node); }

void visitChildOfVariableNode(VariableNode *node, AstNodeVisitor *visitor) {
    if (node->constant) {
        node->constant->accept(node->constant, visitor);
    }
}
