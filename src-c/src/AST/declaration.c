#include "AST/declaration.h"
#include "AST/variable.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdarg.h>
#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitDeclarationNode(visitor, (DeclarationNode *)this);
}

static void destruct(AstNode *this) {
    DeclarationNode *node = (DeclarationNode *)this;
    freeList(node->vars);
    free(node);
}

AstNode *newDeclarationNode(uint32_t line, uint32_t col,
                            VariableNodeList vars) {
    DeclarationNode *node =
        (DeclarationNode *)myMalloc(sizeof(DeclarationNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->vars = vars;

    return (AstNode *)node;
}

void freeDeclarationNode(void *node) { destruct(node); }

void visitChildOfDeclarationNode(DeclarationNode *node,
                                 AstNodeVisitor *visitor) {
    visitAstNodeList(node->vars, visitor);
}
