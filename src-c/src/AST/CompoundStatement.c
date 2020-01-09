#include "AST/CompoundStatement.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitCompoundStatementNode(visitor, (CompoundStatementNode *)this);
}

static void destruct(AstNode *this) {
    CompoundStatementNode *node = (CompoundStatementNode *)this;
    freeList(node->decls);
    freeList(node->statements);
    free(node);
}

AstNode *newCompoundStatementNode(uint32_t line, uint32_t col,
                                  DeclarationNodeList decls,
                                  StatementNodeList statements) {
    CompoundStatementNode *node =
        (CompoundStatementNode *)myMalloc(sizeof(CompoundStatementNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->decls = (decls) ? decls : newList((FreeFPtr)freeDeclarationNode);
    node->statements =
        (statements) ? statements : newList((FreeFPtr)freeAstNode);

    return (AstNode *)node;
}

void freeCompoundStatementNode(void *node) { destruct(node); }

void visitChildOfCompoundStatementNode(CompoundStatementNode *node,
                                       AstNodeVisitor *visitor) {
    visitAstNodeList(node->decls, visitor);
    visitAstNodeList(node->statements, visitor);
}
