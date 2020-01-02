#include "AST/program.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitProgramNode(visitor, (ProgramNode *)this);
}

static void destruct(AstNode *this) {
    ProgramNode *node = (ProgramNode *)this;
    freePType(node->type);
    free(node->name);
    freeList(node->var_decls);
    freeList(node->func_decls);
    node->body->free(node->body);
    free(node->end_name);
    free(node);
}

AstNode *newProgramNode(uint32_t line, uint32_t col, PType *type, char *name,
                        DeclarationNodeList var_decls,
                        FunctionNodeList func_decls, AstNode *body,
                        uint32_t end_name_line, uint32_t end_name_col,
                        char *end_name) {
    ProgramNode *node = (ProgramNode *)myMalloc(sizeof(ProgramNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->type = type;
    node->name = name;
    node->var_decls =
        (var_decls) ? var_decls : newList((FreeFPtr)freeDeclarationNode);
    node->func_decls =
        (func_decls) ? func_decls : newList((FreeFPtr)freeFunctionNode);
    node->body = body;
    node->end_name_location.line = end_name_line;
    node->end_name_location.col = end_name_col;
    node->end_name = end_name;

    return (AstNode *)node;
}

void freeProgramNode(void *node) { destruct(node); }

void visitChildOfProgramNode(ProgramNode *node, AstNodeVisitor *visitor) {
    visitAstNodeList(node->var_decls, visitor);
    visitAstNodeList(node->func_decls, visitor);
    node->body->accept(node->body, visitor);
}
