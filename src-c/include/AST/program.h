#ifndef __PROGRAM_H
#define __PROGRAM_H

#include "AST/ast.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *DeclarationNodeList;
typedef struct __List *FunctionNodeList;

typedef struct __ProgramNode {
    ANONYMOUS_AST_NODE;

    PType *type;
    char *name;
    DeclarationNodeList var_decls;
    FunctionNodeList func_decls;
    AstNode *body;
    Location end_name_location;
    char *end_name;
} ProgramNode;

AstNode *newProgramNode(uint32_t line, uint32_t col, PType *type, char *name,
                        DeclarationNodeList var_decls,
                        FunctionNodeList func_decls, AstNode *body,
                        uint32_t end_name_line, uint32_t end_name_col,
                        char *end_name);
void freeProgramNode(void *node);

void visitChildOfProgramNode(ProgramNode *node,
                             struct __AstNodeVisitor *visitor);

#endif
