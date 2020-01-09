#ifndef __FUNCTION_H
#define __FUNCTION_H

#include "AST/ast.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;
struct __CompoundStatementNode;

typedef struct __List *DeclarationNodeList;

typedef struct __FunctionNode {
    ANONYMOUS_AST_NODE;

    char *name;
    // List of DeclarationNodes
    DeclarationNodeList parameters;
    PType *type;
    struct __CompoundStatementNode *body;
    Location end_name_location;
    char *end_name;
} FunctionNode;

AstNode *newFunctionNode(uint32_t line, uint32_t col, char *name,
                         DeclarationNodeList parameters, PType *type,
                         struct __CompoundStatementNode *body,
                         uint32_t end_name_line, uint32_t end_name_col,
                         char *end_name);
void freeFunctionNode(void *node);

const char *getParametersTypeString(DeclarationNodeList parameters);
void visitChildOfFunctionNode(FunctionNode *node,
                              struct __AstNodeVisitor *visitor);

#endif
