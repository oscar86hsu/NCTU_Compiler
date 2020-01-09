#include "AST/function.h"
#include "AST/CompoundStatement.h"
#include "core/list.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitFunctionNode(visitor, (FunctionNode *)this);
}

static void destruct(AstNode *this) {
    FunctionNode *node = (FunctionNode *)this;
    free(node->name);
    freeList(node->parameters);
    freePType(node->type);
    node->body->free((AstNode *)node->body);
    free(node->end_name);
    free(node);
}

AstNode *newFunctionNode(uint32_t line, uint32_t col, char *name,
                         DeclarationNodeList parameters, PType *type,
                         CompoundStatementNode *body, uint32_t end_name_line,
                         uint32_t end_name_col, char *end_name) {
    FunctionNode *node = (FunctionNode *)myMalloc(sizeof(FunctionNode));
    setAstNode((AstNode *)node, line, col, accept, destruct);
    node->name = name;
    node->parameters =
        (parameters) ? parameters : newList((FreeFPtr)freeDeclarationNode);
    node->type = type;
    node->body = body;
    node->end_name_location.line = end_name_line;
    node->end_name_location.col = end_name_col;
    node->end_name = end_name;

    return (AstNode *)node;
}

void freeFunctionNode(void *node) { destruct(node); }

const char *getParametersTypeString(DeclarationNodeList parameters) {
    const static size_t kParametersBufferSize = 2048u;
    static char buffer[kParametersBufferSize];

    if (parameters->size(parameters) == 0u) {
        return "";
    }

    int position = 0;
    ListNode *decl_node;
    LIST_FOR_EACH(decl_node, parameters->begin(parameters)) {
        if (position >= kParametersBufferSize - 1u) {
            break;
        }

        DeclarationNode *decl = DEREF_LIST_NODE(decl_node);
        ListNode *var_node;
        LIST_FOR_EACH(var_node, decl->vars->begin(decl->vars)) {
            if (position >= kParametersBufferSize - 1u) {
                break;
            }

            VariableNode *var = DEREF_LIST_NODE(var_node);
            position += snprintf(
                buffer + position, kParametersBufferSize - position, "%s, ",
                var->type->getPTypeString(var->type, /* compactOrNot */ true));
        }
    }

    // Discard the last ", "
    buffer[position - 2] = '\0';

    return buffer;
}

void visitChildOfFunctionNode(FunctionNode *node, AstNodeVisitor *visitor) {
    visitAstNodeList(node->parameters, visitor);
    node->body->accept((AstNode *)node->body, visitor);
}
