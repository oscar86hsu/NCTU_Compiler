#include "AST/variable.h"
#include "core/utils.h"
#include "visitor/visitor.h"

#include <stdio.h>

static void accept(AstNode *this, AstNodeVisitor *visitor) {
    visitor->visitConstantValueNode(visitor, (ConstantValueNode *)this);
}

static void destruct(AstNode *this) {
    ConstantValueNode *node = (ConstantValueNode *)this;
    freePType(node->type);
    freeConstant(node->constant);
    free(node);
}

AstNode *newConstantValueNode(uint32_t line, uint32_t col, Constant *constant) {
    ConstantValueNode *node =
        (ConstantValueNode *)myMalloc(sizeof(ConstantValueNode));
    setExpressionNode((ExpressionNode *)node, line, col, accept, destruct,
                      NULL);
    node->constant = NULL;

    if (constant != NULL) {
        node->constant = constant;
        return (AstNode *)node;
    } else {
        freeConstantValueNode(node);
        return NULL;
    }
}

AstNode *copyConstantValueNode(AstNode *node) {
    ConstantValueNode *cvn = (ConstantValueNode *)node;
    if (cvn == NULL) {
        return NULL;
    }
    return newConstantValueNode(cvn->location.line, cvn->location.col,
                                copyConstant(cvn->constant));
}

void freeConstantValueNode(void *node) { destruct(node); }
