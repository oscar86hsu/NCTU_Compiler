#ifndef __VISITOR_H
#define __VISITOR_H

#include "AST/BinaryOperator.h"
#include "AST/CompoundStatement.h"
#include "AST/ConstantValue.h"
#include "AST/FunctionCall.h"
#include "AST/UnaryOperator.h"
#include "AST/VariableReference.h"
#include "AST/assignment.h"
#include "AST/ast.h"
#include "AST/declaration.h"
#include "AST/for.h"
#include "AST/function.h"
#include "AST/if.h"
#include "AST/print.h"
#include "AST/program.h"
#include "AST/read.h"
#include "AST/return.h"
#include "AST/variable.h"
#include "AST/while.h"

#include <stdlib.h>

#define AST_NODE_VISITOR_MEMBERS                                               \
    void (*visitProgramNode)(struct __AstNodeVisitor * this,                   \
                             ProgramNode * node);                              \
    void (*visitDeclarationNode)(struct __AstNodeVisitor * this,               \
                                 DeclarationNode * node);                      \
    void (*visitVariableNode)(struct __AstNodeVisitor * this,                  \
                              VariableNode * node);                            \
    void (*visitConstantValueNode)(struct __AstNodeVisitor * this,             \
                                   ConstantValueNode * node);                  \
    void (*visitFunctionNode)(struct __AstNodeVisitor * this,                  \
                              FunctionNode * node);                            \
    void (*visitCompoundStatementNode)(struct __AstNodeVisitor * this,         \
                                       CompoundStatementNode * node);          \
    void (*visitAssignmentNode)(struct __AstNodeVisitor * this,                \
                                AssignmentNode * node);                        \
    void (*visitPrintNode)(struct __AstNodeVisitor * this, PrintNode * node);  \
    void (*visitReadNode)(struct __AstNodeVisitor * this, ReadNode * node);    \
    void (*visitVariableReferenceNode)(struct __AstNodeVisitor * this,         \
                                       VariableReferenceNode * node);          \
    void (*visitBinaryOperatorNode)(struct __AstNodeVisitor * this,            \
                                    BinaryOperatorNode * node);                \
    void (*visitUnaryOperatorNode)(struct __AstNodeVisitor * this,             \
                                   UnaryOperatorNode * node);                  \
    void (*visitIfNode)(struct __AstNodeVisitor * this, IfNode * node);        \
    void (*visitWhileNode)(struct __AstNodeVisitor * this, WhileNode * node);  \
    void (*visitForNode)(struct __AstNodeVisitor * this, ForNode * node);      \
    void (*visitReturnNode)(struct __AstNodeVisitor * this,                    \
                            ReturnNode * node);                                \
    void (*visitFunctionCallNode)(struct __AstNodeVisitor * this,              \
                                  FunctionCallNode * node)

#define ANONYMOUS_AST_NODE_VISITOR                                             \
    struct {                                                                   \
        AST_NODE_VISITOR_MEMBERS;                                              \
    }

// clang-format off
#define CONSTRUCT_VISITOR(visitor, action)                                     \
    visitor->visitProgramNode           = action ## ProgramNode;               \
    visitor->visitDeclarationNode       = action ## DeclarationNode;           \
    visitor->visitVariableNode          = action ## VariableNode;              \
    visitor->visitConstantValueNode     = action ## ConstantValueNode;         \
    visitor->visitFunctionNode          = action ## FunctionNode;              \
    visitor->visitCompoundStatementNode = action ## CompoundStatementNode;     \
    visitor->visitAssignmentNode        = action ## AssignmentNode;            \
    visitor->visitPrintNode             = action ## PrintNode;                 \
    visitor->visitReadNode              = action ## ReadNode;                  \
    visitor->visitVariableReferenceNode = action ## VariableReferenceNode;     \
    visitor->visitBinaryOperatorNode    = action ## BinaryOperatorNode;        \
    visitor->visitUnaryOperatorNode     = action ## UnaryOperatorNode;         \
    visitor->visitIfNode                = action ## IfNode;                    \
    visitor->visitWhileNode             = action ## WhileNode;                 \
    visitor->visitForNode               = action ## ForNode;                   \
    visitor->visitReturnNode            = action ## ReturnNode;                \
    visitor->visitFunctionCallNode      = action ## FunctionCallNode
// clang-format on

struct __List;

typedef struct __AstNodeVisitor {
    ANONYMOUS_AST_NODE_VISITOR;
} AstNodeVisitor;

void visitAstNodeList(struct __List *list, AstNodeVisitor *visitor);

#endif
