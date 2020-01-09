#ifndef __COMPOUND_STATEMENT_H
#define __COMPOUND_STATEMENT_H

#include "AST/ast.h"

#include <stdint.h>

struct __List;
struct __AstNodeVisitor;

typedef struct __List *DeclarationNodeList;
typedef struct __List *StatementNodeList;

typedef struct __CompoundStatementNode {
    ANONYMOUS_AST_NODE;

    DeclarationNodeList decls;
    StatementNodeList statements;
} CompoundStatementNode;

AstNode *newCompoundStatementNode(uint32_t line, uint32_t col,
                                  DeclarationNodeList decls,
                                  StatementNodeList statements);
void freeCompoundStatementNode(void *node);

void visitChildOfCompoundStatementNode(CompoundStatementNode *node,
                                       struct __AstNodeVisitor *visitor);

#endif
