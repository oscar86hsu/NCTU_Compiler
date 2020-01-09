#ifndef __AST_DUMPER_H
#define __AST_DUMPER_H

#include "visitor/visitor.h"

typedef struct __ASTDumper {
    ANONYMOUS_AST_NODE_VISITOR;
} ASTDumper;

AstNodeVisitor *newASTDumper(void);
void freeASTDumper(void *ad);

#endif
