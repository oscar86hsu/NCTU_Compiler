#ifndef __SEMANTIC_ANALYZE_VISITOR_H
#define __SEMANTIC_ANALYZE_VISITOR_H

#include "visitor/visitor.h"

struct __SymbolManager;

typedef struct __List *SemanticContextStack;
typedef struct __List *ReturnTypeStack;

typedef enum __SemanticContext {
    GLOBAL_SEMANTIC_CONTEXT,
    FUNCTION_SEMANTIC_CONTEXT,
    FOR_LOOP_SEMANTIC_CONTEXT,
    LOCAL_SEMANTIC_CONTEXT
} SemanticContext;

typedef struct __SemanticAnalyzeVisitor {
    ANONYMOUS_AST_NODE_VISITOR;

    struct __SymbolManager *symbol_manager;
    ReturnTypeStack ret_type_stack;
    const PType *ret_type;
    SemanticContextStack context_stack;
    SemanticContext semantic_context;

    const char *filename;

    void (*pushContext)(struct __SemanticAnalyzeVisitor *this,
                        SemanticContext sc);
    void (*popContext)(struct __SemanticAnalyzeVisitor *this);
    void (*pushFunction)(struct __SemanticAnalyzeVisitor *this,
                         const PType *ret_type);
    void (*popFunction)(struct __SemanticAnalyzeVisitor *this);
} SemanticAnalyzeVisitor;

AstNodeVisitor *newSemanticAnalyzeVisitor(const char *filename);
void freeSemanticAnalyzeVisitor(SemanticAnalyzeVisitor *sa_visitor);

#endif
