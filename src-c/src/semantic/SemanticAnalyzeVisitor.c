#include "semantic/SemanticAnalyzeVisitor.h"
#include "core/error.h"
#include "core/list.h"
#include "core/utils.h"
#include "semantic/SymbolTable.h"

#include <assert.h>
#include <libgen.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

/* ============================
 * > Helper Function
 * ============================ */
static inline void constructSymbolTable(SymbolManager *sm) {
    sm->pushScope(sm);
}

static inline void destructSymbolTable(SymbolManager *sm) { sm->popScope(sm); }

static inline bool isInForLoop(SemanticContext sc) {
    return sc == FOR_LOOP_SEMANTIC_CONTEXT;
}

static inline bool isInFunction(SemanticContext sc) {
    return sc == FUNCTION_SEMANTIC_CONTEXT;
}

static inline bool isInLocal(SemanticContext sc) {
    return sc == LOCAL_SEMANTIC_CONTEXT;
}

static const char *getBasename(const char *filename) {
    static const size_t kBufferSize = 32 + 1;
    static char buffer[kBufferSize];

    const char *base = basename((char *)filename);

    uint8_t *dot_pos = (uint8_t *)strchr(base, '.');
    if (dot_pos == NULL) {
        strncpy(buffer, base, kBufferSize - 1);
    } else {
        uint8_t org = *dot_pos;
        *dot_pos = 0u;
        strncpy(buffer, base, kBufferSize - 1);
        *dot_pos = org;
    }
    buffer[kBufferSize - 1] = '\0';
    return buffer;
}

static inline bool isLvalueSomeKind(SymbolManager *sm, const char *name,
                                    SymbolKind kind) {
    const SymbolEntry *se = sm->lookup(sm, name);
    assert(se != NULL && "Shouldn't reach here, since it should have been "
                         "checked when visiting VariableReferenceNode");

    if (se->kind == kind) {
        return true;
    }
    return false;
}

static inline void isConditionBoolean(ExpressionNode *condition) {
    if (condition->type != NULL && !condition->type->isBool(condition->type)) {
        logSemanticError(&condition->location,
                         "the expression of condition must be boolean type");
    }
}

/* ============================
 * > Program Node
 * ============================ */
static inline void addSymbolFromProgramNode(SymbolManager *sm,
                                            ProgramNode *node) {
    if (sm->addSymbol(sm, node->name, PROGRAM_SYMBOL, node->type, NULL) ==
        false) {
        logSemanticError(&node->location, "symbol '%s' is redeclared",
                         node->name);
    }
}

static inline void semanticCheckForProgramNode(ProgramNode *node,
                                               const char *filename) {
    if (strcmp(getBasename(filename), node->name) != 0) {
        logSemanticError(&node->location,
                         "program name must be the same as filename");
    }

    if (strcmp(node->name, node->end_name) != 0) {
        logSemanticError(&node->end_name_location,
                         "identifier at the end of program must be the same as "
                         "identifier at the beginning of program");
    }
}

static void analyzeProgramNode(AstNodeVisitor *visitor, ProgramNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;

    sa_visitor->pushFunction(sa_visitor, node->type);
    sa_visitor->pushContext(sa_visitor, GLOBAL_SEMANTIC_CONTEXT);

    constructSymbolTable(sa_visitor->symbol_manager);
    addSymbolFromProgramNode(sa_visitor->symbol_manager, node);

    visitChildOfProgramNode(node, visitor);
    semanticCheckForProgramNode(node, sa_visitor->filename);

    destructSymbolTable(sa_visitor->symbol_manager);

    sa_visitor->popContext(sa_visitor);
    sa_visitor->popFunction(sa_visitor);
}

/* ============================
 * > Declaration Node
 * ============================ */
static void analyzeDeclarationNode(AstNodeVisitor *visitor,
                                   DeclarationNode *node) {
    visitChildOfDeclarationNode(node, visitor);
}

/* ============================
 * > Variable Node
 * ============================ */
static inline void addSymbolFromVariableNode(SymbolManager *sm,
                                             VariableNode *node,
                                             SemanticContext context) {
    SymbolKind kind;
    Constant *constant = (node->constant)
                             ? ((ConstantValueNode *)node->constant)->constant
                             : NULL;

    if (isInForLoop(context)) {
        kind = LOOP_VAR_SYMBOL;
    } else if (isInLocal(context)) {
        kind = (constant != NULL) ? CONSTANT_SYMBOL : VARIABLE_SYMBOL;
    } else if (isInFunction(context)) {
        kind = PARAMETER_SYMBOL;
    } else {
        kind = (constant != NULL) ? CONSTANT_SYMBOL : VARIABLE_SYMBOL;
    }

    if (sm->addSymbol(sm, node->name, kind, node->type, constant) == false) {
        logSemanticError(&node->location, "symbol '%s' is redeclared",
                         node->name);
    }
}

static inline void semanticCheckForVariableNode(VariableNode *node,
                                                SymbolManager *sm) {
    List *dims = node->type->dimensions;

    if (dims->size(dims) == 0u) {
        return;
    }

    SymbolEntry *se = sm->lookup(sm, node->name);

    ListNode *dim_node;
    LIST_FOR_EACH(dim_node, dims->begin(dims)) {
        Dimension *dimension = DEREF_LIST_NODE(dim_node);

        // [SPEC] TODO: skip further checks
        if ((dimension->lower_bound < dimension->upper_bound) == false) {
            logSemanticError(&node->location,
                             "'%s' declared as an array with a lower bound "
                             "greater or equal to upper bound",
                             node->name);
            se->has_error = true;
            return;
        }
    }
}

static void analyzeVariableNode(AstNodeVisitor *visitor, VariableNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;

    addSymbolFromVariableNode(sa_visitor->symbol_manager, node,
                              sa_visitor->semantic_context);
    visitChildOfVariableNode(node, visitor);
    semanticCheckForVariableNode(node, sa_visitor->symbol_manager);
}

/* ============================
 * > Constant Value Node
 * ============================ */
static bool inferPTypeOfConstantValueNode(ConstantValueNode *node) {
    return node->type = copyPType(node->constant->ptype);
}

static void semanticCheckForConstantValueNode(ConstantValueNode *node) {
    if (inferPTypeOfConstantValueNode(node) == false) {
        assert(false && "constant value must have a ptype");
    }
}

static void analyzeConstantValueNode(AstNodeVisitor *visitor,
                                     ConstantValueNode *node) {
    semanticCheckForConstantValueNode(node);
}

/* ============================
 * > Function Node
 * ============================ */
static void addSymbolFromFunctionNode(SymbolManager *sm, FunctionNode *node) {
    if (sm->addSymbol(sm, node->name, FUNCTION_SYMBOL, node->type,
                      node->parameters) == false) {
        logSemanticError(&node->location, "symbol '%s' is redeclared",
                         node->name);
    }
}

static void semanticCheckForFunctionNode(FunctionNode *node) {
    if (strcmp(node->name, node->end_name) != 0) {
        logSemanticError(&node->end_name_location,
                         "identifier at the end of function must be the same "
                         "as identifier at "
                         "the beginning of function");
    }
}

static void analyzeFunctionNode(AstNodeVisitor *visitor, FunctionNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;

    addSymbolFromFunctionNode(sa_visitor->symbol_manager, node);

    sa_visitor->pushFunction(sa_visitor, node->type);
    sa_visitor->pushContext(sa_visitor, FUNCTION_SEMANTIC_CONTEXT);
    constructSymbolTable(sa_visitor->symbol_manager);
    visitAstNodeList(node->parameters, visitor);

    // Directly visit compound statement node since we don't want to form
    // another scope
    sa_visitor->pushContext(sa_visitor, LOCAL_SEMANTIC_CONTEXT);
    visitChildOfCompoundStatementNode(node->body, visitor);
    sa_visitor->popContext(sa_visitor);

    semanticCheckForFunctionNode(node);

    destructSymbolTable(sa_visitor->symbol_manager);
    sa_visitor->popContext(sa_visitor);
    sa_visitor->popFunction(sa_visitor);
}

/* ============================
 * > Compound Statement Node
 * ============================ */
static void analyzeCompoundStatementNode(AstNodeVisitor *visitor,
                                         CompoundStatementNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;

    sa_visitor->pushContext(sa_visitor, LOCAL_SEMANTIC_CONTEXT);
    constructSymbolTable(sa_visitor->symbol_manager);
    visitChildOfCompoundStatementNode(node, visitor);
    destructSymbolTable(sa_visitor->symbol_manager);
    sa_visitor->popContext(sa_visitor);
}

/* ============================
 * > Assignment Node
 * ============================ */
static void semanticCheckForAssignmentNode(AssignmentNode *node,
                                           SymbolManager *sm,
                                           SemanticContext sc) {
    VariableReferenceNode *lvalue = (VariableReferenceNode *)node->lvalue;
    ExpressionNode *expr = (ExpressionNode *)node->expr;

    // Lvalue cannot be inffered, skip checking
    if (lvalue->type == NULL) {
        return;
    }

    const char *name = ((VariableReferenceNode *)lvalue)->name;
    if (true == isLvalueSomeKind(sm, name, CONSTANT_SYMBOL)) {
        logSemanticError(&lvalue->location,
                         "cannot assign to variable '%s' which is a constant",
                         name);
        return;
    }

    if (sc != FOR_LOOP_SEMANTIC_CONTEXT &&
        true == isLvalueSomeKind(sm, name, LOOP_VAR_SYMBOL)) {
        logSemanticError(
            &lvalue->location,
            "the value of loop variable cannot be modified inside the loop");
        return;
    }

    if (!lvalue->type->isScalar(lvalue->type)) {
        logSemanticError(&lvalue->location, "array assignment is not allowed");
        return;
    }

    // Expr cannot be inffered, skip checking
    if (expr->type == NULL) {
        return;
    }

    if (!expr->type->isScalar(expr->type)) {
        logSemanticError(&expr->location, "array assignment is not allowed");
        return;
    }

    if (!lvalue->type->compare(lvalue->type, expr->type)) {
        logSemanticError(
            &expr->location, "assigning to '%s' from incompatible type '%s'",
            lvalue->type->getPTypeString(lvalue->type, /* compactOrNot */ true),
            expr->type->getPTypeString(expr->type, /* compactOrNot */ true));
    }
}

static void analyzeAssignmentNode(AstNodeVisitor *visitor,
                                  AssignmentNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;
    visitChildOfAssignmentNode(node, visitor);
    semanticCheckForAssignmentNode(node, sa_visitor->symbol_manager,
                                   sa_visitor->semantic_context);
}

/* ============================
 * > Print Node
 * ============================ */
static void semanticCheckForPrintNode(PrintNode *node) {
    ExpressionNode *target = (ExpressionNode *)node->target;

    // Target can't be inferred, skip checking
    if (target->type == NULL) {
        return;
    }

    // [Spec] TODO: fix the error msg, should be "expression of print ..."
    if (!target->type->isScalar(target->type)) {
        logSemanticError(
            &target->location,
            "variable reference of print statement must be scalar type");
        return;
    }
}

static void analyzePrintNode(AstNodeVisitor *visitor, PrintNode *node) {
    visitChildOfPrintNode(node, visitor);
    semanticCheckForPrintNode(node);
}

/* ============================
 * > Read Node
 * ============================ */
static void semanticCheckForReadNode(ReadNode *node, SymbolManager *sm) {
    ExpressionNode *target = (ExpressionNode *)node->target;

    // Target can't be inferred, skip checking
    if (target->type == NULL) {
        return;
    }

    const char *name = ((VariableReferenceNode *)target)->name;

    if (true == isLvalueSomeKind(sm, name, CONSTANT_SYMBOL)) {
        logSemanticError(&target->location,
                         "variable reference of read statement cannot be a "
                         "constant variable reference");
        return;
    }

    if (true == isLvalueSomeKind(sm, name, LOOP_VAR_SYMBOL)) {
        logSemanticError(
            &target->location,
            "the value of loop variable cannot be modified inside the loop");
        return;
    }

    if (!target->type->isScalar(target->type)) {
        logSemanticError(
            &target->location,
            "variable reference of read statement must be scalar type");
        return;
    }
}

static void analyzeReadNode(AstNodeVisitor *visitor, ReadNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;
    visitChildOfReadNode(node, visitor);
    semanticCheckForReadNode(node, sa_visitor->symbol_manager);
}

/* ============================
 * > Variable Reference Node
 * ============================ */
static bool areAllIndicesInteger(List *indices) {
    ListNode *index_node;
    LIST_FOR_EACH(index_node, indices->begin(indices)) {
        ExpressionNode *expr = DEREF_LIST_NODE(index_node);

        // There is some expr can't be inferred, skip checking
        if (expr->type == NULL) {
            return false;
        }

        if (!expr->type->isInteger(expr->type)) {
            logSemanticError(&expr->location,
                             "index of array reference must be an integer");
            return false;
        }
    }
    return true;
}

static bool isThereAnOverArraySubscript(VariableReferenceNode *node,
                                        const PType *orig_type) {
    if (orig_type->dimensions->size(orig_type->dimensions) <
        node->indices->size(node->indices)) {
        logSemanticError(&node->location, "there is an over array subscript");
        return true;
    }
    return false;
}

static void inferPTypeOfVariableReferenceNode(VariableReferenceNode *node,
                                              const PType *orig_type) {
    node->type = newPType(orig_type->getPrimitiveType(orig_type));

    // Dereference
    ListNode *dim_node = orig_type->dimensions->begin(orig_type->dimensions);
    for (size_t i = 0u, end = node->indices->size(node->indices); i < end;
         ++i) {
        ITER_NEXT_LIST_NODE(dim_node);
    }

    // Get the remaining dimensions and set PType
    List *dims = newList(free);
    LIST_FOR_EACH(dim_node, dim_node) {
        Dimension *dim = DEREF_LIST_NODE(dim_node);
        concatenateDimensions(dims, dim->lower_bound, dim->upper_bound);
    }
    node->type->setDimensions(node->type, dims);
}

static inline void
semanticCheckForVariableReferenceNode(VariableReferenceNode *node,
                                      SymbolManager *sm) {
    const SymbolEntry *se = sm->lookup(sm, node->name);

    if (se == NULL) {
        logSemanticError(&node->location, "use of undeclared identifier '%s'",
                         node->name);
        return;
    }

    // [Spec] TODO: add a new error for referencing a symbol which is not a variable

    // There is some error in the variable declaration, skip checking
    if (se->has_error) {
        return;
    }

    if (false == areAllIndicesInteger(node->indices)) {
        return;
    }

    if (true == isThereAnOverArraySubscript(node, se->type)) {
        return;
    }

    inferPTypeOfVariableReferenceNode(node, se->type);
}

static void analyzeVariableReferenceNode(AstNodeVisitor *visitor,
                                         VariableReferenceNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;
    visitChildOfVariableReferenceNode(node, visitor);
    semanticCheckForVariableReferenceNode(node, sa_visitor->symbol_manager);
}

/* ============================
 * > Binary Operator Node
 * ============================ */
static inline bool isThereAnyErrorInOperands(BinaryOperatorNode *node) {
    ExpressionNode *left_expr = (ExpressionNode *)node->left,
                   *right_expr = (ExpressionNode *)node->right;

    // There is some expr can't be inferred, skip checking
    if (left_expr->type == NULL || right_expr->type == NULL) {
        return true;
    }
    return false;
}

static bool
checkTypeOfOperandsInArithmeticOrRelationalOp(BinaryOperatorNode *node) {
    ExpressionNode *left_expr = (ExpressionNode *)node->left,
                   *right_expr = (ExpressionNode *)node->right;

    // String concatenation
    if (node->op == PLUS_OP && left_expr->type->isString(left_expr->type) &&
        right_expr->type->isString(right_expr->type)) {
        return true;
    }

    if ((left_expr->type->isInteger(left_expr->type) ||
         left_expr->type->isReal(left_expr->type)) &&
        (right_expr->type->isInteger(right_expr->type) ||
         right_expr->type->isReal(right_expr->type))) {
        return true;
    }

    return false;
}

static bool checkTypeOfOperandsInModOp(BinaryOperatorNode *node) {
    ExpressionNode *left_expr = (ExpressionNode *)node->left,
                   *right_expr = (ExpressionNode *)node->right;

    if (left_expr->type->isInteger(left_expr->type) &&
        right_expr->type->isInteger(right_expr->type)) {
        return true;
    }
    return false;
}

static bool checkTypeOfOperandsInBinaryBooleanOp(BinaryOperatorNode *node) {
    ExpressionNode *left_expr = (ExpressionNode *)node->left,
                   *right_expr = (ExpressionNode *)node->right;

    if (left_expr->type->isBool(left_expr->type) &&
        right_expr->type->isBool(right_expr->type)) {
        return true;
    }
    return false;
}

static void inferPTypeOfBinaryOperatorNode(BinaryOperatorNode *node) {
    ExpressionNode *left_expr = (ExpressionNode *)node->left,
                   *right_expr = (ExpressionNode *)node->right;

    switch (node->op) {
    case PLUS_OP:
    case MINUS_OP:
    case MULTIPLY_OP:
    case DIVIDE_OP:
        if (left_expr->type->isString(left_expr->type) ||
            right_expr->type->isString(right_expr->type)) {
            node->type = newPType(STRING_TYPE);
        } else if (left_expr->type->isReal(left_expr->type) ||
                   right_expr->type->isReal(right_expr->type)) {
            node->type = newPType(REAL_TYPE);
        } else {
            node->type = newPType(INTEGER_TYPE);
        }
        break;
    case MOD_OP:
        node->type = newPType(INTEGER_TYPE);
        break;
    case AND_OP:
    case OR_OP:
    case LESS_OP:
    case LESS_OR_EQUAL_OP:
    case EQUAL_OP:
    case GREATER_OR_EQUAL_OP:
    case GREATER_OP:
    case NOT_EQUAL_OP:
        node->type = newPType(BOOL_TYPE);
        break;
    case NEG_OP:
    case NOT_OP:
    default:
        assert(false &&
               "Shouldn't reach here (there is an unknown op or unary op)");
    }
}

static void semanticCheckForBinaryOperatorNode(BinaryOperatorNode *node) {
    if (true == isThereAnyErrorInOperands(node)) {
        return;
    }

    ExpressionNode *left_expr = (ExpressionNode *)node->left,
                   *right_expr = (ExpressionNode *)node->right;

    switch (node->op) {
    case PLUS_OP:
    case MINUS_OP:
    case MULTIPLY_OP:
    case DIVIDE_OP:
    case LESS_OP:
    case LESS_OR_EQUAL_OP:
    case EQUAL_OP:
    case GREATER_OR_EQUAL_OP:
    case GREATER_OP:
    case NOT_EQUAL_OP:
        if (false == checkTypeOfOperandsInArithmeticOrRelationalOp(node)) {
            goto log_semantic_err;
        }
        break;
    case MOD_OP:
        if (false == checkTypeOfOperandsInModOp(node)) {
            goto log_semantic_err;
        }
        break;
    case AND_OP:
    case OR_OP:
        if (false == checkTypeOfOperandsInBinaryBooleanOp(node)) {
            goto log_semantic_err;
        }
        break;
    case NEG_OP:
    case NOT_OP:
    default:
        assert(false &&
               "Shouldn't reach here (there is an unknown op or unary op)");
    }

    // Infer the type only if there is no error
    inferPTypeOfBinaryOperatorNode(node);
    return;

log_semantic_err:
    logSemanticError(
        &node->location,
        "invalid operands to binary operation '%s' ('%s' and '%s')",
        kOpString[node->op],
        left_expr->type->getPTypeString(left_expr->type,
                                        /* compactOrNot */ true),
        right_expr->type->getPTypeString(right_expr->type,
                                         /* compactOrNot */ true));
}
static void analyzeBinaryOperatorNode(AstNodeVisitor *visitor,
                                      BinaryOperatorNode *node) {
    visitChildOfBinaryOperatorNode(node, visitor);
    semanticCheckForBinaryOperatorNode(node);
}

/* ============================
 * > Unary Operator Node
 * ============================ */
static void inferPTypeOfUnaryOperatorNode(UnaryOperatorNode *node) {
    ExpressionNode *expr = (ExpressionNode *)node->operand;
    node->type = copyPType(expr->type);
}

static void semanticCheckForUnaryOperatorNode(UnaryOperatorNode *node) {
    ExpressionNode *expr = (ExpressionNode *)node->operand;

    // Operand can't be inferred, skip checking
    if (expr->type == NULL) {
        return;
    }

    switch (node->op) {
    case NEG_OP:
        if (!expr->type->isInteger(expr->type) &&
            !expr->type->isReal(expr->type)) {
            goto log_semantic_err;
        }
        break;
    case NOT_OP:
        if (!expr->type->isBool(expr->type)) {
            goto log_semantic_err;
        }
        break;
    default:
        assert(false &&
               "Shouldn't reach here (there is an unknown op or binary op)");
        break;
    }

    inferPTypeOfUnaryOperatorNode(node);
    return;

log_semantic_err:
    logSemanticError(
        &node->location, "invalid operand to unary operation '%s' ('%s')",
        kOpString[node->op],
        expr->type->getPTypeString(expr->type, /* compactOrNot */ true));
}

static void analyzeUnaryOperatorNode(AstNodeVisitor *visitor,
                                     UnaryOperatorNode *node) {
    visitChildOfUnaryOperatorNode(node, visitor);
    semanticCheckForUnaryOperatorNode(node);
}

/* ============================
 * > If Node
 * ============================ */
static void semanticCheckForIfNode(IfNode *node) {
    isConditionBoolean((ExpressionNode *)node->condition);
}

static void analyzeIfNode(AstNodeVisitor *visitor, IfNode *node) {
    visitChildOfIfNode(node, visitor);
    semanticCheckForIfNode(node);
}

/* ============================
 * > While Node
 * ============================ */
static void semanticCheckForWhileNode(WhileNode *node) {
    isConditionBoolean((ExpressionNode *)node->condition);
}

static void analyzeWhileNode(AstNodeVisitor *visitor, WhileNode *node) {
    visitChildOfWhileNode(node, visitor);
    semanticCheckForWhileNode(node);
}

/* ============================
 * > For Node
 * ============================ */
static void semanticCheckForForNode(ForNode *node) {
    if (node->lower_bound > node->upper_bound) {
        logSemanticError(&node->location,
                         "the lower bound of iteration count must be smaller "
                         "than or equal to the upper bound");
    }
}

static void analyzeForNode(AstNodeVisitor *visitor, ForNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;

    sa_visitor->pushContext(sa_visitor, FOR_LOOP_SEMANTIC_CONTEXT);
    constructSymbolTable(sa_visitor->symbol_manager);

    node->loop_var_decl->accept(node->loop_var_decl, visitor);
    node->initial_statement->accept(node->initial_statement, visitor);
    node->condition->accept(node->condition, visitor);
    visitAstNodeList(node->body_statements, visitor);
    semanticCheckForForNode(node);

    destructSymbolTable(sa_visitor->symbol_manager);
    sa_visitor->popContext(sa_visitor);
}

/* ============================
 * > Return Node
 * ============================ */
static void semanticCheckForReturnNode(ReturnNode *node,
                                       const PType *ret_type) {
    assert(ret_type != NULL &&
           "Shouldn't be NULL, program must be in some function");

    if (ret_type->isVoid(ret_type)) {
        logSemanticError(&node->location,
                         "program/procedure should not return a value");
        return;
    }

    ExpressionNode *retval = (ExpressionNode *)node->retval;

    // Expression cannot be inffered, skip checking
    if (retval->type == NULL) {
        return;
    }

    // [Spec] TODO: apply type coerion
    if (!ret_type->compare(ret_type, retval->type)) {
        logSemanticError(
            &retval->location,
            "return '%s' from a function with return type '%s'",
            retval->type->getPTypeString(retval->type, /* compactOrNot */ true),
            ret_type->getPTypeString(ret_type, /* compactOrNot */ true));
    }
}

static void analyzeReturnNode(AstNodeVisitor *visitor, ReturnNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;
    visitChildOfReturnNode(node, visitor);
    semanticCheckForReturnNode(node, sa_visitor->ret_type);
}

/* ============================
 * > Function Call Node
 * ============================ */
static bool isNumOfArgsCorrect(FunctionCallNode *node,
                               const DeclarationNodeList dns) {
    size_t num_of_parameters = 0u;
    ListNode *decl_node;
    LIST_FOR_EACH(decl_node, dns->begin(dns)) {
        DeclarationNode *decl = DEREF_LIST_NODE(decl_node);
        num_of_parameters += decl->vars->size(decl->vars);
    }
    if (num_of_parameters != node->args->size(node->args)) {
        logSemanticError(&node->location,
                         "too few/much arguments to function invocation");
        return false;
    }
    return true;
}

static bool checkIfArgsMatchParameters(const ExpressionNodeList ens,
                                       const DeclarationNodeList dns) {
    ListNode *decl_node, *expr_node = ens->begin(ens);
    LIST_FOR_EACH(decl_node, dns->begin(dns)) {
        DeclarationNode *decl = DEREF_LIST_NODE(decl_node);
        ListNode *var_node;
        LIST_FOR_EACH(var_node, decl->vars->begin(decl->vars)) {
            VariableNode *var = DEREF_LIST_NODE(var_node);
            ExpressionNode *expr = DEREF_LIST_NODE(expr_node);

            // [Spec] TODO: follow the same rule of checking indices in
            //              variable reference
            //
            // Expr cannot be inffered, skip checking
            if (expr->type == NULL) {
                return false;
            }

            if (!var->type->compare(var->type, expr->type)) {
                logSemanticError(
                    &expr->location,
                    "incompatible types passing '%s' to parameter of type '%s'",
                    expr->type->getPTypeString(expr->type,
                                               /* compactOrNot */ true),
                    var->type->getPTypeString(var->type,
                                              /* compactOrNot */ true));
                return false;
            }

            ITER_NEXT_LIST_NODE(expr_node);
        }
    }
    return true;
}

static void semanticCheckForFunctionCallNode(FunctionCallNode *node,
                                             SymbolManager *sm) {
    const SymbolEntry *se = sm->lookup(sm, node->name);

    // [Spec] TODO: add another error msg for calling a symbol
    //              which isn't a function
    if (se == NULL || se->kind != FUNCTION_SYMBOL) {
        logSemanticError(&node->location, "use of undeclared function '%s'",
                         node->name);
        return;
    }

    const DeclarationNodeList dns =
        (const DeclarationNodeList)se->attribute.data;

    if (false == isNumOfArgsCorrect(node, dns)) {
        return;
    }

    if (!checkIfArgsMatchParameters(node->args, dns)) {
        return;
    }

    node->type = copyPType(se->type);
}

static void analyzeFunctionCallNode(AstNodeVisitor *visitor,
                                    FunctionCallNode *node) {
    SemanticAnalyzeVisitor *sa_visitor = (SemanticAnalyzeVisitor *)visitor;
    visitChildOfFunctionCallNode(node, visitor);
    semanticCheckForFunctionCallNode(node, sa_visitor->symbol_manager);
}

/* ============================
 * > Semantic Analyze Visitor
 * ============================ */
static void pushContext(SemanticAnalyzeVisitor *this, SemanticContext sc) {
    SemanticContext *data =
        (SemanticContext *)myMalloc(sizeof(SemanticContext));
    *data = sc;
    this->context_stack->pushFront(this->context_stack, data);
    this->semantic_context = sc;
}

static void popContext(SemanticAnalyzeVisitor *this) {
    free(this->context_stack->popFront(this->context_stack));
    SemanticContext *sc =
        (SemanticContext *)this->context_stack->front(this->context_stack);
    if (sc) {
        this->semantic_context = *sc;
    } else {
        this->semantic_context = GLOBAL_SEMANTIC_CONTEXT;
    }
}

static void pushFunction(SemanticAnalyzeVisitor *this, const PType *type) {
    PType *ret_type = copyPType(type);
    this->ret_type_stack->pushFront(this->ret_type_stack, ret_type);
    this->ret_type = ret_type;
}

static void popFunction(SemanticAnalyzeVisitor *this) {
    freePType(this->ret_type_stack->popFront(this->ret_type_stack));
    this->ret_type = this->ret_type_stack->front(this->ret_type_stack);
}

AstNodeVisitor *newSemanticAnalyzeVisitor(const char *filename) {
    SemanticAnalyzeVisitor *visitor =
        (SemanticAnalyzeVisitor *)myMalloc(sizeof(SemanticAnalyzeVisitor));
    CONSTRUCT_VISITOR(visitor, analyze);
    visitor->symbol_manager = newSymbolManager();
    visitor->ret_type_stack = newList((FreeFPtr)freePType);
    visitor->ret_type = NULL;
    visitor->context_stack = newList(free);
    visitor->semantic_context = GLOBAL_SEMANTIC_CONTEXT;
    visitor->filename = filename;
    visitor->pushContext = pushContext;
    visitor->popContext = popContext;
    visitor->pushFunction = pushFunction;
    visitor->popFunction = popFunction;

    return (AstNodeVisitor *)visitor;
}

void freeSemanticAnalyzeVisitor(SemanticAnalyzeVisitor *sa_visitor) {
    freeSymbolManager(sa_visitor->symbol_manager);
    freeList(sa_visitor->ret_type_stack);
    freeList(sa_visitor->context_stack);
    free(sa_visitor);
}
