%{
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
#include "AST/ASTDumper.h"
#include "core/list.h"
#include "core/error.h"
#include "semantic/SemanticAnalyzeVisitor.h"

#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define YYLTYPE yyltype

typedef struct YYLTYPE {
    uint32_t first_line;
    uint32_t first_column;
    uint32_t last_line;
    uint32_t last_column;
} yyltype;

/* Declared by scanner.l */
extern uint32_t line_num;
extern char Buffer[512];
extern FILE *yyin;
extern char *yytext;
/* End */

static AstNode *root;
bool hasError = false;

extern int yylex(void);
static void yyerror(const char *msg);

VariableNodeList constructVariableNodeList(IdentifierInfoList id_infos,
                                           const PType *ptype, AstNode *constant) {
    VariableNodeList vns = newList((FreeFPtr)freeVariableNode);
    IdentifierInfo *id_info;
    while ((id_info = id_infos->popFront(id_infos)) != NULL) {
        vns->pushBack(
            vns,
            newVariableNode(id_info->location.line, id_info->location.col,
                            id_info->identifier, copyPType(ptype),
                            copyConstantValueNode(constant)));
        freeIdentifierInfo(id_info);
    }
    return vns;
}

%}

    /* For yylval */
%union {
    char *identifier;
    AstNode *node;
    List *list;
    PType *type;
    int32_t integer;
    double real;
    bool boolean;
    char *string;
    Constant *constant;
};
%type <identifier> ProgramName FunctionName
%type <node> Declaration FunctionDeclaration FormalArg
             Statement
             CompoundStatement Simple Condition For While Return FunctionInvokation
             Expression VariableReference FunctionCall
%type <list> IdList ArrDecl FormalArgList FormalArgs DeclarationList Declarations
             FunctionList Functions ElseOrNot StatementList Statements ArrRef
             ExpressionList Expressions
%type <type> Type ScalarType ArrType ReturnType
%type <constant> LiteralConstant
%type <integer> INT_LITERAL
%type <real> REAL_LITERAL
%type <string> STRING_LITERAL
%type <boolean> TRUE FALSE

    /* Delimiter */
%token COMMA SEMICOLON COLON
%token L_PARENTHESIS R_PARENTHESIS
%token L_BRACKET R_BRACKET

    /* Operator */
%token ASSIGN
%left OR
%left AND
%right NOT
%left LESS LESS_OR_EQUAL EQUAL GREATER GREATER_OR_EQUAL NOT_EQUAL
%left PLUS MINUS
%left MULTIPLY DIVIDE MOD
%right UNARY_MINUS

    /* Keyword */
%token ARRAY BOOLEAN INTEGER REAL STRING
%token END BEGIN_ /* Use BEGIN_ since BEGIN is a keyword in lex */
%token DO ELSE FOR IF THEN WHILE
%token DEF OF TO RETURN VAR
%token FALSE TRUE
%token PRINT READ

    /* Identifier */
%token <identifier> ID

    /* Literal */
%token INT_LITERAL
%token REAL_LITERAL
%token STRING_LITERAL

%%
    /*
       Program Units
                     */

Program:
    ProgramName SEMICOLON
    /* ProgramBody */
    DeclarationList FunctionList CompoundStatement
    /* End of ProgramBody */
    END ProgramName {
        root = newProgramNode(@1.first_line, @1.first_column, newPType(VOID_TYPE), $1,
                              $3, $4, $5,
                              @7.first_line, @7.first_column, $7);
    }
;

ProgramName:
    ID
;

DeclarationList:
    Epsilon {
        $$ = NULL;
    }
    |
    Declarations {
        $$ = $1;
    }
;

Declarations:
    Declaration {
        $$ = newList((FreeFPtr)freeDeclarationNode);
        $$->pushBack($$, $1);
    }
    |
    Declarations Declaration {
        $1->pushBack($1, $2);
        $$ = $1;
    }
;

FunctionList:
    Epsilon {
        $$ = NULL;
    }
    |
    Functions {
        $$ = $1;
    }
;

Functions:
    FunctionDeclaration {
        $$ = newList((FreeFPtr)freeFunctionNode);
        $$->pushBack($$, $1);
    }
    |
    Functions FunctionDeclaration {
        $1->pushBack($1, $2);
        $$ = $1;
    }
;

FunctionDeclaration:
    FunctionName L_PARENTHESIS FormalArgList R_PARENTHESIS ReturnType SEMICOLON
    CompoundStatement
    END FunctionName {
        $$ = newFunctionNode(@1.first_line, @1.first_column,
                             $1, $3, $5, (CompoundStatementNode *)$7,
                             @9.first_line, @9.first_column, $9);
    }
;

FunctionName:
    ID
;

FormalArgList:
    Epsilon {
        $$ = NULL;
    }
    |
    FormalArgs {
        $$ = $1;
    }
;

FormalArgs:
    FormalArg {
        List *list = newList((FreeFPtr)freeDeclarationNode);
        list->pushBack(list, $1);
        $$ = list;
    }
    |
    FormalArgs SEMICOLON FormalArg {
        $1->pushBack($1, $3);
        $$ = $1;
    }
;

FormalArg:
    IdList COLON Type {
        $$ = newDeclarationNode(@1.first_line, @1.first_column,
                                constructVariableNodeList($1, $3, NULL));
        freeList($1);
        freePType($3);
    }
;

IdList:
    ID {
        List *list = newList(freeIdentifierInfo);
        list->pushBack(list, newIdentifierInfo(@1.first_line, @1.first_column, $1));
        $$ = list;
    }
    |
    IdList COMMA ID {
        $1->pushBack($1, newIdentifierInfo(@3.first_line, @3.first_column, $3));
        $$ = $1;
    }
;

ReturnType:
    COLON ScalarType {
        $$ = $2;
    }
    |
    Epsilon {
        $$ = newPType(VOID_TYPE);
    }
;

    /*
       Data Types and Declarations
                                   */

Declaration:
    VAR IdList COLON Type SEMICOLON {
        $$ = newDeclarationNode(@1.first_line, @1.first_column,
                                constructVariableNodeList($2, $4, NULL));
        freeList($2);
        freePType($4);
    }
    |
    VAR IdList COLON LiteralConstant SEMICOLON {
        AstNode *cvn = newConstantValueNode(@4.first_line, @4.first_column,
                                            copyConstant($4));
        $$ = newDeclarationNode(@1.first_line, @1.first_column,
                                constructVariableNodeList($2, $4->ptype, cvn));
        freeList($2);
        freeConstant($4);
        cvn->free(cvn);
    }
;

Type:
    ScalarType
    |
    ArrType
;

ScalarType:
    INTEGER { $$ = newPType(INTEGER_TYPE); }
    |
    REAL { $$ = newPType(REAL_TYPE); }
    |
    STRING { $$ = newPType(STRING_TYPE); }
    |
    BOOLEAN { $$ = newPType(BOOL_TYPE); }
;

ArrType:
    ArrDecl ScalarType {
        $2->setDimensions($2, $1);
        $$ = $2;
    }
;

ArrDecl:
    ARRAY INT_LITERAL TO INT_LITERAL OF {
        $$ = newList(free);
        concatenateDimensions($$, $2, $4);
    }
    |
    ArrDecl ARRAY INT_LITERAL TO INT_LITERAL OF {
        concatenateDimensions($1, $3, $5);
        $$ = $1;
    }
;

LiteralConstant:
    INT_LITERAL {
        union ConstantValue value = { .integer = $1 };
        $$ = newConstant(newPType(INTEGER_TYPE), value);
    }
    |
    REAL_LITERAL {
        union ConstantValue value = { .real = $1 };
        $$ = newConstant(newPType(REAL_TYPE), value);
    }
    |
    STRING_LITERAL {
        union ConstantValue value = { .string = $1 };
        $$ = newConstant(newPType(STRING_TYPE), value);
    }
    |
    TRUE {
        union ConstantValue value = { .boolean = $1 };
        $$ = newConstant(newPType(BOOL_TYPE), value);
    }
    |
    FALSE {
        union ConstantValue value = { .boolean = $1 };
        $$ = newConstant(newPType(BOOL_TYPE), value);
    }
;

    /*
       Statements
                  */

Statement:
    CompoundStatement {
        $$ = $1;
    }
    |
    Simple {
        $$ = $1;
    }
    |
    Condition {
        $$ = $1;
    }
    |
    While {
        $$ = $1;
    }
    |
    For {
        $$ = $1;
    }
    |
    Return {
        $$ = $1;
    }
    |
    FunctionInvokation {
        $$ = $1;
    }
;

CompoundStatement:
    BEGIN_
    DeclarationList
    StatementList
    END {
        $$ = newCompoundStatementNode(@1.first_line, @1.first_column, $2, $3);
    }
;

Simple:
    VariableReference ASSIGN Expression SEMICOLON {
        $$ = newAssignmentNode(@2.first_line, @2.first_column, $1, $3);
    }
    |
    PRINT Expression SEMICOLON {
        $$ = newPrintNode(@1.first_line, @1.first_column, $2);
    }
    |
    READ VariableReference SEMICOLON {
        $$ = newReadNode(@1.first_line, @1.first_column, $2);
    }
;

VariableReference:
    ID {
        $$ = newVariableReferenceNode(@1.first_line, @1.first_column, $1, NULL);
    }
    |
    ID ArrRef {
        $$ = newVariableReferenceNode(@1.first_line, @1.first_column, $1, $2);
    }
;

ArrRef:
    L_BRACKET Expression R_BRACKET {
        $$ = newList((FreeFPtr)freeAstNode);
        $$->pushBack($$, $2);
    }
    |
    ArrRef L_BRACKET Expression R_BRACKET {
        // Add an AstNode
        // Be evaluated during semantic analysis and code generation
        $1->pushBack($1, $3);
        $$ = $1;
    }
;

Condition:
    IF Expression THEN
    StatementList
    ElseOrNot
    END IF {
        $$ = newIfNode(@1.first_line, @1.first_column, $2, $4, $5);
    }
;

ElseOrNot:
    ELSE
    StatementList {
        $$ = $2;
    }
    |
    Epsilon {
        $$ = NULL;
    }
;

While:
    WHILE Expression DO
    StatementList
    END DO {
        $$ = newWhileNode(@1.first_line, @1.first_column, $2, $4);
    }
;

For:
    FOR ID ASSIGN INT_LITERAL TO INT_LITERAL DO
    StatementList
    END DO {
        PType *type;
        union ConstantValue value;
        List *list;
        AstNode *const_value_node;

        /* Prepare DeclarationNode */
        list = newList(freeIdentifierInfo);
        list->pushBack(list, newIdentifierInfo(@2.first_line, @2.first_column, $2));
        type = newPType(INTEGER_TYPE);
        AstNode *loop_var_decl = newDeclarationNode(@2.first_line, @2.first_column,
                                                    constructVariableNodeList(list, type,
                                                                              NULL));
        freeList(list);
        freePType(type);

        /* Prepare AssignmentNode */
        AstNode *var_ref = newVariableReferenceNode(@2.first_line, @2.first_column,
                                                    strdup($2), NULL);

        value.integer = $4;
        const_value_node = newConstantValueNode(@4.first_line, @4.first_column,
                                                newConstant(newPType(INTEGER_TYPE),
                                                            value));

        AstNode *assign = newAssignmentNode(@3.first_line, @3.first_column,
                                            var_ref, const_value_node);

        /* Prepare end condition */
        value.integer = $6;
        const_value_node = newConstantValueNode(@6.first_line, @6.first_column,
                                                newConstant(newPType(INTEGER_TYPE),
                                                            value));

        $$ = newForNode(@1.first_line, @1.first_column, $4, $6,
                        loop_var_decl, assign, const_value_node, $8);
    }
;

Return:
    RETURN Expression SEMICOLON {
        $$ = newReturnNode(@1.first_line, @1.first_column, $2);
    }
;

FunctionInvokation:
    FunctionCall SEMICOLON {
        $$ = $1;
    }
;

FunctionCall:
    ID L_PARENTHESIS ExpressionList R_PARENTHESIS {
        $$ = newFunctionCallNode(@1.first_line, @1.first_column, $1, $3);
    }
;

ExpressionList:
    Epsilon {
        $$ = NULL;
    }
    |
    Expressions {
        $$ = $1;
    }
;

Expressions:
    Expression {
        List *list = newList((FreeFPtr)freeAstNode);
        list->pushBack(list, $1);
        $$ = list;
    }
    |
    Expressions COMMA Expression {
        $1->pushBack($1, $3);
        $$ = $1;
    }
;

StatementList:
    Epsilon {
        $$ = NULL;
    }
    |
    Statements {
        $$ = $1;
    }
;

Statements:
    Statement {
        $$ = newList((FreeFPtr)freeAstNode);
        $$->pushBack($$, $1);
    }
    |
    Statements Statement {
        $1->pushBack($1, $2);
        $$ = $1;
    }
;

Expression:
    L_PARENTHESIS Expression R_PARENTHESIS {
        $$ = $2;
    }
    |
    MINUS Expression %prec UNARY_MINUS {
        $$ = newUnaryOperatorNode(@1.first_line, @1.first_column,
                                  NEG_OP, $2);
    }
    |
    Expression MULTIPLY Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   MULTIPLY_OP, $1, $3);
    }
    |
    Expression DIVIDE Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   DIVIDE_OP, $1, $3);
    }
    |
    Expression MOD Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   MOD_OP, $1, $3);
    }
    |
    Expression PLUS Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   PLUS_OP, $1, $3);
    }
    |
    Expression MINUS Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   MINUS_OP, $1, $3);
    }
    |
    Expression LESS Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   LESS_OP, $1, $3);
    }
    |
    Expression LESS_OR_EQUAL Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   LESS_OR_EQUAL_OP, $1, $3);
    }
    |
    Expression GREATER Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   GREATER_OP, $1, $3);
    }
    |
    Expression GREATER_OR_EQUAL Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   GREATER_OR_EQUAL_OP, $1, $3);
    }
    |
    Expression EQUAL Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   EQUAL_OP, $1, $3);
    }
    |
    Expression NOT_EQUAL Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   NOT_EQUAL_OP, $1, $3);
    }
    |
    NOT Expression {
        $$ = newUnaryOperatorNode(@1.first_line, @1.first_column,
                                  NOT_OP, $2);
    }
    |
    Expression AND Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   AND_OP, $1, $3);
    }
    |
    Expression OR Expression {
        $$ = newBinaryOperatorNode(@2.first_line, @2.first_column,
                                   OR_OP, $1, $3);
    }
    |
    LiteralConstant {
        AstNode *constant = newConstantValueNode(@1.first_line, @1.first_column,
                                                 copyConstant($1));
        freeConstant($1);
        $$ = constant;
    }
    |
    VariableReference {
        $$ = $1;
    }
    |
    FunctionCall {
        $$ = $1;
    }
;

    /*
       misc
            */
Epsilon:
;
%%

void yyerror(const char *msg) {
    fprintf(stderr,
            "\n"
            "|-----------------------------------------------------------------"
            "---------\n"
            "| Error found in Line #%d: %s\n"
            "|\n"
            "| Unmatched token: %s\n"
            "|-----------------------------------------------------------------"
            "---------\n",
            line_num, Buffer, yytext);
    exit(-1);
}

int main(int argc, const char *argv[]) {
    CHECK(argc >= 2, "Usage: ./parser <filename> [--dump-ast]\n");

    FILE *fp = fopen(argv[1], "r");

    CHECK(fp != NULL, "fopen() fails.\n");
    yyin = fp;
    yyparse();

    if (argc > 2 && strcmp(argv[2], "--dump-ast") == 0) {
        AstNodeVisitor *dump_visitor = newASTDumper();
        root->accept(root, dump_visitor);
        freeASTDumper(dump_visitor);
    }
    AstNodeVisitor *sa_visitor = newSemanticAnalyzeVisitor(argv[1]);
    root->accept(root, sa_visitor);
    freeSemanticAnalyzeVisitor(sa_visitor);

    if (!hasError) {
        printf("\n"
               "|---------------------------------------------|\n"
               "|  There is no syntactic and semantic error!  |\n"
               "|---------------------------------------------|\n");
    }

    freeProgramNode(root);
    fclose(fp);
    return 0;
}
