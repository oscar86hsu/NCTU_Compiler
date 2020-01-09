#include "AST/ASTDumper.h"
#include "core/list.h"
#include "core/utils.h"

#include <stdio.h>

uint32_t g_indentation = 0u;
const uint32_t kIndentionWidth = 2u;

static void dumpProgramNode(AstNodeVisitor *visitor, ProgramNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "program <line: %u, col: %u> %s %s\n", node->location.line,
            node->location.col, node->name,
            node->type->getPTypeString(node->type, /* compactOrNot */ false));

    g_indentation += kIndentionWidth;
    visitChildOfProgramNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpDeclarationNode(AstNodeVisitor *visitor,
                                DeclarationNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "declaration <line: %u, col: %u>\n", node->location.line,
            node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfDeclarationNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpVariableNode(AstNodeVisitor *visitor, VariableNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "variable <line: %u, col: %u> %s %s\n", node->location.line,
            node->location.col, node->name,
            node->type->getPTypeString(node->type, /* compactOrNot */ false));

    g_indentation += kIndentionWidth;
    visitChildOfVariableNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpConstantValueNode(AstNodeVisitor *visitor,
                                  ConstantValueNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "constant <line: %u, col: %u> ", node->location.line,
            node->location.col);
    fprintf(stdout, "%s\n",
            node->constant->getConstantValueString(node->constant));
}

static const char *getFunctionPrototypeString(const FunctionNode *node) {
    const static size_t kBufferSize = 2148u;
    static char buffer[kBufferSize];

    int position = snprintf(
        buffer, kBufferSize, "%s ",
        node->type->getPTypeString(node->type, /* compactOrNot */ false));
    snprintf(buffer + position, kBufferSize - position, "(%s)",
             getParametersTypeString(node->parameters));

    return buffer;
}

static void dumpFunctionNode(AstNodeVisitor *visitor, FunctionNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "function declaration <line: %u, col: %u> %s %s\n",
            node->location.line, node->location.col, node->name,
            getFunctionPrototypeString(node));

    g_indentation += kIndentionWidth;
    visitChildOfFunctionNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpCompoundStatementNode(AstNodeVisitor *visitor,
                                      CompoundStatementNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "compound statement <line: %u, col: %u>\n",
            node->location.line, node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfCompoundStatementNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpAssignmentNode(AstNodeVisitor *visitor, AssignmentNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "assignment statement <line: %u, col: %u>\n",
            node->location.line, node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfAssignmentNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpPrintNode(AstNodeVisitor *visitor, PrintNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "print statement <line: %u, col: %u>\n",
            node->location.line, node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfPrintNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpReadNode(AstNodeVisitor *visitor, ReadNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "read statement <line: %u, col: %u>\n", node->location.line,
            node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfReadNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpVariableReferenceNode(AstNodeVisitor *visitor,
                                      VariableReferenceNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "variable reference <line: %u, col: %u> %s\n",
            node->location.line, node->location.col, node->name);

    ListNode *n;
    LIST_FOR_EACH(n, node->indices->begin(node->indices)) {
        fprintf(stdout, "%*s[\n", g_indentation, "");
        g_indentation += kIndentionWidth;

        AstNode *idx_node = DEREF_LIST_NODE(n);
        idx_node->accept(idx_node, visitor);

        g_indentation -= kIndentionWidth;
        fprintf(stdout, "%*s]\n", g_indentation, "");
    }
}

static void dumpBinaryOperatorNode(AstNodeVisitor *visitor,
                                   BinaryOperatorNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "binary operator <line: %u, col: %u> %s\n",
            node->location.line, node->location.col, kOpString[node->op]);

    g_indentation += kIndentionWidth;
    visitChildOfBinaryOperatorNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpUnaryOperatorNode(AstNodeVisitor *visitor,
                                  UnaryOperatorNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "unary operator <line: %u, col: %u> %s\n",
            node->location.line, node->location.col, kOpString[node->op]);

    g_indentation += kIndentionWidth;
    visitChildOfUnaryOperatorNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpIfNode(AstNodeVisitor *visitor, IfNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "if statement <line: %u, col: %u>\n", node->location.line,
            node->location.col);

    g_indentation += kIndentionWidth;
    node->condition->accept(node->condition, visitor);
    visitAstNodeList(node->body_statements, visitor);
    g_indentation -= kIndentionWidth;

    if (node->else_statements) {
        fprintf(stdout, "%*s", g_indentation, "");
        fprintf(stdout, "else\n");
        g_indentation += kIndentionWidth;
        visitAstNodeList(node->else_statements, visitor);
        g_indentation -= kIndentionWidth;
    }
}

static void dumpWhileNode(AstNodeVisitor *visitor, WhileNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "while statement <line: %u, col: %u>\n",
            node->location.line, node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfWhileNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpForNode(AstNodeVisitor *visitor, ForNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "for statement <line: %u, col: %u>\n", node->location.line,
            node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfForNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpReturnNode(AstNodeVisitor *visitor, ReturnNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "return statement <line: %u, col: %u>\n",
            node->location.line, node->location.col);

    g_indentation += kIndentionWidth;
    visitChildOfReturnNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

static void dumpFunctionCallNode(AstNodeVisitor *visitor,
                                 FunctionCallNode *node) {
    fprintf(stdout, "%*s", g_indentation, "");
    fprintf(stdout, "function call statement <line: %u, col: %u> %s\n",
            node->location.line, node->location.col, node->name);

    g_indentation += kIndentionWidth;
    visitChildOfFunctionCallNode(node, visitor);
    g_indentation -= kIndentionWidth;
}

AstNodeVisitor *newASTDumper(void) {
    ASTDumper *visitor = (ASTDumper *)myMalloc(sizeof(ASTDumper));
    CONSTRUCT_VISITOR(visitor, dump);

    return (AstNodeVisitor *)visitor;
}

void freeASTDumper(void *ad) { free(ad); }
