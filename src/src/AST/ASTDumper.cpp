#include "AST/ASTDumper.hpp"
#include "AST/assignment.hpp"
#include "AST/binary_operator.hpp"
#include "AST/compound_statement.hpp"
#include "AST/constant_value.hpp"
#include "AST/declaration.hpp"
#include "AST/for.hpp"
#include "AST/function.hpp"
#include "AST/function_call.hpp"
#include "AST/if.hpp"
#include "AST/print.hpp"
#include "AST/program.hpp"
#include "AST/read.hpp"
#include "AST/return.hpp"
#include "AST/unary_operator.hpp"
#include "AST/variable.hpp"
#include "AST/variable_reference.hpp"
#include "AST/while.hpp"

#include <iostream>

void ASTDumper::visit(ProgramNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->declaration_node_list != nullptr)
        for (uint i = 0; i < m->declaration_node_list->size(); i++) {
            (*(m->declaration_node_list))[i]->accept(*this);
        }

    if (m->function_node_list != nullptr)
        for (uint i = 0; i < m->function_node_list->size(); i++) {
            (*(m->function_node_list))[i]->accept(*this);
        }

    if (m->compound_statement_node != nullptr)
        m->compound_statement_node->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(DeclarationNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->variables_node_list != nullptr)
        for (uint i = 0; i < m->variables_node_list->size(); i++) {
            (*(m->variables_node_list))[i]->accept(*this);
        }
    this->space_counter_decrease();
}

void ASTDumper::visit(VariableNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->constant_value_node != nullptr)
        m->constant_value_node->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(ConstantValueNode *m) {
    this->print_space();
    m->print();

    // this->space_counter_increase();
    // this->space_counter_decrease();
}

void ASTDumper::visit(FunctionNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->parameters != nullptr)
        for (uint i = 0; i < m->parameters->size(); i++) {
            (*(m->parameters))[i]->node->accept(*this);
        }

    if (m->body != nullptr)
        m->body->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(CompoundStatementNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->declaration_node_list != nullptr)
        for (uint i = 0; i < m->declaration_node_list->size(); i++) {
            (*(m->declaration_node_list))[i]->accept(*this);
        }
    if (m->statement_node_list != nullptr)
        for (uint i = 0; i < m->statement_node_list->size(); i++) {
            (*(m->statement_node_list))[i]->accept(*this);
        }
    this->space_counter_decrease();
}

void ASTDumper::visit(AssignmentNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->variable_reference_node != nullptr)
        m->variable_reference_node->accept(*this);

    if (m->expression_node != nullptr)
        m->expression_node->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(PrintNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->expression_node != nullptr)
        m->expression_node->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(ReadNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->variable_reference_node != nullptr)
        m->variable_reference_node->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(VariableReferenceNode *m) {
    this->print_space();
    m->print();

    if (m->expression_node_list != nullptr)
        for (uint i = 0; i < m->expression_node_list->size(); i++) {
            this->print_space();
            std::cout << "[" << std::endl;

            this->space_counter_increase();
            (*(m->expression_node_list))[i]->accept(*this);
            this->space_counter_decrease();

            this->print_space();
            std::cout << "]" << std::endl;
        }
}

void ASTDumper::visit(BinaryOperatorNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->left_operand != nullptr)
        m->left_operand->accept(*this);

    if (m->right_operand != nullptr)
        m->right_operand->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(UnaryOperatorNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->operand != nullptr)
        m->operand->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(IfNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->condition != nullptr)
        m->condition->accept(*this);

    if (m->body != nullptr)
        for (uint i = 0; i < m->body->size(); i++)
            (*(m->body))[i]->accept(*this);
    this->space_counter_decrease();

    if (m->body_of_else != nullptr) {
        this->print_space();
        std::cout << "else" << std::endl;

        this->space_counter_increase();
        for (uint i = 0; i < m->body_of_else->size(); i++)
            (*(m->body_of_else))[i]->accept(*this);
        this->space_counter_decrease();
    }
}

void ASTDumper::visit(WhileNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->condition != nullptr)
        m->condition->accept(*this);

    if (m->body != nullptr)
        for (uint i = 0; i < m->body->size(); i++)
            (*(m->body))[i]->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(ForNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->loop_variable_declaration != nullptr)
        m->loop_variable_declaration->accept(*this);

    if (m->initial_statement != nullptr)
        m->initial_statement->accept(*this);

    if (m->condition != nullptr)
        m->condition->accept(*this);

    if (m->body != nullptr)
        for (uint i = 0; i < m->body->size(); i++)
            (*(m->body))[i]->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(ReturnNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->return_value != nullptr)
        m->return_value->accept(*this);
    this->space_counter_decrease();
}

void ASTDumper::visit(FunctionCallNode *m) {
    this->print_space();
    m->print();

    this->space_counter_increase();
    if (m->arguments != nullptr)
        for (uint i = 0; i < m->arguments->size(); i++)
            (*(m->arguments))[i]->accept(*this);
    this->space_counter_decrease();
}
