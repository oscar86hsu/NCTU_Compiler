#include "AST/for.hpp"
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <string>

ForNode::ForNode(int _line_number, int _col_number,
                 Node _loop_variable_declaration, Node _initial_statement,
                 Node _condition, NodeList *_body, string _loop_var_name,
                 int _lower_bound, int _upper_bound) {
    this->line_number = _line_number;
    this->col_number = _col_number;
    this->loop_variable_declaration = _loop_variable_declaration;
    this->initial_statement = _initial_statement;
    this->condition = _condition;
    this->body = _body;

    this->lower_bound = _lower_bound; // HW4 ADD
    this->upper_bound = _upper_bound; // HW4 ADD
}

ForNode::~ForNode() {
    SAFE_DELETE(this->loop_variable_declaration)
    SAFE_DELETE(this->initial_statement)
    SAFE_DELETE(this->condition)
    NODELIST_PTR_DELETE(this->body)
}

void ForNode::print() {
    std::cout << "for statement <line: " << line_number
              << ", col: " << col_number << ">" << std::endl;
}