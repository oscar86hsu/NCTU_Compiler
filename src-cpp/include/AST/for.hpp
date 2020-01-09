#pragma once
#include "AST/ast.hpp"
#include "visitor/visitor.hpp"
#include <string>

class ForNode : public ASTNodeBase {
  public:
    Node loop_variable_declaration; // a declaration node
    Node initial_statement;         // an assignment node
    Node condition;                 // an expression node
    NodeList *body;                 // a list of statement nodes (zero or more)

    int lower_bound; // HW4 ADD
    int upper_bound; // HW4 ADD
  public:
    ForNode(int _line_number, int _col_number, Node _loop_variable_declaration,
            Node _initial_statement, Node _condition, NodeList *_body,
            std::string loop_var_name, int _lower_bound, int _upper_bound);
    ~ForNode();
    void accept(ASTVisitorBase &v) { v.visit(this); }
    void print();
};