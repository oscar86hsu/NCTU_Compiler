#pragma once
#include "AST/ast.hpp"
#include "visitor/visitor.hpp"

class AssignmentNode : public ASTNodeBase {
  public:
    Node variable_reference_node; // Lvalue
    Node expression_node;         // Expression

  public:
    AssignmentNode(int _line_number, int _col_nubmer,
                   Node _variable_reference_node, Node _expression_node);
    ~AssignmentNode();
    void accept(ASTVisitorBase &v) { v.visit(this); }
    void print();
};