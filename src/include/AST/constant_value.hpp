#pragma once
#include "AST/ast.hpp"
#include "visitor/visitor.hpp"

class ConstantValueNode : public ASTNodeBase {
  public:
    VariableInfo *constant_value; // Not sure its type

  public:
    ConstantValueNode(int _line_number, int _col_number,
                      VariableInfo *_constant_value);
    ~ConstantValueNode();
    void accept(ASTVisitorBase &v) { v.visit(this); }
    void print();
};