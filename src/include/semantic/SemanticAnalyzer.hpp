#pragma once
#include "AST/ast.hpp"
#include "semantic/SymbolTable.hpp"
#include "visitor/visitor.hpp"
#include <cstdio>
#include <stack>
#include <string>
#include <vector>
#include <stack> 
using namespace std;
// FIXME: remember to replace ";" below with ";", or your implementations in
// .cpp won't be compiled.

class SemanticAnalyzer : public ASTVisitorBase {
  public:
    void visit(ProgramNode *m) override;
    void visit(DeclarationNode *m) override;
    void visit(VariableNode *m) override;
    void visit(ConstantValueNode *m) override;
    void visit(FunctionNode *m) override;
    void visit(CompoundStatementNode *m) override;
    void visit(AssignmentNode *m) override;
    void visit(PrintNode *m) override;
    void visit(ReadNode *m) override;
    void visit(VariableReferenceNode *m) override;
    void visit(BinaryOperatorNode *m) override;
    void visit(UnaryOperatorNode *m) override;
    void visit(IfNode *m) override;
    void visit(WhileNode *m) override;
    void visit(ForNode *m) override;
    void visit(ReturnNode *m) override;
    void visit(FunctionCallNode *m) override;

    SemanticAnalyzer(string _filename, FILE *_fp);
    ~SemanticAnalyzer();

    class SymbolTable *get_symbol_table();
    void dump_symbol_table();
    void dump_riscv(string _path);
    void output_err_msg();
    int is_semantic_error();

  private: // TODO
    class SymbolTable *symbol_table_root;
    class SymbolTable *current_scope;
    unsigned int level;
    vector<string> global_var, global_const, function, main;

    string filename;
    FILE *fp;
    int dump_enable;

    string error_msg;
    int semantic_error;
    
    stack<int> tmp_return_value;
    int loop_num = 0;

    // Level Manange
    void level_up();
    void level_down();

    // Scope Manage
    void push(SymbolTable *_new_scope, enum EnumNodeTable type,
              VariableInfo re_type);
    void pop();

    // Kind Specify
    bool specify;
    FieldKind specify_kind;
    void specify_on(FieldKind);
    void specify_off();

    // Source Node
    stack<enum EnumNodeTable> src_node;
    void push_src_node(enum EnumNodeTable);
    void pop_src_node();

    // Expression Stack
    stack<VariableInfo> expression_stack;

    // Dump Symbol Table
    void dump_symbol_table_util(SymbolTable *enter);

    // Dump RISC-V Utils
    string dump_riscv_util(vector<string> vec, string prefix);
    string get_function_start_code(string name);
    string get_function_end_code(string name);

    // Other Utils
    bool check_symbol_inside(string _name);
    SymbolEntry get_symbol_entry(string _name);

    bool check_loop_var(string _name);
    bool check_array_declaration_error(string _name);
    bool check_program_or_procedure_call();
    bool check_function_declaration(string _name);

    VariableInfo get_function_return_type();
    string get_const_value(VariableInfo var_info);
    

};