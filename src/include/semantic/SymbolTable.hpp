#pragma once
#include <AST/ast.hpp>
#include <map>
#include <string>
#include <vector>
using namespace std;

enum AttributeType {
    NO_ATTRIBUTE = 200,
    ATTRIBUTE_PARAMETERS,
    ATTRIBUTE_VALUE_OF_CONSTANT,
    UNKNOWN_ATTRIBUTE,
};

class Attribute {
  public:
    vector<VariableInfo> parameter_type;
    VariableInfo value_of_constant;
    AttributeType attr_type;

  public:
    Attribute();
    Attribute(AttributeType);
    Attribute(vector<VariableInfo>);
    Attribute(VariableInfo);

    void set_parameter_type(vector<VariableInfo>);
    void set_value_of_constant(VariableInfo);
};

enum FieldKind {
    KIND_PROGRAM = 100,
    KIND_FUNCTION,
    KIND_PARAMETER,
    KIND_VARIABLE,
    KIND_LOOP_VAR,
    KIND_CONSTANT,
    KIND_UNKNOWN
};

class SymbolEntry {
  public:
    // Public Info
    string name; // size = 1 to 32
    FieldKind kind;
    unsigned int level;
    VariableInfo type;
    Attribute attribute;
    int stack_addr;

    // Hide Info
    bool is_used;
    bool is_arr_decl_error; // For Array Declaration
    enum EnumNodeTable node_type;

    class ProgramNode *program_node;
    class VariableNode *variable_node;
    class FunctionNode *function_node;

  public:
    SymbolEntry();
    SymbolEntry(string _name, FieldKind _kind, unsigned int _level,
                VariableInfo _type, Attribute _attribute,
                enum EnumNodeTable _node_type, class ProgramNode *_program_node,
                class VariableNode *_variable_node,
                class FunctionNode *_function_node, int _stack_addr = 0);
};

class SymbolTable {
  public:
    // Link Info
    SymbolTable *prev_scope;
    enum EnumNodeTable in_node_type;
    VariableInfo in_node_return_type;
    vector<SymbolTable *> next_scope_list;
    int current_stack_addr = -20;
    int current_tmp = 0;
    

    // General Info
    unsigned int level;
    map<string, SymbolEntry> entry;
    vector<string> entry_name;
    bool used_tmp[16] = {false};

  public:
    SymbolTable(unsigned int _level);
    ~SymbolTable();

    void put(SymbolEntry _symbol_entry);
    SymbolEntry get_entry(string _name);
    bool redeclare_check(string _name);
    bool check_entry(string _name);
    int get_used_tmp();
};