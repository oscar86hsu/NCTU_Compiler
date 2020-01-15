#include "AST/assignment.hpp"
#include "AST/ast.hpp"
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
#include "semantic/DumpSymbolTable.hpp"
#include "semantic/ErrorMsg.hpp"
#include "semantic/SemanticAnalyzer.hpp"
#include "semantic/SymbolTable.hpp"
#include <cstdio>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <stack> 
using namespace std;

//
// TODO: implementations of constructor and destructor
//

SemanticAnalyzer::SemanticAnalyzer(string _filename, FILE *_fp)
{
    this->symbol_table_root = new SymbolTable(0);
    this->current_scope = this->symbol_table_root;
    this->level = 0;

    _filename = _filename.substr(0, _filename.length() - 2);
    for (int i = _filename.length() - 1; i >= 0; i--)
    {
        if (_filename[i] == '/')
        {
            _filename = _filename.substr(i + 1, _filename.length() - i);
            break;
        }
    }
    this->filename = _filename;
    this->fp = _fp;

    this->semantic_error = 0;
    this->error_msg = "";

    this->specify = false;
    this->specify_kind = KIND_UNKNOWN;
}

SemanticAnalyzer::~SemanticAnalyzer() { delete this->symbol_table_root; }

void SemanticAnalyzer::level_up() { this->level++; }
void SemanticAnalyzer::level_down() { this->level--; }
void SemanticAnalyzer::output_err_msg() { cerr << this->error_msg; }
int SemanticAnalyzer::is_semantic_error() { return this->semantic_error; }

SymbolTable *SemanticAnalyzer::get_symbol_table()
{
    return this->symbol_table_root;
}

void SemanticAnalyzer::dump_symbol_table()
{
    this->dump_symbol_table_util(this->symbol_table_root->next_scope_list[0]);
}

void SemanticAnalyzer::push(SymbolTable *_new_scope, enum EnumNodeTable type,
                            VariableInfo re_type)
{
    _new_scope->prev_scope = this->current_scope;
    _new_scope->in_node_type = type;
    _new_scope->in_node_return_type = re_type;
    this->current_scope->next_scope_list.push_back(_new_scope);

    this->current_scope = _new_scope;
}
void SemanticAnalyzer::pop()
{
    this->current_scope = this->current_scope->prev_scope;
}

void SemanticAnalyzer::specify_on(FieldKind _field_kind)
{
    this->specify = true;
    this->specify_kind = _field_kind;
}

void SemanticAnalyzer::specify_off() { this->specify = false; }

void SemanticAnalyzer::push_src_node(EnumNodeTable _node)
{
    this->src_node.push(_node);
}

void SemanticAnalyzer::pop_src_node() { this->src_node.pop(); }

void SemanticAnalyzer::dump_symbol_table_util(SymbolTable *enter)
{

    for (uint i = 0; i < enter->next_scope_list.size(); i++)
        dump_symbol_table_util(enter->next_scope_list[i]);

    dumpSymbol_Header();
    for (uint i = 0; i < enter->entry_name.size(); i++)
        dumpSymbol_Body(enter->entry[enter->entry_name[i]]);
    dumpSymbol_Bottom();
}

// false -> not found
bool SemanticAnalyzer::check_symbol_inside(string _name)
{
    if (_name.length() > 32)
        _name = _name.substr(0, 32);
    bool found = false;
    SymbolTable *current = this->current_scope;
    while (true)
    {
        if (current->entry[_name].is_used == true)
        {
            found = true;
            break;
        }
        else
        {
            if (current->level == 0)
                break;
            else
                current = current->prev_scope;
        }
    }
    return found;
}

SymbolEntry SemanticAnalyzer::get_symbol_entry(string _name)
{
    SymbolEntry temp;
    SymbolTable *current = this->current_scope;
    while (true)
    {
        if (current->entry[_name].is_used == true)
        {
            return current->entry[_name];
        }
        else
        {
            if (current->level == 0)
                break;
            else
                current = current->prev_scope;
        }
    }
    return temp; // Won't Happen .... Maybe
}

// true -> loop_var has been declared
bool SemanticAnalyzer::check_loop_var(string _name)
{
    if (_name.length() > 32)
        _name = _name.substr(0, 32);
    bool found = false;
    SymbolTable *current = this->current_scope;
    while (true)
    {
        if (current->entry[_name].is_used == true &&
            current->entry[_name].kind == KIND_LOOP_VAR)
        {
            found = true;
            break;
        }
        else
        {
            if (current->level == 0)
                break;
            else
                current = current->prev_scope;
        }
    }
    return found;
}

// true -> error array declaration
bool SemanticAnalyzer::check_array_declaration_error(string _name)
{
    if (_name.length() > 32)
        _name = _name.substr(0, 32);
    bool is_error = false;
    SymbolTable *current = this->current_scope;
    while (true)
    {
        if (current->entry[_name].is_used == true)
        {
            is_error = current->entry[_name].is_arr_decl_error;
            break;
        }
        else
        {
            if (current->level == 0)
                break;
            else
                current = current->prev_scope;
        }
    }
    return is_error;
}

// true -> inside program / procedure call
bool SemanticAnalyzer::check_program_or_procedure_call()
{
    bool is_error = false;
    SymbolTable *current = this->current_scope;
    while (true)
    {
        if (current->in_node_type == FUNCTION_NODE ||
            current->in_node_type == PROGRAM_NODE)
        {
            if (current->in_node_return_type.type == TYPE_VOID)
            {
                return true;
            }
            break;
        }
        else
            current = current->prev_scope;
    }
    return is_error;
}

VariableInfo SemanticAnalyzer::get_function_return_type()
{
    SymbolTable *current = this->current_scope;
    while (true)
    {
        if (current->in_node_type == FUNCTION_NODE)
        {
            return current->in_node_return_type;
        }
        else
            current = current->prev_scope;
    }
}

bool SemanticAnalyzer::check_function_declaration(string _name)
{
    if (_name.length() > 32)
        _name = _name.substr(0, 32);
    SymbolTable *global_scope = this->symbol_table_root->next_scope_list[0];
    if (global_scope->entry[_name].is_used == true)
    {
        return true;
    }
    else
    {
        return false;
    }
}

void SemanticAnalyzer::dump_riscv(string _path)
{
    string output_code;
    output_code += "    .file \"" + this->filename + ".p\"\n";
    output_code += "    .option nopic\n";
    output_code += dump_riscv_util(global_var, ".bss");
    output_code += dump_riscv_util(global_const, ".text");
    output_code += dump_riscv_util(function, ".text");
    output_code += dump_riscv_util(main, ".text");
    //cout << output_code << endl;
    if (_path.back() != '/')
        _path += "/";
    ofstream file(_path + this->filename + ".s");
    file << output_code;
    file.close();
}

string SemanticAnalyzer::dump_riscv_util(vector<string> vec, string prefix)
{
    string output_code;
    if (vec.size() > 0)
    {
        output_code += prefix + "\n";
        for (auto &it : vec)
        {
            output_code += it;
        }
    }

    return output_code;
}

string SemanticAnalyzer::get_function_start_code(string name)
{
    string output_code;
    output_code += "    .align 2\n";
    output_code += "    .global " + name + "\n";
    output_code += "    .type " + name + ", @function\n";
    output_code += name + ":\n";
    output_code += "    addi sp, sp, -64\n";
    output_code += "    sd ra, 56(sp)\n";
    output_code += "    sd s0, 48(sp)\n";
    output_code += "    addi s0, sp, 64\n";
    return output_code;
}
string SemanticAnalyzer::get_function_end_code(string name)
{
    string output_code;
    output_code += "    ld ra, 56(sp)\n";
    output_code += "    ld s0, 48(sp)\n";
    output_code += "    addi sp, sp, 64\n";
    output_code += "    jr ra\n";
    output_code += "    .size " + name + ", .-" + name + "\n";
    return output_code;
}

string SemanticAnalyzer::get_const_value(VariableInfo var_info)
{
    string value;
    switch (var_info.type_set)
    {
    case SET_SCALAR:
    case SET_CONSTANT_LITERAL:
        switch (var_info.type)
        {
        case TYPE_INTEGER:
            value = to_string(var_info.int_literal);
            break;
        case TYPE_REAL:
            value = to_string(var_info.real_literal);
            break;
        case TYPE_STRING:
            value = var_info.string_literal;
            break;
        case TYPE_BOOLEAN:
            switch (var_info.boolean_literal)
            {
            case true:
                value = "1";
                break;
            default:
                value = "0";
                break;
            }
            break;
        default:
            value = "";
            break;
        }
        break;
    case SET_ACCUMLATED:
        switch (var_info.type)
        {
        case TYPE_INTEGER:
            value = to_string(var_info.int_literal);
            break;
        case TYPE_REAL:
            value = to_string(var_info.real_literal);
            break;
        case TYPE_STRING:
            value = var_info.string_literal;
            break;
        case TYPE_BOOLEAN:
            switch (var_info.boolean_literal)
            {
            case true:
                value = "1";
                break;
            default:
                value = "0";
                break;
            }
            break;
        default:
            value = "";
            break;
        }
        break;
    case UNKNOWN_SET:
    default:
        value = "";
        break;
    }
    return value;
}

