#include "semantic/SemanticAnalyzer.hpp"
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
#include "semantic/SymbolTable.hpp"
#include <cstdio>
#include <iomanip>
#include <iostream>
#include <typeinfo>
using namespace std;

//
// TODO: implementations of visit(xxxxNode *)
//

void SemanticAnalyzer::visit(ProgramNode *m)
{
    // Put Symbol Table (Special Case)
    SymbolTable *new_scope = new SymbolTable(0);
    this->push(new_scope, PROGRAM_NODE, VariableInfo(UNKNOWN_SET, TYPE_VOID));

    // Push Symbol Entity
    if (this->current_scope->redeclare_check(m->program_name) == false)
    {
        // Error: Redeclare
        this->semantic_error = 1;
        this->error_msg +=
            redeclare_error_msg(m->line_number, m->col_number, m->program_name);
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);
    }
    else
    {
        this->current_scope->put(
            SymbolEntry(m->program_name, KIND_PROGRAM, this->level,
                        VariableInfo(UNKNOWN_SET, TYPE_VOID),
                        Attribute(NO_ATTRIBUTE), PROGRAM_NODE, m, NULL, NULL));
    }

    this->main.push_back(this->get_function_start_code("main"));

    // Visit Child Nodes
    this->push_src_node(PROGRAM_NODE);
    if (m->declaration_node_list != nullptr)
        for (uint i = 0; i < m->declaration_node_list->size(); i++)
        {
            (*(m->declaration_node_list))[i]->accept(*this);
        }

    if (m->function_node_list != nullptr)
        for (uint i = 0; i < m->function_node_list->size(); i++)
        {
            (*(m->function_node_list))[i]->accept(*this);
        }

    if (m->compound_statement_node != nullptr)
        m->compound_statement_node->accept(*this);
    this->pop_src_node();

    // Semantic Analyses of Program Node
    if (m->program_name != this->filename)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->line_number, m->col_number);
        this->error_msg += "program name must be the same as filename\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);
    }

    if (m->program_name != m->end_name)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->end_line_number, m->end_col_number);
        this->error_msg += "identifier at the end of program must be the same "
                           "as identifier at the beginning of program\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->end_line_number, m->end_col_number);
    }

    this->main.push_back(get_function_end_code("main"));
    // Pop Scope
    this->pop();
}

void SemanticAnalyzer::visit(DeclarationNode *m)
{
    // Visit Child Nodes
    this->push_src_node(DECLARATION_NODE);
    if (m->variables_node_list != nullptr)
        for (uint i = 0; i < m->variables_node_list->size(); i++)
        {
            (*(m->variables_node_list))[i]->accept(*this);
        }
    this->pop_src_node();
}

void SemanticAnalyzer::visit(VariableNode *m)
{
    // Push Entry
    // New Variable check Old Loop Var
    if (check_loop_var(m->variable_name) == true)
    {
        // Error: Redeclare
        this->semantic_error = 1;
        this->error_msg += redeclare_error_msg(m->line_number, m->col_number,
                                               m->variable_name);
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);

        return;
    }

    // New Variable check Redeclared
    if (this->current_scope->redeclare_check(m->variable_name) == false)
    {
        // Error: Redeclare
        this->semantic_error = 1;
        this->error_msg += redeclare_error_msg(m->line_number, m->col_number,
                                               m->variable_name);
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);

        return;
    }

    if (this->specify == true)
    {
        if (m->constant_value_node == nullptr)
        { // Not Constant
            if (this->level == 0)
            { // Global
                this->current_scope->put(SymbolEntry(
                    m->variable_name, this->specify_kind, this->level, *(m->type),
                    Attribute(NO_ATTRIBUTE), VARIABLE_NODE, NULL, m, NULL));
                string output_code;
                output_code += m->variable_name + ":\n";
                output_code += "    .word 0\n";
                this->global_var.push_back(output_code);
            }
            else
            { // Local
                this->current_scope->put(SymbolEntry(
                    m->variable_name, this->specify_kind, this->level, *(m->type),
                    Attribute(NO_ATTRIBUTE), VARIABLE_NODE, NULL, m, NULL, this->current_scope->current_stack_addr));
                this->current_scope->current_stack_addr -= 4;
            }
        }
        else
        { // Constant
            if (this->level == 0)
            { // Global
                this->current_scope->put(SymbolEntry(
                    m->variable_name, this->specify_kind, this->level, *(m->type),
                    Attribute(*(m->type)), VARIABLE_NODE, NULL, m, NULL));
                string output_code;
                output_code += m->variable_name + ":\n";
                output_code += "    .word " + this->get_const_value(*(m->type)) + "\n";
                this->global_const.push_back(output_code);
            }
            else
            { // Local
                this->current_scope->put(SymbolEntry(
                    m->variable_name, this->specify_kind, this->level, *(m->type),
                    Attribute(*(m->type)), VARIABLE_NODE, NULL, m, NULL, this->current_scope->current_stack_addr));
                string output_code;
                output_code += "    li t0, " + this->get_const_value(*(m->type)) + "\n";
                output_code += "    sw t0, " + to_string(this->current_scope->get_entry(m->variable_name).stack_addr) + "(s0)\n";
                if (this->current_scope->in_node_type != FUNCTION_NODE)
                {
                    this->main.push_back(output_code);
                }
                else
                {
                    this->function.push_back(output_code);
                }
                this->current_scope->current_stack_addr -= 4;
            }
        }
    }
    else
    {

        if (m->constant_value_node == nullptr)
        { // Not Constant
            if (this->level == 0)
            { // Global
                this->current_scope->put(SymbolEntry(
                    m->variable_name, KIND_VARIABLE, this->level, *(m->type),
                    Attribute(NO_ATTRIBUTE), VARIABLE_NODE, NULL, m, NULL));
                string output_code;
                output_code += m->variable_name + ":\n";
                output_code += "    .word 0\n";
                this->global_var.push_back(output_code);
            }
            else
            { // Local
                this->current_scope->put(SymbolEntry(
                    m->variable_name, KIND_VARIABLE, this->level, *(m->type),
                    Attribute(NO_ATTRIBUTE), VARIABLE_NODE, NULL, m, NULL, this->current_scope->current_stack_addr));
                this->current_scope->current_stack_addr -= 4;
            }
        }
        else
        {
            if (this->level == 0)
            { // Global
                this->current_scope->put(SymbolEntry(
                    m->variable_name, KIND_CONSTANT, this->level, *(m->type),
                    Attribute(*(m->type)), VARIABLE_NODE, NULL, m, NULL));
                string output_code;
                output_code += m->variable_name + ":\n";
                output_code += "    .word " + this->get_const_value(*(m->type)) + "\n";
                this->global_const.push_back(output_code);
            }
            else
            { // Local
                this->current_scope->put(SymbolEntry(
                    m->variable_name, KIND_CONSTANT, this->level, *(m->type),
                    Attribute(*(m->type)), VARIABLE_NODE, NULL, m, NULL, this->current_scope->current_stack_addr));
                string output_code;
                output_code += "    li t0, " + this->get_const_value(*(m->type)) + "\n";
                output_code += "    sw t0, " + to_string(this->current_scope->get_entry(m->variable_name).stack_addr) + "(s0)\n";
                if (this->current_scope->in_node_type != FUNCTION_NODE)
                {
                    this->main.push_back(output_code);
                }
                else
                {
                    this->function.push_back(output_code);
                }
                this->current_scope->current_stack_addr -= 4;
            }
        }
    }

    // Semantic Check
    if (m->type->type_set == SET_ACCUMLATED)
    {
        bool is_upperbound_le_lowerbound = false;
        for (uint i = 0; i < m->type->array_range.size(); i++)
        {
            if (m->type->array_range[i].end <= m->type->array_range[i].start)
            {
                is_upperbound_le_lowerbound = true;
                break;
            }
        }

        if (is_upperbound_le_lowerbound == true)
        {
            this->semantic_error = 1;
            this->error_msg += error_found_msg(m->line_number, m->col_number);
            this->error_msg += "'" + m->variable_name + "'";
            this->error_msg += " declared as an array with a lower bound "
                               "greater or equal to upper bound\n";
            this->error_msg +=
                src_notation_msg(this->fp, m->line_number, m->col_number);

            this->current_scope->entry[m->variable_name].is_arr_decl_error =
                true;
        }
    }
}

void SemanticAnalyzer::visit(ConstantValueNode *m)
{ // EXPRESSION
    this->expression_stack.push(*(m->constant_value));
}

void SemanticAnalyzer::visit(FunctionNode *m)
{
    this->function.push_back(get_function_start_code(m->function_name));
    // Part 1:
    // Redeclare Check (current_scope still is global)
    if (this->current_scope->redeclare_check(m->function_name) == false)
    {
        // Error: Redeclare
        this->semantic_error = 1;
        this->error_msg += redeclare_error_msg(m->line_number, m->col_number,
                                               m->function_name);
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);
    }
    else
    {
        // Push Name into global scope
        vector<VariableInfo> tempVI;
        for (uint i = 0; i < m->prototype.size(); i++)
        {
            tempVI.push_back(*(m->prototype[i]));
        }

        this->current_scope->put(SymbolEntry(
            m->function_name, KIND_FUNCTION, this->level, *(m->return_type),
            Attribute(tempVI), FUNCTION_NODE, NULL, NULL, m));
    }

    // Part 2:
    // Push Scope
    this->level_up();
    SymbolTable *new_scope = new SymbolTable(this->level);
    this->push(new_scope, FUNCTION_NODE, *(m->return_type));

    // Visit Child Node
    this->push_src_node(FUNCTION_NODE);
    this->specify_on(KIND_PARAMETER);
    if (m->parameters != nullptr)
    {
        for (uint i = 0; i < m->parameters->size(); i++)
        {
            (*(m->parameters))[i]->node->accept(*this);
        }
    }
    if (m->parameters != nullptr)
    {
        string output_code;
        int tmp_addr = -20;
        for (uint i = 0; i < m->prototype.size(); i++)
        {
            cout << (m->prototype)[i] << endl;
            output_code += "    sw a" + to_string(i) + ", " + to_string(tmp_addr) + "(s0)\n";
            tmp_addr -= 4;
        }
        this->function.push_back(output_code);
    }

    this->specify_off();

    if (m->body != nullptr)
        m->body->accept(*this);
    this->pop_src_node();

    // Semantic Check
    if (m->function_name != m->end_name)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->end_line_number, m->end_col_number);
        this->error_msg += "identifier at the end of function must be the same "
                           "as identifier at the beginning of function\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->end_line_number, m->end_col_number);
    }

    this->function.push_back(get_function_end_code(m->function_name));
    // Pop Scope
    this->pop();
    this->level_down();
}

void SemanticAnalyzer::visit(CompoundStatementNode *m)
{ // STATEMENT
    // Push Scope
    if (this->src_node.top() != FUNCTION_NODE)
    {
        this->level_up();
        SymbolTable *new_scope = new SymbolTable(this->level);
        this->push(new_scope, COMPOUND_STATEMENT_NODE,
                   VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));
    }

    // Visit Child Nodes
    this->push_src_node(COMPOUND_STATEMENT_NODE);
    if (m->declaration_node_list != nullptr)
        for (uint i = 0; i < m->declaration_node_list->size(); i++)
        {
            (*(m->declaration_node_list))[i]->accept(*this);
        }

    if (m->statement_node_list != nullptr)
        for (uint i = 0; i < m->statement_node_list->size(); i++)
        {
            (*(m->statement_node_list))[i]->accept(*this);
        }
    this->pop_src_node();

    // Pop Scope
    if (this->src_node.top() != FUNCTION_NODE)
    {
        this->pop();
        this->level_down();
    }
}

void SemanticAnalyzer::visit(AssignmentNode *m)
{ // STATEMENT
    // Visit Child Node
    this->push_src_node(ASSIGNMENT_NODE);
    if (m->variable_reference_node != nullptr)
        m->variable_reference_node->accept(*this);

    if (m->expression_node != nullptr)
        m->expression_node->accept(*this);
    this->pop_src_node();

    // Semantic Check
    VariableInfo r_type = this->expression_stack.top();
    this->expression_stack.pop();
    VariableInfo l_type = this->expression_stack.top();
    this->expression_stack.pop();

    if (l_type.type_set == UNKNOWN_SET && l_type.type == UNKNOWN_TYPE)
    {
        // No Need Further Check
        return;
    }

    if (l_type.type_set == SET_CONSTANT_LITERAL)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->variable_reference_node->line_number,
                            m->variable_reference_node->col_number);
        this->error_msg += "cannot assign to variable '" +
                           m->variable_reference_node->name +
                           "' which is a constant\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->variable_reference_node->line_number,
                             m->variable_reference_node->col_number);
        return;
    }

    if (check_loop_var(m->variable_reference_node->name) == true)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->variable_reference_node->line_number,
                            m->variable_reference_node->col_number);
        this->error_msg +=
            "the value of loop variable cannot be modified inside the loop\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->variable_reference_node->line_number,
                             m->variable_reference_node->col_number);
        return;
    }

    if (l_type.type_set == SET_ACCUMLATED)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->variable_reference_node->line_number,
                            m->variable_reference_node->col_number);
        this->error_msg += "array assignment is not allowed\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->variable_reference_node->line_number,
                             m->variable_reference_node->col_number);
        return;
    }

    if (r_type.type_set == UNKNOWN_SET && r_type.type == UNKNOWN_TYPE)
    {
        // No Need Further Check
        return;
    }

    if (r_type.type_set == SET_ACCUMLATED)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->expression_node->line_number,
                                           m->expression_node->col_number);
        this->error_msg += "array assignment is not allowed\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->expression_node->line_number,
                             m->expression_node->col_number);
        return;
    }

    if (l_type.type_set == SET_SCALAR && l_type.type == TYPE_INTEGER &&
        (((r_type.type_set == SET_SCALAR ||
           r_type.type_set == SET_CONSTANT_LITERAL) &&
          (r_type.type == TYPE_INTEGER || r_type.type == TYPE_REAL)) ==
         false))
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->expression_node->line_number,
                                           m->expression_node->col_number);
        this->error_msg += "assigning to '" + info_convert(l_type);
        this->error_msg +=
            "' from incompatible type '" + info_convert(r_type) + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->expression_node->line_number,
                             m->expression_node->col_number);
    }
    else if (l_type.type_set == SET_SCALAR && l_type.type == TYPE_REAL &&
             (((r_type.type_set == SET_SCALAR ||
                r_type.type_set == SET_CONSTANT_LITERAL) &&
               (r_type.type == TYPE_REAL)) == false))
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->expression_node->line_number,
                                           m->expression_node->col_number);
        this->error_msg += "assigning to '" + info_convert(l_type);
        this->error_msg +=
            "' from incompatible type '" + info_convert(r_type) + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->expression_node->line_number,
                             m->expression_node->col_number);
    }
    else if (l_type.type_set == SET_SCALAR && l_type.type == TYPE_BOOLEAN &&
             (((r_type.type_set == SET_SCALAR ||
                r_type.type_set == SET_CONSTANT_LITERAL) &&
               (r_type.type == TYPE_BOOLEAN)) == false))
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->expression_node->line_number,
                                           m->expression_node->col_number);
        this->error_msg += "assigning to '" + info_convert(l_type);
        this->error_msg +=
            "' from incompatible type '" + info_convert(r_type) + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->expression_node->line_number,
                             m->expression_node->col_number);
    }
    else if (l_type.type_set == SET_SCALAR && l_type.type == TYPE_STRING &&
             (((r_type.type_set == SET_SCALAR ||
                r_type.type_set == SET_CONSTANT_LITERAL) &&
               (r_type.type == TYPE_STRING)) == false))
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->expression_node->line_number,
                                           m->expression_node->col_number);
        this->error_msg += "assigning to '" + info_convert(l_type);
        this->error_msg +=
            "' from incompatible type '" + info_convert(r_type) + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->expression_node->line_number,
                             m->expression_node->col_number);
    }
    else if (l_type.type_set == SET_ACCUMLATED &&
             r_type.type_set == SET_ACCUMLATED)
    {
        if (array_size_check(l_type, r_type) == false)
        {
            this->semantic_error = 1;
            this->error_msg += error_found_msg(m->expression_node->line_number,
                                               m->expression_node->col_number);
            this->error_msg += "assigning to '" + info_convert(l_type);
            this->error_msg +=
                "' from incompatible type '" + info_convert(r_type) + "'\n";
            this->error_msg +=
                src_notation_msg(this->fp, m->expression_node->line_number,
                                 m->expression_node->col_number);
        }
    }

    string output_code;

    if (r_type.type_set == SET_CONSTANT_LITERAL)
    {
        output_code += "    li t0, " + get_const_value(r_type) + "\n";
    }
    else
    {
        if (typeid(*m->expression_node) == typeid(VARIABLE_REFERENCE_NODE))
        {
            if (get_symbol_entry(m->expression_node->name).level == 0)
            {
                output_code += "    la t" + to_string(this->current_scope->get_used_tmp() + 1) + ", " + m->expression_node->name + "\n";
                output_code += "    lw t0, 0(t" + to_string(this->current_scope->get_used_tmp() + 1) + ")\n";
            }
            else
            {
                output_code += "    lw t0, " + to_string(get_symbol_entry(m->expression_node->name).stack_addr) + "(s0)\n";
            }
        }
    }
    if (get_symbol_entry(m->variable_reference_node->name).level == 0)
    {
        output_code += "    la t" + to_string(this->current_scope->get_used_tmp() + 1) + ", " + m->variable_reference_node->name + "\n";
        output_code += "    sw t0, 0(t" + to_string(this->current_scope->get_used_tmp() + 1) + ")\n";
    }
    else
    {
        output_code += "    sw t0, " + to_string(this->current_scope->get_entry(m->variable_reference_node->name).stack_addr) + "(s0)\n";
    }

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }
}

void SemanticAnalyzer::visit(PrintNode *m)
{ // STATEMENT
    // Visit Child Node
    this->push_src_node(PRINT_NODE);
    if (m->expression_node != nullptr)
        m->expression_node->accept(*this);
    this->pop_src_node();

    // Semantic Check
    VariableInfo tmpInfo = this->expression_stack.top();
    this->expression_stack.pop();

    if (tmpInfo.type_set == UNKNOWN_SET && tmpInfo.type == UNKNOWN_TYPE)
    {
        return; // No Need Further Check
    }

    if (tmpInfo.type_set != SET_SCALAR && tmpInfo.type_set != SET_CONSTANT_LITERAL)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->expression_node->line_number,
                                           m->expression_node->col_number);
        this->error_msg +=
            "variable reference of print statement must be scalar type\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->expression_node->line_number,
                             m->expression_node->col_number);
    }
    string output_code;
    if (this->current_scope->get_entry(m->expression_node->name).level == 0)
    {
        output_code += "    la t0, " + m->expression_node->name + "\n";
        output_code += "    lw a0, 0(t0)\n";
    }
    else
    {

        output_code += "    lw a0, " + to_string(this->current_scope->get_entry(m->expression_node->name).stack_addr) + "(s0)\n";
    }

    output_code += "    jal ra, print\n";
    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }
}

void SemanticAnalyzer::visit(ReadNode *m)
{ // STATEMENT
    // Visit Child Node
    this->push_src_node(READ_NODE);
    if (m->variable_reference_node != nullptr)
        m->variable_reference_node->accept(*this);
    this->pop_src_node();

    // Semantic Check
    VariableInfo r_type = this->expression_stack.top();
    this->expression_stack.pop();

    if (r_type.type_set == UNKNOWN_SET && r_type.type == UNKNOWN_TYPE)
    {
        return; // No Need Further Check
    }

    if (r_type.type_set == SET_CONSTANT_LITERAL)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->variable_reference_node->line_number,
                            m->variable_reference_node->col_number);
        this->error_msg += "variable reference of read statement cannot be a "
                           "constant variable reference\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->variable_reference_node->line_number,
                             m->variable_reference_node->col_number);
        return;
    }

    if (check_loop_var(m->variable_reference_node->name) == true)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->variable_reference_node->line_number,
                            m->variable_reference_node->col_number);
        this->error_msg +=
            "the value of loop variable cannot be modified inside the loop\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->variable_reference_node->line_number,
                             m->variable_reference_node->col_number);
        return;
    }

    if (r_type.type_set != SET_SCALAR)
    {
        this->semantic_error = 1;
        this->error_msg +=
            error_found_msg(m->variable_reference_node->line_number,
                            m->variable_reference_node->col_number);
        this->error_msg +=
            "variable reference of read statement must be scalar type\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->variable_reference_node->line_number,
                             m->variable_reference_node->col_number);
        return;
    }

    string output_code;
    output_code += "    jal ra, read\n";
    output_code += "    la t0, " + m->variable_reference_node->name + "\n";
    output_code += "    sw a0, 0(t0)\n";

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }
}

void SemanticAnalyzer::visit(VariableReferenceNode *m)
{ // EXPRESSION
    // Part 1:
    // Semantic Check
    // Special Case
    if (this->specify == true && this->specify_kind == KIND_LOOP_VAR)
    {
        // Error Happen in this node
        VariableInfo tmpInfo;
        tmpInfo.type_set = UNKNOWN_SET;
        tmpInfo.type = UNKNOWN_TYPE;
        this->expression_stack.push(tmpInfo);
        return;
    }

    // Part 2:
    // Semantic Check
    // Normal Case
    bool m_error = false;
    if (check_symbol_inside(m->variable_name) == false)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->line_number, m->col_number);
        this->error_msg +=
            "use of undeclared identifier '" + m->variable_name + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);

        m_error = true; // This Error is Special. When it Occur, No need
                        // Traverse this Node
    }
    else if (check_array_declaration_error(m->variable_name) == true)
    {

        m_error = true; // This Error is Special. When it Occur, No need
                        // Traverse this Node
    }
    else if (m->expression_node_list != nullptr && m_error == false)
    {

        // First visit expression list
        this->push_src_node(VARIABLE_REFERENCE_NODE);
        if (m->expression_node_list != nullptr)
            for (int i = m->expression_node_list->size() - 1; i >= 0;
                 i--) // REVERSE TRAVERSE
                (*(m->expression_node_list))[i]->accept(*this);
        this->pop_src_node();

        // Part1:
        // Check the expression stack
        bool index_error = false;
        int type_check = 0;
        for (uint i = 0; i < m->expression_node_list->size(); i++)
        {
            VariableInfo temp = this->expression_stack.top();
            expression_stack.pop();

            if (temp.type == UNKNOWN_TYPE && type_check != 0)
                type_check = 2;
            else if (temp.type != TYPE_INTEGER && type_check == 0)
            {
                type_check = 1;
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->expression_node_list->at(i)->line_number,
                                    m->expression_node_list->at(i)->col_number);
                this->error_msg +=
                    "index of array reference must be an integer\n";
                this->error_msg += src_notation_msg(
                    this->fp, m->expression_node_list->at(i)->line_number,
                    m->expression_node_list->at(i)->col_number);
                m_error = true;
                index_error = true;
            }
        }

        // Part2:
        if (index_error == false)
        {
            unsigned int subscript_size =
                this->get_symbol_entry(m->variable_name)
                    .variable_node->type->array_range.size();
            if (m->expression_node_list->size() > subscript_size)
            {
                // Error!
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "there is an over array subscript\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                m_error = true;
            }
        }
    }

    // Put Expression Stack
    if (m_error == true)
    {
        // Error Happen in this node
        VariableInfo tmpInfo;
        tmpInfo.type_set = UNKNOWN_SET;
        tmpInfo.type = UNKNOWN_TYPE;

        this->expression_stack.push(tmpInfo);
    }
    else
    {
        if (m->expression_node_list != nullptr)
        {
            VariableInfo entry_info =
                *this->get_symbol_entry(m->variable_name).variable_node->type;
            VariableInfo tmp_info(entry_info.type_set, entry_info.type);
            int dimension =
                entry_info.array_range.size() - m->expression_node_list->size();

            if (dimension == 0) // Exactly SCALAR
                tmp_info.type_set = SET_SCALAR;
            else
                for (uint i = m->expression_node_list->size();
                     i < entry_info.array_range.size(); i++)
                    tmp_info.array_range.push_back(entry_info.array_range[i]);

            this->expression_stack.push(tmp_info);
        }
        else
        {
            VariableInfo tmp_info =
                *this->get_symbol_entry(m->variable_name).variable_node->type;
            this->expression_stack.push(tmp_info);
        }
    }
}

void SemanticAnalyzer::visit(BinaryOperatorNode *m)
{ // EXPRESSION
    // Visit Child Node
    this->push_src_node(BINARY_OPERATOR_NODE);
    if (m->left_operand != nullptr)
        m->left_operand->accept(*this);

    if (m->right_operand != nullptr)
        m->right_operand->accept(*this);
    this->pop_src_node();

    // Semantic Check // Expression Stack
    VariableInfo rhs = this->expression_stack.top();
    this->expression_stack.pop();
    VariableInfo lhs = this->expression_stack.top();
    this->expression_stack.pop();
    bool error = false;

    string output_code;

    if (rhs.type_set == SET_CONSTANT_LITERAL)
    {
        output_code += "    li t1, " + get_const_value(rhs) + "\n";
    }
    else
    {
        if (typeid(*m->right_operand) == typeid(VariableReferenceNode))
        {
            if (get_symbol_entry(m->right_operand->name).level == 0)
            {
                output_code += "    la t" + to_string(this->current_scope->get_used_tmp() + 1) + ", " + m->right_operand->name + "\n";
                output_code += "    lw t1, 0(t" + to_string(this->current_scope->get_used_tmp() + 1) + ")\n";
            }
            else
            {
                output_code += "    lw t1, " + to_string(get_symbol_entry(m->right_operand->name).stack_addr) + "(s0)\n";
            }
        }
        else
        {
            output_code += "    mv t1, t0\n";
        }
    }
    this->current_scope->used_tmp[1] = true;

    if (lhs.type_set == SET_CONSTANT_LITERAL)
    {
        output_code += "    li t0, " + get_const_value(lhs) + "\n";
    }
    else
    {
        if (typeid(*m->left_operand) == typeid(VariableReferenceNode))
        {
            if (get_symbol_entry(m->left_operand->name).level == 0)
            {
                output_code += "    la t" + to_string(this->current_scope->get_used_tmp() + 1) + ", " + m->left_operand->name + "\n";
                output_code += "    lw t0, 0(t" + to_string(this->current_scope->get_used_tmp() + 1) + ")\n";
            }
            else
            {
                output_code += "    lw t0, " + to_string(get_symbol_entry(m->left_operand->name).stack_addr) + "(s0)\n";
            }
        }
    }
    this->current_scope->used_tmp[0] = true;

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }

    if (fault_type_check(lhs) && fault_type_check(rhs))
    {
        switch (m->op)
        {
        case OP_OR:
        case OP_AND:
        case OP_NOT:
            if ((lhs.type_set == SET_SCALAR ||
                 lhs.type_set == SET_CONSTANT_LITERAL) &&
                (lhs.type == TYPE_BOOLEAN))
            {
                ;
            }
            else
            {
                error = true;
            }
            if ((rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_BOOLEAN))
            {
                ;
            }
            else
            {
                error = true;
            }
            if (error == true)
            {
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "invalid operands to binary operation";
                this->error_msg += " '" + op_convert(m->op) + "' ";
                this->error_msg += "('" + info_convert(lhs) + "' and '" +
                                   info_convert(rhs) + "')\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                break;
            }
            else
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_BOOLEAN));
            }

            break;

        case OP_LESS:
        case OP_LESS_OR_EQUAL:
        case OP_EQUAL:
        case OP_GREATER:
        case OP_GREATER_OR_EQUAL:
        case OP_NOT_EQUAL:
            if ((lhs.type_set == SET_SCALAR ||
                 lhs.type_set == SET_CONSTANT_LITERAL) &&
                (lhs.type == TYPE_INTEGER || lhs.type == TYPE_REAL))
            {
                ;
            }
            else
            {
                error = true;
            }
            if ((rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_INTEGER || rhs.type == TYPE_REAL))
            {
                ;
            }
            else
            {
                error = true;
            }

            if (error == true)
            {
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "invalid operands to binary operation";
                this->error_msg += " '" + op_convert(m->op) + "' ";
                this->error_msg += "('" + info_convert(lhs) + "' and '" +
                                   info_convert(rhs) + "')\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                break;
            }
            else
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_BOOLEAN));
            }

            break;

        case OP_PLUS: // Special Case
            if ((lhs.type_set == SET_SCALAR ||
                 lhs.type_set == SET_CONSTANT_LITERAL) &&
                (lhs.type == TYPE_STRING) &&
                (rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_STRING))
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_STRING));
                break;
            }
            // Forward Check
        case OP_MINUS:
        case OP_MULTIPLY:
        case OP_DIVIDE:
            if ((lhs.type_set == SET_SCALAR ||
                 lhs.type_set == SET_CONSTANT_LITERAL) &&
                (lhs.type == TYPE_INTEGER) &&
                (rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_INTEGER))
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_INTEGER));
                break;
            }
            if ((lhs.type_set == SET_SCALAR ||
                 lhs.type_set == SET_CONSTANT_LITERAL) &&
                (lhs.type == TYPE_INTEGER || lhs.type == TYPE_REAL) &&
                (rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_INTEGER || rhs.type == TYPE_REAL))
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_REAL));
                break;
            }
            else
            {
                error = true;
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "invalid operands to binary operation";
                this->error_msg += " '" + op_convert(m->op) + "' ";
                this->error_msg += "('" + info_convert(lhs) + "' and '" +
                                   info_convert(rhs) + "')\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                break;
            }

            break;

        case OP_MOD:
            if ((lhs.type_set == SET_SCALAR ||
                 lhs.type_set == SET_CONSTANT_LITERAL) &&
                (lhs.type == TYPE_INTEGER))
            {
                ;
            }
            else
            {
                error = true;
            }
            if ((rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_INTEGER))
            {
                ;
            }
            else
            {
                error = true;
            }

            if (error == true)
            {
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "invalid operands to binary operation";
                this->error_msg += " '" + op_convert(m->op) + "' ";
                this->error_msg += "('" + info_convert(lhs) + "' and '" +
                                   info_convert(rhs) + "')\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                break;
            }
            else
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_INTEGER));
            }

            break;

        default:
            break;
        }
    }
    else
    {
        error = true;
    }

    if (error == true)
    {
        // Error Has Happened Before or Now
        this->expression_stack.push(VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));
    }
    else
    {
        ;
    }
    if (!error)
    {
        string output_code;

        switch (m->op)
        {
        case OP_LESS:
            if (this->src_node.top() == IF_NODE)
            {
                output_code += "    bge t0, t1, L" + to_string(this->loop_num + 2) + "\n";
            }
            else
            {
                output_code += "    blt t0, t1, L" + to_string(this->loop_num + 1) + "\n";
            }

            break;
        case OP_LESS_OR_EQUAL:
            if (this->src_node.top() == IF_NODE)
            {
                output_code += "    bgt t0, t1, L" + to_string(this->loop_num + 2) + "\n";
            }
            else
            {
                output_code += "    ble t0, t1, L" + to_string(this->loop_num + 1) + "\n";
            }

            break;
        case OP_EQUAL:
            if (this->src_node.top() == IF_NODE)
            {
                output_code += "    bne t0, t1, L" + to_string(this->loop_num + 2) + "\n";
            }
            else
            {
                output_code += "    beq t0, t1, L" + to_string(this->loop_num + 1) + "\n";
            }

            break;
        case OP_GREATER:
            if (this->src_node.top() == IF_NODE)
            {
                output_code += "    ble t0, t1, L" + to_string(this->loop_num + 2) + "\n";
            }
            else
            {
                output_code += "    bgt t0, t1, L" + to_string(this->loop_num + 1) + "\n";
            }
            break;
        case OP_GREATER_OR_EQUAL:
            if (this->src_node.top() == IF_NODE)
            {
                output_code += "    blt t0, t1, L" + to_string(this->loop_num + 2) + "\n";
            }
            else
            {
                output_code += "    bge t0, t1, L" + to_string(this->loop_num + 1) + "\n";
            }

            break;
        case OP_NOT_EQUAL:
            if (this->src_node.top() == IF_NODE)
            {
                output_code += "    beq t0, t1, L" + to_string(this->loop_num + 2) + "\n";
            }
            else
            {
                output_code += "    bne t0, t1, L" + to_string(this->loop_num + 1) + "\n";
            }

            break;
        case OP_PLUS:
            output_code += "    addw t2, t1, t0\n";
            output_code += "    mv t0, t2\n";
            break;
        case OP_MINUS:
            output_code += "    subw t2, t1, t0\n";
            output_code += "    mv t0, t2\n";
            break;
        case OP_MULTIPLY:
            output_code += "    mulw t2, t1, t0\n";
            output_code += "    mv t0, t2\n";
            break;
        case OP_DIVIDE:
            output_code += "    divw t2, t1, t0\n";
            output_code += "    mv t0, t2\n";
            break;
        case OP_MOD:
            output_code += "    remw t2, t1, t0\n";
            output_code += "    mv t0, t2\n";
            break;

        default:
            break;
        }

        this->current_scope->used_tmp[0] = false;
        this->current_scope->used_tmp[1] = false;
        this->current_scope->used_tmp[2] = false;
        if (this->current_scope->in_node_type != FUNCTION_NODE)
        {
            this->main.push_back(output_code);
        }
        else
        {
            this->function.push_back(output_code);
        }
    }
}

void SemanticAnalyzer::visit(UnaryOperatorNode *m)
{ // EXPRESSION
    // Visit Child Node
    this->push_src_node(UNARY_OPERATOR_NODE);
    if (m->operand != nullptr)
        m->operand->accept(*this);
    this->pop_src_node();

    // Semantic Check // Expression Stack
    VariableInfo rhs = this->expression_stack.top();
    this->expression_stack.pop();
    bool error = false;

    if (fault_type_check(rhs))
    {
        switch (m->op)
        {
        case OP_NOT:
            if ((rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_BOOLEAN))
            {
                ;
            }
            else
            {
                error = true;
            }
            if (error == true)
            {
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "invalid operand to unary operation";
                this->error_msg += " '" + op_convert(m->op) + "' ";
                this->error_msg += "('" + info_convert(rhs) + "')\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                break;
            }
            else
            {
                this->expression_stack.push(
                    VariableInfo(SET_SCALAR, TYPE_BOOLEAN));
            }

            break;

        case OP_MINUS:
            if ((rhs.type_set == SET_SCALAR ||
                 rhs.type_set == SET_CONSTANT_LITERAL) &&
                (rhs.type == TYPE_INTEGER || rhs.type == TYPE_REAL))
            {
                this->expression_stack.push(VariableInfo(SET_SCALAR, rhs.type));
                break;
            }
            else
            {
                error = true;
                this->semantic_error = 1;
                this->error_msg +=
                    error_found_msg(m->line_number, m->col_number);
                this->error_msg += "invalid operands to unary operation";
                this->error_msg += " '" + op_convert(m->op) + "' ";
                this->error_msg += "('" + info_convert(rhs) + "')\n";
                this->error_msg +=
                    src_notation_msg(this->fp, m->line_number, m->col_number);
                break;
            }

            break;

        default:
            break;
        }
    }
    else
    {
        error = true;
    }

    if (error == true)
    {
        // Error Has Happened Before or Now
        this->expression_stack.push(VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));
    }
    else
    {
        ;
    }
}

void SemanticAnalyzer::visit(IfNode *m)
{ // STATEMENT
    // Visit Child Nodes
    this->push_src_node(IF_NODE);
    if (m->condition != nullptr)
        m->condition->accept(*this);

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back("L" + to_string(this->loop_num + 1) + ":\n");
    }
    else
    {
        this->function.push_back("L" + to_string(this->loop_num + 1) + ":\n");
    }

    if (m->body != nullptr)
        for (uint i = 0; i < m->body->size(); i++)
            (*(m->body))[i]->accept(*this);

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back("    j L" + to_string(this->loop_num + 3) + "\n");
        this->main.push_back("L" + to_string(this->loop_num + 2) + ":\n");
    }
    else
    {
        this->function.push_back("    j L" + to_string(this->loop_num + 3) + "\n");
        this->function.push_back("L" + to_string(this->loop_num + 2) + ":\n");
    }

    if (m->body_of_else != nullptr)
        for (uint i = 0; i < m->body_of_else->size(); i++)
            (*(m->body_of_else))[i]->accept(*this);

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back("L" + to_string(this->loop_num + 3) + ":\n");
    }
    else
    {
        this->function.push_back("L" + to_string(this->loop_num + 3) + ":\n");
    }
    this->loop_num += 3;
    this->pop_src_node();

    // Semantic Check
    VariableInfo tmpInfo = this->expression_stack.top();
    this->expression_stack.pop();

    if (tmpInfo.type_set == UNKNOWN_SET && tmpInfo.type == UNKNOWN_TYPE)
    {
        return; // No Need Further Check
    }

    if (tmpInfo.type != TYPE_BOOLEAN)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->condition->line_number,
                                           m->condition->col_number);
        this->error_msg += "the expression of condition must be boolean type\n";
        this->error_msg += src_notation_msg(this->fp, m->condition->line_number,
                                            m->condition->col_number);
    }
}

void SemanticAnalyzer::visit(WhileNode *m)
{ // STATEMENT
    // Visit Child Nodes
    this->push_src_node(WHILE_NODE);
    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back("    j L" + to_string(this->loop_num + 2) + "\n");
        this->main.push_back("L" + to_string(this->loop_num + 1) + ":\n");
    }
    else
    {
        this->function.push_back("    j L" + to_string(this->loop_num + 2) + "\n");
        this->function.push_back("L" + to_string(this->loop_num + 1) + ":\n");
    }

    if (m->body != nullptr)
        for (uint i = 0; i < m->body->size(); i++)
            (*(m->body))[i]->accept(*this);

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back("L" + to_string(this->loop_num + 2) + ":\n");
    }
    else
    {
        this->function.push_back("L" + to_string(this->loop_num + 2) + ":\n");
    }

    if (m->condition != nullptr)
        m->condition->accept(*this);

    this->loop_num += 2;
    this->pop_src_node();

    // Semantic Check
    VariableInfo tmpInfo = this->expression_stack.top();
    this->expression_stack.pop();

    if (tmpInfo.type_set == UNKNOWN_SET && tmpInfo.type == UNKNOWN_TYPE)
    {
        return; // No Need Further Check
    }

    if (tmpInfo.type != TYPE_BOOLEAN)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->condition->line_number,
                                           m->condition->col_number);
        this->error_msg += "the expression of condition must be boolean type\n";
        this->error_msg += src_notation_msg(this->fp, m->condition->line_number,
                                            m->condition->col_number);
    }
}

void SemanticAnalyzer::visit(ForNode *m)
{ // STATEMENT
    // Push Scope
    this->level_up();
    SymbolTable *new_scope = new SymbolTable(this->level);
    this->push(new_scope, FOR_NODE, VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));

    // Visit Child Node
    this->push_src_node(FOR_NODE);
    this->specify_on(KIND_LOOP_VAR);
    if (m->loop_variable_declaration != nullptr)
        m->loop_variable_declaration->accept(*this);
    this->specify_off();

    this->specify_on(KIND_LOOP_VAR);
    if (m->initial_statement != nullptr)
        m->initial_statement->accept(*this);
    this->specify_off();

    if (m->condition != nullptr)
        m->condition->accept(*this);

    string output_code;

    output_code += "    li t0, " + to_string(m->lower_bound) + "\n";
    output_code += "    sw t0, " + to_string(this->current_scope->current_stack_addr) + "(s0)\n";
    output_code += "    j L" + to_string(this->loop_num + 2) + "\n";
    output_code += "L" + to_string(this->loop_num + 1) + ":\n";
    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }

    if (m->body != nullptr)
        for (uint i = 0; i < m->body->size(); i++)
            (*(m->body))[i]->accept(*this);


    output_code = "L" + to_string(this->loop_num + 2) + ":\n";
    output_code += "    lw t0, " + to_string(this->current_scope->current_stack_addr) + "(s0)\n";
    output_code += "    li t1, 1\n";
    output_code += "    addw t2, t1, t0\n";
    output_code += "    mv t0, t2\n";
    output_code += "    sw t0, " + to_string(this->current_scope->current_stack_addr) + "(s0)\n";
    output_code += "    li t1, " + to_string(m->upper_bound) + "\n";
    output_code += "    ble t0, t1, L" + to_string(this->loop_num + 1) + "\n";
    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }
    this->pop_src_node();

    // Semantic Check
    if (m->lower_bound > m->upper_bound)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->line_number, m->col_number);
        this->error_msg += "the lower bound of iteration count must be smaller "
                           "than or equal to the upper bound\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);
    }
    this->current_scope->current_stack_addr -= 4;
    this->loop_num += 2;
    // Pop Scope
    this->pop();
    this->level_down();
}

void SemanticAnalyzer::visit(ReturnNode *m)
{ // STATEMENT
    // Visit Child Node
    this->push_src_node(RETURN_NODE);
    if (m->return_value != nullptr)
        m->return_value->accept(*this);
    this->pop_src_node();

    // Semantic Check Error
    VariableInfo r_type = this->expression_stack.top();
    this->expression_stack.pop();

    if (r_type.type_set == UNKNOWN_SET && r_type.type == UNKNOWN_TYPE)
    {
        return; // No Need Further Check
    }

    if (check_program_or_procedure_call() == true)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->line_number, m->col_number);
        this->error_msg += "program/procedure should not return a value\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);
        return;
    }

    VariableInfo returnTypeInfo = get_function_return_type();
    if ((r_type.type_set == SET_ACCUMLATED) ||
        (r_type.type != returnTypeInfo.type))
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->return_value->line_number,
                                           m->return_value->col_number);
        this->error_msg += "return '" + info_convert(r_type) +
                           "' from a function with return type '" +
                           info_convert(returnTypeInfo) + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->return_value->line_number,
                             m->return_value->col_number);
        return;
    }

    string output_code;
    if (r_type.type_set == SET_CONSTANT_LITERAL)
    {
        output_code += "    li a0, " + get_const_value(r_type) + "\n";
    }
    else
    {

        //output_code += "    sw t0, " + to_string(this->current_scope->get_entry(m->return_value->name).stack_addr) + "(s0)\n";
        output_code += "    lw a0, " + to_string(this->current_scope->get_entry(m->return_value->name).stack_addr) + "(s0)\n";
    }

    if (this->current_scope->in_node_type != FUNCTION_NODE)
    {
        this->main.push_back(output_code);
    }
    else
    {
        this->function.push_back(output_code);
    }
}

void SemanticAnalyzer::visit(FunctionCallNode *m)
{ // EXPRESSION //STATEMENT
    // Visit Child Node
    this->push_src_node(FUNCTION_CALL_NODE);
    if (m->arguments != nullptr)
        for (int i = m->arguments->size() - 1; i >= 0; i--) // REVERSE TRAVERSE
        {
            (*(m->arguments))[i]->accept(*this);
        }

    if (m->arguments != nullptr)
    {
        string output_code;
        for (int i = m->arguments->size() - 1; i >= 0; i--)
        {
            switch (this->current_scope->get_entry((*(m->arguments))[m->arguments->size() - 1 - i]->name).kind)
            {
            case KIND_CONSTANT:
                output_code += "    lw a" + to_string(m->arguments->size() - 1 - i) + ", " + to_string(this->current_scope->get_entry((*(m->arguments))[m->arguments->size() - 1 - i]->name).stack_addr) + "(s0)\n";
                break;
            case KIND_PARAMETER:
                output_code += "    lw a" + to_string(m->arguments->size() - 1 - i) + ", " + to_string(this->current_scope->get_entry((*(m->arguments))[m->arguments->size() - 1 - i]->name).stack_addr) + "(s0)\n";
                break;
            case KIND_VARIABLE:
                if (this->current_scope->get_entry((*(m->arguments))[m->arguments->size() - 1 - i]->name).level == 0)
                {
                    output_code += "    la t" + to_string(this->current_scope->get_used_tmp()) + ", " + (*(m->arguments))[m->arguments->size() - 1 - i]->name + "\n";
                    output_code += "    lw a" + to_string(m->arguments->size() - 1 - i) + ", 0(t" + to_string(this->current_scope->get_used_tmp()) + ")\n";
                }
                else
                {
                    output_code += "    lw a" + to_string(m->arguments->size() - 1 - i) + ", " + to_string(this->current_scope->get_entry((*(m->arguments))[m->arguments->size() - 1 - i]->name).stack_addr) + "(s0)\n";
                }
                break;
            case KIND_UNKNOWN:
                if ((*(m->arguments))[m->arguments->size() - 1 - i]->name.length() > 0)
                {
                    output_code += "    la t" + to_string(this->current_scope->get_used_tmp()) + ", " + (*(m->arguments))[m->arguments->size() - 1 - i]->name + "\n";
                    output_code += "    lw a" + to_string(m->arguments->size() - 1 - i) + ", 0(t" + to_string(this->current_scope->get_used_tmp()) + ")\n";
                }
                else
                {
                    output_code += "    lw a" + to_string(m->arguments->size() - 1 - i) + ", " + to_string(this->tmp_return_value.top()) + "(s0)\n";
                    this->tmp_return_value.pop();
                }
                break;

            default:
                break;
            }
        }
        output_code += "    jal ra, " + m->function_name + "\n";
        output_code += "    mv t0, a0\n";
        output_code += "    sw t0, " + to_string(this->current_scope->current_stack_addr) + "(s0)\n";

        this->tmp_return_value.push(this->current_scope->current_stack_addr);
        this->current_scope->current_stack_addr -= 4;
        this->current_scope->used_tmp[this->current_scope->get_used_tmp()] = true;
        if (this->current_scope->in_node_type != FUNCTION_NODE)
        {
            this->main.push_back(output_code);
        }
        else
        {
            this->function.push_back(output_code);
        }
    }

    this->pop_src_node();

    // Semantic Check
    if (check_function_declaration(m->function_name) == false)
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->line_number, m->col_number);
        this->error_msg += "used of undeclared function '" +
                           name_cut(m->function_name) + "'\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);

        this->expression_stack.push(VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));

        return;
    }

    SymbolEntry tmpEntry =
        this->symbol_table_root->next_scope_list[0]->entry[m->function_name];
    unsigned int arguments_size;

    if (m->arguments != nullptr)
        arguments_size = m->arguments->size();
    else
        arguments_size = 0;

    if (arguments_size != tmpEntry.function_node->prototype.size())
    {
        this->semantic_error = 1;
        this->error_msg += error_found_msg(m->line_number, m->col_number);
        this->error_msg += "too few/much arguments to function invocation\n";
        this->error_msg +=
            src_notation_msg(this->fp, m->line_number, m->col_number);

        this->expression_stack.push(VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));

        return;
    }

    bool error_found = false;
    for (uint i = 0; i < tmpEntry.function_node->prototype.size(); i++)
    {
        VariableInfo tmpInfo = this->expression_stack.top();
        this->expression_stack.pop();

        if (error_found == false)
        {
            switch (tmpInfo.type_set)
            {
            case SET_ACCUMLATED:
                if (array_size_check(tmpInfo,
                                     *(tmpEntry.function_node->prototype[i])) ==
                    false)
                {
                    this->semantic_error = 1;
                    this->error_msg +=
                        error_found_msg(m->arguments->at(i)->line_number,
                                        m->arguments->at(i)->col_number);
                    this->error_msg +=
                        "incompatible types passing '" + info_convert(tmpInfo);
                    this->error_msg +=
                        "' to parameter of type '" +
                        info_convert(*(tmpEntry.function_node->prototype[i])) +
                        "'\n";
                    error_found = true;
                }
                break;
            case SET_SCALAR:
            case SET_CONSTANT_LITERAL:
                if (tmpInfo.type !=
                    tmpEntry.function_node->prototype[i]->type)
                {
                    this->semantic_error = 1;
                    this->error_msg +=
                        error_found_msg(m->arguments->at(i)->line_number,
                                        m->arguments->at(i)->col_number);
                    this->error_msg +=
                        "incompatible types passing '" + info_convert(tmpInfo);
                    this->error_msg +=
                        "' to parameter of type '" +
                        info_convert(*(tmpEntry.function_node->prototype[i])) +
                        "'\n";
                    error_found = true;
                }
                break;
            case UNKNOWN_SET:
            default:
                error_found = true;
                break;
            }
        }
    }

    // Push Expression Stack
    if (error_found == false)
    {
        VariableInfo tmpInfo = *(tmpEntry.function_node->return_type);
        this->expression_stack.push(tmpInfo);
    }
    else
    {
        this->expression_stack.push(VariableInfo(UNKNOWN_SET, UNKNOWN_TYPE));
    }
}
