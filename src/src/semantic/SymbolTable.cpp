#include "semantic/SymbolTable.hpp"
#include "semantic/DumpSymbolTable.hpp"

Attribute::Attribute() { this->attr_type = UNKNOWN_ATTRIBUTE; }

Attribute::Attribute(AttributeType _attr_type) { this->attr_type = _attr_type; }

Attribute::Attribute(vector<VariableInfo> _parameters) {
    this->parameter_type = _parameters;
    this->attr_type = ATTRIBUTE_PARAMETERS;
}

Attribute::Attribute(VariableInfo _value) {
    this->value_of_constant = _value;
    this->attr_type = ATTRIBUTE_VALUE_OF_CONSTANT;
}

void Attribute::set_parameter_type(vector<VariableInfo> _parameters) {
    this->parameter_type = _parameters;
    this->attr_type = ATTRIBUTE_PARAMETERS;
}

void Attribute::set_value_of_constant(VariableInfo _value) {
    this->value_of_constant = _value;
    this->attr_type = ATTRIBUTE_VALUE_OF_CONSTANT;
}

SymbolEntry::SymbolEntry() {
    this->kind = KIND_UNKNOWN;
    this->is_used = false;
}

SymbolEntry::SymbolEntry(string _name, FieldKind _kind, unsigned int _level,
                         VariableInfo _type, Attribute _attribute,
                         enum EnumNodeTable _node_type,
                         class ProgramNode *_program_node,
                         class VariableNode *_variable_node,
                         class FunctionNode *_function_node,
                         int _stack_addr) {
    this->name = name_cut(_name);
    this->kind = _kind;
    this->level = _level;
    this->type = _type;
    this->attribute = _attribute;
    this->node_type = _node_type;
    this->program_node = _program_node;
    this->variable_node = _variable_node;
    this->function_node = _function_node;
    this->stack_addr = _stack_addr;

    this->is_used = true;
    this->is_arr_decl_error = false;
}

SymbolTable::SymbolTable(unsigned int _level) {
    this->prev_scope = NULL;
    this->next_scope_list.clear();
    this->level = _level;
    this->entry.clear();
    this->entry_name.clear();
}

SymbolTable::~SymbolTable() {
    for (uint i = 0; i < this->next_scope_list.size(); i++) {
        SAFE_DELETE(this->next_scope_list[i])
    }
}

void SymbolTable::put(SymbolEntry _symbol_entry) {
    this->entry[_symbol_entry.name] = _symbol_entry;
    this->entry_name.push_back(_symbol_entry.name);
}

// Check the Variable is Redeclared Before
// false -> redeclare happen
bool SymbolTable::redeclare_check(string _name) {
    if (_name.length() > 32)
        _name = _name.substr(0, 32);
    if (this->entry[_name].is_used == true) {
        return false;
    } else {
        return true;
    }
}

SymbolEntry SymbolTable::get_entry(string _name) {
    return this->entry[_name];
}

bool SymbolTable::check_entry(string _name) {
    return this->entry[_name].is_used;
}

int SymbolTable::get_used_tmp()
{
    for (int i = 1; i < 16; i++)
    {
        if (!this->used_tmp[i])
            return i;
    }
}