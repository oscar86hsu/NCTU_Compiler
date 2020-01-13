#pragma once
#include "AST/ast.hpp"
#include "semantic/SymbolTable.hpp"

//
// TODO: Dump Function
//

string name_cut(string _name);
bool array_size_check(VariableInfo lhs, VariableInfo rhs);
bool fault_type_check(VariableInfo input);
string info_convert(VariableInfo input);
string op_convert(enum enumOperator op);

void dumpDemarcation(const char chr);
void dumpSymbol_Header();
void dumpSymbol_Body(SymbolEntry symbol_entry);
void dumpSymbol_Bottom();
