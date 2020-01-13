#pragma once
#include <cstdio>
#include <string>
using namespace std;

//
// Error Message
//

string error_found_msg(uint32_t x, uint32_t y);
string src_notation_msg(FILE *fp, uint32_t line_num, uint32_t col_num);
string redeclare_error_msg(uint32_t x, uint32_t y, string symbol_name);