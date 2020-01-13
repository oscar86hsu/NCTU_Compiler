#include <cstdio>
#include <semantic/ErrorMsg.hpp>
#include <string>
using namespace std;

//
// Error Message
//

string error_found_msg(uint32_t x, uint32_t y) {
    string temp = "";
    temp += "<Error> Found in line ";
    temp += to_string(x);
    temp += ", column ";
    temp += to_string(y);
    temp += ": ";
    return temp;
}

string src_notation_msg(FILE *fp, uint32_t line_num, uint32_t col_num) {
    string temp = "";
    char buffer[1024];
    fseek(fp, 0, SEEK_SET); // Back to Start
    for (uint i = 0; i < line_num; i++) {
        fgets(buffer, 1024, fp);
    }

    temp += "    ";
    temp += string(buffer);

    temp += "    ";
    for (uint i = 0; i < col_num - 1; i++)
        temp += " ";

    temp += "^\n";
    return temp;
}

string redeclare_error_msg(uint32_t x, uint32_t y, string symbol_name) {
    string temp = "";
    if (symbol_name.length() > 32)
        symbol_name = symbol_name.substr(0, 32);
    temp += "<Error> Found in line ";
    temp += to_string(x);
    temp += ", column ";
    temp += to_string(y);
    temp += ": symbol '";
    temp += symbol_name;
    temp += "' is redeclared";
    temp += "\n";
    return temp;
}
