#pragma once

#include "visitor/visitor.hpp"
#include <memory>
#include <string>
#include <vector>

#define SAFE_DELETE(NODE)                                                      \
    if ((NODE) != nullptr) {                                                   \
        delete (NODE);                                                         \
        (NODE) = nullptr;                                                      \
    }

#define NODELIST_PTR_DELETE(NODELIST_PTR)                                      \
    if ((NODELIST_PTR) != nullptr) {                                           \
        for (uint i = 0; i < (NODELIST_PTR)->size(); i++) {                    \
            delete (*(NODELIST_PTR))[i];                                       \
            (*(NODELIST_PTR))[i] = nullptr;                                    \
        }                                                                      \
        delete (NODELIST_PTR);                                                 \
        (NODELIST_PTR) = nullptr;                                              \
    }

using namespace std;

typedef vector<class ASTNodeBase *> NodeList;
typedef class ASTNodeBase *Node;

enum enumOperator {
    OP_ASSIGN = 500,
    OP_OR,
    OP_AND,
    OP_NOT,
    OP_LESS,
    OP_LESS_OR_EQUAL,
    OP_EQUAL,
    OP_GREATER,
    OP_GREATER_OR_EQUAL,
    OP_NOT_EQUAL,
    OP_PLUS,
    OP_MINUS,
    OP_MULTIPLY,
    OP_DIVIDE,
    OP_MOD,
    UNKNOWN_OP
};

enum EnumTypeSet {
    SET_SCALAR = 300,
    SET_ACCUMLATED,
    SET_CONSTANT_LITERAL,
    UNKNOWN_SET
};

enum EnumType {
    TYPE_INTEGER = 400,
    TYPE_REAL,
    TYPE_STRING,
    TYPE_BOOLEAN,
    TYPE_VOID,
    UNKNOWN_TYPE
};

struct IntPair {
    int start;
    int end;
};

enum BooleanLiteral { Boolean_TRUE = 400, Boolean_FALSE, UNKNOWN };

struct VariableInfo {
    EnumTypeSet type_set;
    EnumType type;
    vector<IntPair> array_range;
    int int_literal;
    double real_literal;
    string string_literal;
    BooleanLiteral boolean_literal;

    VariableInfo() {
        this->type_set = UNKNOWN_SET;
        this->type = UNKNOWN_TYPE;
    }

    VariableInfo(EnumTypeSet _type_set, EnumType _type) {
        this->type_set = _type_set;
        this->type = _type;
    }

    VariableInfo(EnumTypeSet _type_set, EnumType _type, int _int_literal) {
        this->type_set = _type_set;
        this->type = _type;
        this->int_literal = _int_literal;
    }

    VariableInfo(EnumTypeSet _type_set, EnumType _type, double _real_literal) {
        this->type_set = _type_set;
        this->type = _type;
        this->real_literal = _real_literal;
    }

    VariableInfo(EnumTypeSet _type_set, EnumType _type,
                 string _string_literal) {
        this->type_set = _type_set;
        this->type = _type;
        this->string_literal = _string_literal;
    }

    VariableInfo(EnumTypeSet _type_set, EnumType _type,
                 BooleanLiteral _boolean_literal) {
        this->type_set = _type_set;
        this->type = _type;
        this->boolean_literal = _boolean_literal;
    }
};

struct NodeWithTypeList {
    Node node;
    VariableInfo *type;
    uint counter;
};

class ASTNodeBase {
  public:
    int line_number;
    int col_number;
    string name;

  public:
    virtual void accept(class ASTVisitorBase &v) = 0;
    virtual ~ASTNodeBase(){};
};