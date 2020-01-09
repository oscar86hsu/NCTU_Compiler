#ifndef __AST_H
#define __AST_H

#include "AST/PType.h"
#include "AST/constant.h"

#include <stdbool.h>
#include <stdint.h>

#define AST_NODE_MEMBERS                                                       \
    Location location;                                                         \
    AcceptFPtr accept;                                                         \
    DestructFPtr free

#define ANONYMOUS_AST_NODE                                                     \
    struct {                                                                   \
        AST_NODE_MEMBERS;                                                      \
    }

#define CONSTRUCT_AST_NODE(NODE)                                               \
    (NODE).location.line = line;                                               \
    (NODE).location.col = col;                                                 \
    (NODE).accept = accept;                                                    \
    (NODE).free = destruct

extern const uint32_t kBufferSize;
extern const char *kTFString[];
extern const char *kOpString[];

/************************
 * Forward Declaration
 ************************/
struct __AstNode;
struct __AstNodeVisitor;
struct __List;

/*****************************************************************************
 * Sub Data Structure: Data structures that help to deliver semantic value to
 *                     AstNode.
 *****************************************************************************/
typedef void (*AcceptFPtr)(struct __AstNode *this,
                           struct __AstNodeVisitor *visitor);
typedef void (*DestructFPtr)(struct __AstNode *this);
typedef struct __List *IdentifierInfoList;

typedef enum __Operator {
    NEG_OP,
    MULTIPLY_OP,
    DIVIDE_OP,
    MOD_OP,
    PLUS_OP,
    MINUS_OP,
    LESS_OP,
    LESS_OR_EQUAL_OP,
    GREATER_OP,
    GREATER_OR_EQUAL_OP,
    EQUAL_OP,
    NOT_EQUAL_OP,
    NOT_OP,
    AND_OP,
    OR_OP
} Operator;

/************************
 * Main Data Structure
 ************************/
typedef struct __Location {
    uint32_t line;
    uint32_t col;
} Location;

// Only used to carry location info with semantic value
typedef struct __ConstantInfo {
    Location location;
    Constant *constant;
} ConstantInfo;

// Only used to carry location info with semantic value
typedef struct __IdentifierInfo {
    Location location;
    char *identifier;
} IdentifierInfo;

typedef struct __AstNode {
    AST_NODE_MEMBERS;
} AstNode;

void setAstNode(struct __AstNode *node, uint32_t line, uint32_t col,
                AcceptFPtr accept, DestructFPtr free);

IdentifierInfo *newIdentifierInfo(uint32_t line, uint32_t col, char *id);
void freeIdentifierInfo(void *ptr);

void freeAstNode(void *node);

#endif
