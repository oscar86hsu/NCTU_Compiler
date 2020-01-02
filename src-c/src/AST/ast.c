#include "AST/ast.h"
#include "core/list.h"
#include "core/utils.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const uint32_t kBufferSize = 1024u;
const char *kTFString[] = {"false", "true"};
const char *kOpString[] = {"neg", "*",  "/", "mod", "+",   "-",   "<", "<=",
                           ">",   ">=", "=", "<>",  "not", "and", "or"};

void setAstNode(AstNode *node, uint32_t line, uint32_t col, AcceptFPtr accept,
                DestructFPtr free) {
    node->location.line = line;
    node->location.col = col;
    node->accept = accept;
    node->free = free;
}

IdentifierInfo *newIdentifierInfo(uint32_t line, uint32_t col, char *id) {
    IdentifierInfo *id_info =
        (IdentifierInfo *)myMalloc(sizeof(IdentifierInfo));
    id_info->location.line = line;
    id_info->location.col = col;
    id_info->identifier = id;
    return id_info;
}

// Only carry info of location with id, doesn't own the pointer of id
void freeIdentifierInfo(void *ptr) { free(ptr); }

void freeAstNode(void *node) {
    if (node == NULL) {
        return;
    }

    AstNode *n = (AstNode *)node;
    n->free(n);
}
