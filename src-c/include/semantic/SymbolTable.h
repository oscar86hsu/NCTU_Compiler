#ifndef __SYMBOL_TABLE_H
#define __SYMBOL_TABLE_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/************************
 * Forward Declaration
 ************************/
struct __List;
struct __PType;

/************************
 * Type Definition
 ************************/
typedef struct __Attribute {
    // There are two attributes:
    //   Constant * for constant value,
    //   List * for parameters
    const void *data;

    const char *(*interpret)(struct __Attribute *);
} Attribute;

typedef enum __SymbolKind {
    PROGRAM_SYMBOL,
    FUNCTION_SYMBOL,
    PARAMETER_SYMBOL,
    VARIABLE_SYMBOL,
    LOOP_VAR_SYMBOL,
    CONSTANT_SYMBOL
} SymbolKind;

typedef struct __SymbolEntry {
    const char *name;
    SymbolKind kind;
    size_t level;
    const struct __PType *type;
    Attribute attribute;
    bool has_error;

    // Record the outer symbol
    struct __SymbolEntry *prev;
} SymbolEntry;

typedef struct __SymbolTable {
    struct __SymbolEntry **entries;
    size_t size;
    size_t capacity;

    struct __SymbolTable *parent;
    struct __SymbolTable *child;
    struct __SymbolTable *sibling;

    bool (*addSymbol)(struct __SymbolTable *this, const char *name,
                      SymbolKind kind, size_t cur_level,
                      const struct __PType *type, const void *attributes);
} SymbolTable;

typedef struct __SymbolManager {
    /*
     * Use tree structure to store symbol tables
     *   - parent-child represents the scopes that have different depths
     *   - siblings represents the scopes that have the same depth
     */
    SymbolTable *root;
    SymbolTable **indirect_next_table;
    SymbolTable *current_table;
    size_t current_level;

    void (*pushScope)(struct __SymbolManager *this);
    void (*popScope)(struct __SymbolManager *this);
    void (*nextScope)(struct __SymbolManager *this);
    void (*prevScope)(struct __SymbolManager *this);
    bool (*addSymbol)(struct __SymbolManager *this, const char *name,
                      SymbolKind kind, const struct __PType *type,
                      const void *attributes);
    SymbolEntry *(*lookup)(struct __SymbolManager *this, const char *name);
} SymbolManager;

/************************
 * Public Function
 ************************/
SymbolManager *newSymbolManager(void);
void freeSymbolManager(SymbolManager *);

#endif
