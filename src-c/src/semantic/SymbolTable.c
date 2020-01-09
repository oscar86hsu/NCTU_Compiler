#include "semantic/SymbolTable.h"
#include "AST/ast.h"
#include "AST/declaration.h"
#include "AST/function.h"
#include "AST/variable.h"
#include "core/hash.h"
#include "core/list.h"
#include "core/utils.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int32_t OptDmp;
static const size_t kBasicEntrySize = 16;
static HashTable *_HashTable;

/************************
 * Function Definition
 ************************/
static const char *interpretConstant(Attribute *attr) {
    const Constant *constant = (const Constant *)attr->data;

    if (constant == NULL) {
        return "";
    }

    return constant->getConstantValueString(constant);
}

static const char *interpretParameters(Attribute *attr) {
    List *parameters = (List *)attr->data;

    if (parameters->size(parameters) == 0u) {
        return "";
    }

    return getParametersTypeString(parameters);
}

static const char *interpretNothing(Attribute *attr) { return ""; }

static SymbolEntry *newSymbolEntry(SymbolEntry *data) {
    SymbolEntry *se = (SymbolEntry *)myMalloc(sizeof(SymbolEntry));

    memcpy(se, data, sizeof(SymbolEntry));

    return se;
}

static bool addSymbolInternal(SymbolTable *this, const char *name,
                              SymbolKind kind, size_t cur_level,
                              const PType *type, const void *attributes) {
    HashBucket *it = (HashBucket *)_HashTable->find(_HashTable, name);
    SymbolEntry *old_entry = NULL;

    if (it != NULL) {
        old_entry = it->value;
        if (old_entry->level == cur_level ||
            old_entry->kind == LOOP_VAR_SYMBOL) {
            return false;
        }
    }

    SymbolEntry *new_entry =
        newSymbolEntry(&(SymbolEntry){.name = name,
                                      .kind = kind,
                                      .level = cur_level,
                                      .type = type,
                                      .attribute.data = attributes,
                                      .has_error = false,
                                      .prev = old_entry});
    if (kind == CONSTANT_SYMBOL) {
        new_entry->attribute.interpret = interpretConstant;
    } else if (kind == FUNCTION_SYMBOL) {
        new_entry->attribute.interpret = interpretParameters;
    } else {
        new_entry->attribute.interpret = interpretNothing;
    }
    this->entries[this->size++] = new_entry;
    _HashTable->insert(_HashTable, name, new_entry, it);

    return true;
}

static SymbolTable *newSymbolTable(SymbolTable *parent) {
    SymbolTable *st = (SymbolTable *)myMalloc(sizeof(SymbolTable));
    st->entries =
        (SymbolEntry **)myMalloc(sizeof(SymbolEntry *) * kBasicEntrySize);
    st->size = 0u;
    st->capacity = kBasicEntrySize;
    st->parent = parent;
    st->child = NULL;
    st->sibling = NULL;
    st->addSymbol = addSymbolInternal;

    return st;
}

static void freeSymbolTable(SymbolTable *st) {
    if (st) {
        freeSymbolTable(st->child);
        freeSymbolTable(st->sibling);

        for (size_t i = 0; i < st->size; ++i) {
            free(st->entries[i]);
        }
        free(st->entries);
        free(st);
    }
}

static inline void dumpSymbolTable(SymbolTable *st) {
    if (!OptDmp) {
        return;
    }

    static const char *kind_strings[] = {"program",  "function", "parameter",
                                         "variable", "loop_var", "constant"};

    fprintf(stdout, "=========================================================="
                    "====================================================\n");
    fprintf(stdout, "%-33s%-11s%-11s%-17s%-11s\n", "Name", "Kind", "Level",
            "Type", "Attribute");
    fprintf(stdout, "----------------------------------------------------------"
                    "----------------------------------------------------\n");
    for (size_t i = 0; i < st->size; ++i) {
        SymbolEntry *se = st->entries[i];

        fprintf(stdout, "%-33s", se->name);
        fprintf(stdout, "%-11s", kind_strings[se->kind]);
        fprintf(stdout, "%lu%-10s", se->level,
                (se->level) ? "(local)" : "(global)");
        fprintf(stdout, "%-17s",
                se->type->getPTypeString(se->type, /* compactOrNot */ true));
        fprintf(stdout, "%-11s", se->attribute.interpret(&se->attribute));
        puts("");
    }
    fprintf(stdout, "----------------------------------------------------------"
                    "----------------------------------------------------\n");
}

static void pushScope(SymbolManager *this) {
    SymbolTable *new_scope = newSymbolTable(this->current_table);

    // write to member 'child' of current table or member 'sibling' of child
    // table of current table
    *(this->indirect_next_table) = new_scope;

    this->indirect_next_table = &new_scope->child;
    this->current_table = new_scope;
    this->current_level++;
}

// Dump the current table and change the status of symbol manager only (memory
// release is left to destruction of SymbolManager)
static void popScope(SymbolManager *this) {
    dumpSymbolTable(this->current_table);
    this->prevScope(this);
}

static void reconstructHashTableUsingSymbolTable(SymbolTable *st) {
    for (size_t i = 0; i < st->size; ++i) {
        SymbolEntry *se = st->entries[i];
        HashBucket *it = (HashBucket *)_HashTable->find(_HashTable, se->name);
        _HashTable->insert(_HashTable, se->name, se, it);
    }
}

/*
 * Simulate the change of the status of symbol manager during symbol table
 * construction.
 *
 * The member 'indirect_next_table' is well set by prevScope().
 *
 * Can be used only after all symbol tables have been constructed.
 */
static void nextScope(SymbolManager *this) {
    assert((*(this->indirect_next_table) != NULL) &&
           "cannot use this method without constructing the symbol tables or "
           "there are no more inner or adjacent tables.");

    this->current_table = *(this->indirect_next_table);
    this->indirect_next_table = &this->current_table->child;
    this->current_level++;
    reconstructHashTableUsingSymbolTable(this->current_table);
}

static inline void removeSymbolsFromHashTable(SymbolTable *st) {
    for (size_t i = 0; i < st->size; ++i) {
        SymbolEntry *se = st->entries[i];
        HashBucket *it = _HashTable->find(_HashTable, se->name);
        assert(it != NULL && "Cannot remove the symbol which does not exist.");

        if (se->prev) {
            // Reset the outer symbol hidden before
            _HashTable->insert(_HashTable, se->prev->name, se->prev, it);
        } else {
            // clang-format off
            _HashTable->delete(_HashTable, se->name);
            // clang-format on
        }
    }
}

/*
 * Simulate the change of the status of symbol manager during symbol table
 * destruction but without dumping symbol table.
 */
static void prevScope(SymbolManager *this) {
    assert((this->current_table != NULL) &&
           "If happens, it means that the uses of prevScope() is more than the "
           "ones of pushScope().");

    SymbolTable *ct = this->current_table;

    removeSymbolsFromHashTable(ct);
    this->current_table = ct->parent;
    this->indirect_next_table = (ct->parent) ? &ct->sibling : &this->root;
    this->current_level--;
}

static void needEnlargeSymbolEntry(SymbolTable *st) {
    if (st->size == st->capacity) {
        st->capacity *= 2;
        st->entries = (SymbolEntry **)myRealloc(
            st->entries, sizeof(SymbolEntry *) * st->capacity);
    }
}

static bool addSymbol(SymbolManager *this, const char *name, SymbolKind kind,
                      const PType *type, const void *attributes) {
    SymbolTable *st = this->current_table;

    needEnlargeSymbolEntry(st);

    return st->addSymbol(st, name, kind, this->current_level - 1u, type,
                         attributes);
}

static SymbolEntry *lookup(SymbolManager *this, const char *name) {
    HashBucket *it = _HashTable->find(_HashTable, name);
    if (it == NULL) {
        return NULL;
    }
    return it->value;
}

static int compare(const void *a, const void *b) { return strcmp(a, b); }

// Use djb2 hash algorithm
static size_t hash(const void *key) {
    const char *string = (const char *)key;
    size_t n = 5381;
    for (size_t i = 0; string[i]; ++i) {
        n = (n << 5) + n + string[i];
    }
    return n;
}

SymbolManager *newSymbolManager(void) {
    SymbolManager *sm = (SymbolManager *)myMalloc(sizeof(SymbolManager));

    sm->root = NULL;
    sm->current_table = NULL;
    sm->indirect_next_table = &sm->root;
    sm->current_level = 0u;
    sm->pushScope = pushScope;
    sm->popScope = popScope;
    sm->nextScope = nextScope;
    sm->prevScope = prevScope;
    sm->addSymbol = addSymbol;
    sm->lookup = lookup;

    _HashTable = newHashTable(compare, hash);

    return sm;
}

void freeSymbolManager(SymbolManager *sm) {
    if (sm) {
        freeSymbolTable(sm->root);
        freeHashTable(_HashTable);
        free(sm);
    }
}
