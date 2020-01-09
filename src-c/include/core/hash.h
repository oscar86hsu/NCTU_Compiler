#ifndef __HASH_H
#define __HASH_H

#include <stddef.h>

typedef struct _HashBucket {
    const void *key;
    void *value;
    size_t hash;
    struct _HashBucket *next;
} HashBucket;

typedef struct _HashTable {
    HashBucket **buckets;
    size_t size;
    size_t capacity;

    // Return a - b
    int (*compare)(const void *a, const void *b);
    size_t (*hashFunction)(const void *key);

    // Return the bucket if the key exists, NULL if not
    HashBucket *(*find)(struct _HashTable *this, const void *key);
    void (*insert)(struct _HashTable *this, const void *key, void *value,
                   HashBucket *position);
    void (*delete)(struct _HashTable *this, const void *key);
} HashTable;

HashTable *newHashTable(int (*compare)(const void *, const void *),
                        size_t (*hashFunction)(const void *));
void freeHashTable(HashTable *ht);

#endif
