#include "core/hash.h"
#include "core/utils.h"

#include <assert.h>
#include <stdlib.h>

#define BASE_BUCKETS_SIZE 8
#define MAX_BUCKETS_SIZE 65536

// Fast way to calculate number mod 2^n
#define INDEX_HASH(hash, table_size) ((hash) & ((table_size)-1))
#define SET_HASH_AND_INDEX(hash_table, key)                                    \
    size_t hash = hash_table->hashFunction(key);                               \
    size_t index = INDEX_HASH(hash, hash_table->capacity)

/************************
 * Function Definition
 ************************/
static HashBucket *find(HashTable *this, const void *key) {
    SET_HASH_AND_INDEX(this, key);
    HashBucket *it = this->buckets[index];

    while (it != NULL) {
        if (this->compare(it->key, key) == 0) {
            return it;
        }
        it = it->next;
    }
    return NULL;
}

static void doubleHashTable(HashTable *ht, size_t new_size) {
    HashBucket **new_buckets =
        (HashBucket **)myCalloc(new_size, sizeof(HashBucket *));
    for (size_t i = 0; i < ht->capacity; ++i) {
        HashBucket *current_bucket = ht->buckets[i];
        HashBucket *next_bucket = NULL;
        while (current_bucket != NULL) {
            size_t index = INDEX_HASH(current_bucket->hash, new_size);

            next_bucket = current_bucket->next;

            // concatenate the bucket of the same index
            current_bucket->next = new_buckets[index];
            new_buckets[index] = current_bucket;

            current_bucket = next_bucket;
        }
    }
    free(ht->buckets);

    ht->buckets = new_buckets;
    ht->capacity = new_size;
}

static void insert(HashTable *this, const void *key, void *value,
                   HashBucket *position) {
    if (position) {
        position->key = key;
        position->value = value;
        return;
    }

    SET_HASH_AND_INDEX(this, key);

    ++this->size;
    if (this->size > this->capacity && this->capacity < MAX_BUCKETS_SIZE) {
        doubleHashTable(this, this->capacity * 2);
        index = INDEX_HASH(hash, this->capacity);
    }
    HashBucket *new_bucket = (HashBucket *)myMalloc(sizeof(HashBucket));
    new_bucket->key = key;
    new_bucket->value = value;
    new_bucket->hash = hash;
    new_bucket->next = this->buckets[index];
    this->buckets[index] = new_bucket;
}

static void delete (HashTable *this, const void *key) {
    size_t index = INDEX_HASH(this->hashFunction(key), this->capacity);
    HashBucket *it = this->buckets[index];
    HashBucket **indirect = &this->buckets[index];

    while (it != NULL) {
        if (this->compare(it->key, key) == 0) {
            *indirect = it->next;
            free(it);
            --this->size;
            break;
        }
        indirect = &it->next;
        it = it->next;
    }
}

HashTable *newHashTable(int (*compare)(const void *, const void *),
                        size_t (*hashFunction)(const void *)) {
    assert(compare != NULL);
    assert(hashFunction != NULL);

    HashTable *ht = (HashTable *)myMalloc(sizeof(HashTable));

    ht->buckets =
        (HashBucket **)myCalloc(BASE_BUCKETS_SIZE, sizeof(HashBucket *));
    ht->size = 0;
    ht->capacity = BASE_BUCKETS_SIZE;
    ht->compare = compare;
    ht->hashFunction = hashFunction;
    ht->find = find;
    ht->insert = insert;
    ht->delete = delete;

    return ht;
}

void freeHashTable(HashTable *ht) {
    // TODO: clear buckets
    free(ht->buckets);
    free(ht);
}
