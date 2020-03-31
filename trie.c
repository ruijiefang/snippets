/*
 * ==============================================================
 *       Filename:  symbtable.c
 *    Description:  Trie-based symble table implementation.
 * ==============================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include "symbtable.h"
/* A node is a struct of keys, some of which have
   content, others are set to NULL. It also keeps track
   of the size of its subtree (excluding its own payload).
   its payload can be either NULL (in which case one of
   its descendents have a non-NULL payload) or non-NULL.
   The character it represents is stored in "node_char".
   It also contains a pointer to its parent. The node_char
   variable of root is set to (char)0 and the parent pointer
   of root is set to NULL. */
typedef struct node {
  struct node *keys[94];
  struct node * parent;
  size_t size;
  void *payload;
  int occupied;
  char node_char;
} Node;

/* A table contains only a single entry - the root.
   The size of the trie is kept track inside the root's
   size field. */
struct table {
  Node * root;
};

/* converts a char to internal keys array index. */
inline static size_t idx(char c)
{
  return c - 32;
}

/* Creates a node with parent pointer "parent" and
   representing character "c" */
static Node * node_create(Node * parent, char c)
{
  Node * n = malloc(sizeof(Node));
  memset(n, 0, sizeof(Node));
  n->parent = parent;
  n->node_char = c;
  return n;
}

/* Creates a new symbol table with empty contents. */
Table * table_create()
{
  Table * t = malloc(sizeof(Table));
  t->root = node_create(NULL, (char)0);
  return t;
}

/* Inserts a key-value pair (str, data) into trie. */
static void node_insert(Node * root, char * str,
    void * data)
{
  Node * ptr = root;
  size_t loc;

  /* Insert by looking thru each element of key "str"
     and stopping at the last character (before the
     NULL-terminator. */
  for(loc = 0; str[loc] != '\0'; ++loc) {
    /* If an entry is NULL, create it */
    if (ptr->keys[idx(str[loc])] == NULL) {
      ptr->keys[idx(str[loc])] = node_create(ptr, str[loc]);
    }
    /* Increment the size of the intermediary nodes */
    ++ptr->size;
    ptr = ptr->keys[idx(str[loc])];
  }
  ptr->occupied = 1;
  ptr->payload = data;
}

/* Retrieve value by querying a key. */
static void * node_find(Node * root, char * str)
{
  Node * ptr = root;
  size_t loc;
  /* Loop through each element of key and
     go down our trie. */
  for(loc = 0; str[loc] != '\0'; ++loc) {
    /* Oops... key might not be found. */
    if (ptr->keys[idx(str[loc])] == NULL) return NULL;
    /* Otherwise, continue down the trie. */
    ptr = ptr->keys[idx(str[loc])];
  }
  /* ptr is now at the position of our key. */
  return ptr->payload;
}

/* Does key exist in our system? */
static int node_exists(Node * root, char * str)
{
  Node * ptr = root;
  size_t loc;
  /* Loop through each element of key and
     go down our trie. */

  for(loc = 0; str[loc] != '\0'; ++loc) {
    if (ptr->keys[idx(str[loc])] == NULL) {
      return 0;
    }
    ptr = ptr->keys[idx(str[loc])];
  }
  /* Is it occupied? */
  return ptr->occupied;
}

/* Delete a node by key. */
static void * node_delete(Node * root, char * str)
{
  size_t iters = 0;
  Node * ptr = root, * ptr2;
  void * data = NULL;
  size_t loc;
  char node_char;
  /* Perform a lookup first. Otherwise the delete
     process also needs to maintain the size of
     subtrees at each intermediary node, and keys
     that are not found complicates this process. */
  if (!node_exists(root, str)) return NULL;
  /* We are now sure that the key is in the tree.
     Loop through each element of the key and go down
     the tree, maintaining the sizes of the subtrees
     at each node in the process */
  for(loc = 0; str[loc] != '\0'; ++loc) {
    --(ptr->size);
    ptr = ptr->keys[idx(str[loc])];
  }
  data = ptr->payload;
  /* Delete the payload. */
  ptr->payload = NULL;
  ptr->occupied = 0;
  /* Prune off branches of the trie that are not
     needed anymore after this deletion. */
  while (ptr != root) {
    ptr2 = ptr->parent;
    node_char = ptr->node_char;
    /* If a node doesn't have any subtrees and
       payload, it is not needed. */
    if (ptr->size == 0 && !ptr->occupied) {
      /* consolidate node */
      free(ptr);
      /* also clear of its entry in its parent's
         keys table. */
      if (ptr2 != NULL)
        ptr2->keys[idx(node_char)] = NULL;
    }
    /* To the parent. */
    ptr = ptr2;
    ++iters;
  }
  return data;
}

void * table_find(Table * t, char * key)
{
  return node_find(t->root, key);
}

void table_insert(Table * t, char * key, void * data)
{
  return node_insert(t->root, key, data);
}

void * table_delete(Table * t, char * key)
{
  return node_delete(t->root, key);
}

int table_exists(Table *t, char * key)
{
  return node_exists(t->root, key);
}

static void node_destroy(Node * node)
{
  size_t i;
  for (i = 0; i < 94; ++i) {
    if (node->keys[i] != NULL) node_destroy(node->keys[i]);
    free(node->keys[i]);
  }
}

void table_destroy(Table * t)
{
  node_destroy(t->root);
  free(t->root);
}

size_t table_size(Table * t)
{
  return t->root->size + (t->root->occupied);
}



