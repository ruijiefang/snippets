/*
 * =====================================================================================
 *       Filename:  symbtable.h
 *    Description:  Symbol table API
 * =====================================================================================
 */

#ifndef SYMBTABLE_H
#define SYMBTABLE_H
typedef struct table Table;
Table * table_create();
void * table_find(Table * t, char * key);
void table_insert(Table * t, char * key, void * data);
void * table_delete(Table * t, char * key);
int table_exists(Table *t, char * key);
void table_destroy(Table * t);
size_t table_size(Table * t);
#endif
