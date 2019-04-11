#ifndef LIST_H
#define LIST_H

typedef void *data_ptr;

struct list
{
  struct list *next;
  data_ptr data;
};

typedef struct list *list_t;

void list_empty(list_t *l);

void list_insert_front(list_t *l, struct list *new);

void list_singleton(list_t *l, struct list *new);

void list_insert_after(struct list *node, struct list *new);

struct list *list_find_last_node(list_t *l);

void list_insert_back(list_t *l, struct list *new);

#endif
