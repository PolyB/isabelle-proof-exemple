#include  "list.h"

#ifndef NULL
#define NULL ((void *)0)
#endif


void list_empty(list_t *l)
{
  *l = NULL;
}

void list_insert_front(list_t *l, struct list *new)
{
  new->next = *l;
  *l = new;
} 

void list_singleton(list_t *l, struct list *new)
{
  *l = new;
  new->next = NULL;
}

void list_insert_after(struct list *node, struct list*new)
{
  new->next = node->next;
  node->next = new;
}

struct list *list_find_last_node(list_t *l)
{
  struct list *p = *l;
  if (!p)
    return NULL;
  while (p->next)
    p = p->next;
  return p;
}

void list_insert_back(list_t *l, struct list *new)
{
  if (!*l)
    list_singleton(l, new);
  else
  {
    struct list *last = list_find_last_node(l);
    list_insert_after(last, new);
  }
} 
