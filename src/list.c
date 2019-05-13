/*  Titre:      src/list.c
    Auteur:     Adrien Stalain

    Fait dans le cadre d'un stage à Orange Labs
*/

#include  "list.h"

#ifndef NULL
#define NULL ((void *)0)
#endif

void list_empty(list_t *l)
{
  *l = NULL;
}

#ifdef PROOVER
int global_variable;
void list_empty_alt1(list_t *l)
{
  *l = NULL;
  global_variable = (int)l;
}

void list_empty_alt2(list_t *l)
{
  for(unsigned int i = 0; i < 0xFFFFFFFF;i++)
    *l = NULL;
}

#endif

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

#ifdef PROOVER
void list_singleton_alt(list_t *l, struct list *new)
{
  *l = new;
}
#endif

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

struct list *list_pop(list_t *l)
{
  if (!*l)
    return NULL;
  struct list *first = *l;
  *l = first->next;
  return first;
}

unsigned int list_length(list_t *l)
{
  unsigned int count = 0;
  struct list *p = *l;
  while (p)
  {
    count++;
    p = p->next;
  }
  return count;
}


int list_is_empty(list_t *l)
{
  return (*l == NULL);
}
