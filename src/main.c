#include "list.h"

// list element "allocator"

struct list *get_new_data(void)
{
  static struct list list_elems[30];
  static unsigned int elem_rest = 30;
  if (elem_rest == 0)
    return NULL;
  elem_rest = elem_rest - 1;
  return &list_elems[elem_rest];
}


int main(void)
{
  static struct list *main_list;
  list_empty(&main_list);

  {
    struct list *d = get_new_data();
    d->data = (void *)3;
    list_insert_front(&main_list, d);
  }

  return 0;
}
