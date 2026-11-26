#include "include/rt.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <stdarg.h>

#define STEP_SIZE 1024 * 1024
#define INIT_SIZE STEP_SIZE * 128

struct MLV *memory = NULL;
struct MLV *memory_ptr = NULL;
struct MLV *end_memory = NULL;

struct MLV False = {0, NULL, 0, NULL};
struct MLV True = {1, NULL, 0, NULL};

struct MLV *alloc(int i){
  if (memory == NULL){
    memory = malloc(INIT_SIZE * sizeof(struct MLV));
    memory_ptr = memory;
    end_memory = memory + INIT_SIZE;
  }
  if (end_memory < memory_ptr + i){
    // TODO réalloc
    printf("Pas assez de mémoire.");
    exit(1);
  }
  struct MLV *out = memory_ptr;
  memory_ptr += i;
  return out;
}

struct MLV copy(struct MLV a){
  struct MLV b;
  b.value = a.value;
  b.funptr = a.funptr;
  b.size = a.size;
  b.ptr = alloc(a.size);
  for (int i = 0; i < a.size; i ++){
    b.ptr[i] = a.ptr[i];
  }
  return b;
}

struct MLV clot_call(struct MLV a, int n, ...) {
  va_list ap;
  va_start(ap, n);
  struct MLV cpy = copy(a);
  for (int i = 0; i < n; i++) {
    assert(cpy.value < cpy.size);
    cpy.ptr[cpy.value ++] = va_arg(ap, MLV);
    if (cpy.value == cpy.size){
      cpy = cpy.funptr(cpy);
    }
  }
  va_end(ap);
  return cpy;
}


struct MLV clot_make(void* funptr, int arr, int n, ...) {
  va_list ap;
  va_start(ap, n);
  if (n > arr) {
    assert(0);
  }
  struct MLV out;
  out.funptr = funptr;
  out.size = arr;
  out.ptr = alloc(arr);
  out.value = n;
  for (int i = 0; i < n; i++) {
    out.ptr[i] = va_arg(ap, MLV);
  }
  va_end(ap);
  return out;
}

struct MLV construct(int field, struct MLV v){
  struct MLV out;
  out.ptr = alloc(1);
  out.value = field;
  out.size = 1;
  out.ptr[0] = v;
  out.funptr = NULL;
  return out;
}

struct MLV destruct(int field, struct MLV a){
  assert(a.size == 1);
  return a.ptr[0];
}
int is_constructed(int f, struct MLV a){
  assert(a.size == 1);
  return a.value == f;
}

struct MLV record(int nfields){ // TODO ...
  struct MLV out;
  out.funptr = NULL;
  out.ptr = alloc(nfields * 2);
  out.size = nfields;
  return out;
}
void record_fill(struct MLV record, int indice, int field, struct MLV v){
  record.ptr[indice * 2].value = field;
  record.ptr[indice * 2].ptr = NULL;
  record.ptr[indice * 2 + 1] = v;
}
struct MLV record_get(struct MLV record, int field){
  for (int i = 0; i < record.size; i ++){
    if (field == record.ptr[i * 2].value)
      return record.ptr[i * 2 + 1];
  }
  assert(0);
}

struct MLV tuple_nth(int i, struct MLV a){
  return a.ptr[i];
}
struct MLV make_tuple(int n, ...){
  va_list ap;
  va_start(ap, n);
  struct MLV out;
  out.funptr = NULL;
  out.ptr = alloc(n);
  out.value = 0;
  out.size = n;
  for (int i = 0; i < n; i++) {
    out.ptr[i] = va_arg(ap, MLV);
  }
  va_end(ap);
  return out;
}

struct MLV make_int(int i){
  struct MLV out;
  out.value = i;
  out.size = 0;
  out.ptr = NULL;
  out.funptr = NULL;
  return out;
}

struct MLV make_bool(int i){
  return make_int(i);
}

struct MLV int_add(struct MLV a, struct MLV b){
  return make_int(a.value + b.value);
}

struct MLV int_sub(struct MLV a, struct MLV b){
  return make_int(a.value - b.value);
}
struct MLV int_neg(struct MLV a){
  return make_int(-a.value);
}

int to_bool(struct MLV a){
  return a.value;
}

struct MLV mlv_eq(struct MLV a, struct MLV b){
  if (a.value == b.value &&
    a.funptr == b.funptr && a.size == b.size){
    for (int i = 0; i < a.size; i ++){
      if (!to_bool(mlv_eq(a.ptr[i], b.ptr[i]))) return False;
    }
    return True;
  } else return False;
}

struct MLV int_mul(struct MLV a, struct MLV b){
  return make_int(a.value * b.value);
}

struct MLV int_div(struct MLV a, struct MLV b){
  return make_int(a.value / b.value);
}

struct MLV int_lt(struct MLV a, struct MLV b){
  return make_bool(a.value < b.value);
}

struct MLV int_le(struct MLV a, struct MLV b){
  return make_bool(a.value <= b.value);
}

struct MLV int_gt(struct MLV a, struct MLV b){
  return make_bool(a.value > b.value);
}

struct MLV int_ge(struct MLV a, struct MLV b){
  return make_bool(a.value >= b.value);
}

struct MLV mlv_neq(struct MLV a, struct MLV b){
  return make_bool(!to_bool(mlv_eq(a, b)));
}

MLV prim_print_int(MLV m){
  printf("%d", m.ptr[0].value);
  return m;
}

MLV prim_print_int_clot;
void runtime_init(){
  prim_print_int_clot = clot_make(prim_print_int, 1, 0);
}

struct MLV bool_or(struct MLV a, struct MLV b) {
  return make_bool(a.value || b.value);
}

struct MLV bool_and(struct MLV a, struct MLV b){
  return make_bool(a.value && b.value);
}

struct MLV bool_not(struct MLV a){
  return make_bool(!a.value);
}
