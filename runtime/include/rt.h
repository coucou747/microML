typedef struct MLV MLV;

typedef MLV (*ml_fun)(MLV arg);

extern MLV True;
extern MLV False;

struct MLV {
  int value;
  ml_fun funptr;
  int size;
  struct MLV *ptr;
};

struct MLV clot_call(struct MLV a, int n, ...);
struct MLV clot_make(void* funptr, int arr, int n, ...);

struct MLV construct(int f, struct MLV a);
struct MLV destruct(int f, struct MLV a);
int is_constructed(int f, struct MLV a);

struct MLV tuple_nth(int i, struct MLV a);
struct MLV make_tuple(int i, ...);

struct MLV make_bool(int i);
struct MLV make_int(int i);

struct MLV int_neg(struct MLV a);
struct MLV int_add(struct MLV a, struct MLV b);
struct MLV int_sub(struct MLV a, struct MLV b);
struct MLV int_mul(struct MLV a, struct MLV b);
struct MLV int_div(struct MLV a, struct MLV b);
struct MLV int_lt(struct MLV a, struct MLV b);
struct MLV int_le(struct MLV a, struct MLV b);
struct MLV int_gt(struct MLV a, struct MLV b);
struct MLV int_ge(struct MLV a, struct MLV b);


struct MLV bool_or(struct MLV a, struct MLV b);
struct MLV bool_and(struct MLV a, struct MLV b);
struct MLV bool_not(struct MLV a);

void runtime_init();
extern MLV prim_print_int_clot;

struct MLV mlv_eq(struct MLV a, struct MLV b);
struct MLV mlv_neq(struct MLV a, struct MLV b);
int to_bool(struct MLV a);
