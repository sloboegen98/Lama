/* Lama SM Bytecode interpreter */

# include <string.h>
# include <stdio.h>
# include <errno.h>
# include <malloc.h>
# include "../runtime/runtime.h"

// # define DEBUG 1

/* SM instructions */

enum Operation
{
    OpAdd = 0,
    OpSub = 1,
    OpMul = 2,
    OpDiv = 3,
    OpMod = 4,
    OpLt = 5,
    OpLeq = 6,
    OpGt = 7,
    OpGeq = 8,
    OpEq = 9,
    OpNeq = 10,
    OpAnd = 11,
    OpOr = 12
};

enum Cls1 {
    CONST = 0,
    STR = 1,
    SEXP = 2,
    STI = 3,
    STA = 4,
    JMP = 5,
    END = 6,
    RET = 7,
    DROP = 8,
    DUP = 9,
    SWAP = 10,
    ELEM = 11
};

enum LDS {
    LD = 2,
    LDA = 3,
    ST = 4
};

enum LocType {
    Global = 0,
    Local = 1,
    Arg = 2,
    Access = 3
};

enum Cls2 {
    CJMPz = 0,
    CJMPnz = 1,
    BEGIN = 2,
    CBEGIN = 3,
    CLOSURE = 4,
    CALLC = 5,
    CALL = 6,
    TAG = 7,
    ARRAY = 8
};

enum Patt {
    PATT_STR = 0,
    PATT_STR_TAG = 1,
    PATT_ARRAY = 2,
    PATT_SEXP = 3,
    PATT_BOX = 4,
    PATT_UNBOX = 5,
    PATT_FUN = 6
};

enum Builtin {
    LREAD = 0,
    LWRITE = 1,
    LLENGTH = 2,
    LSTRING = 3,
    BARRAY = 4
};

# define STRING_TAG  0x00000001
# define ARRAY_TAG   0x00000003
# define SEXP_TAG    0x00000005
# define CLOSURE_TAG 0x00000007

# define TO_DATA(x) ((data*)((char*)(x)-sizeof(int)))
# define LEN(x) ((x & 0xFFFFFFF8) >> 3)

# define UNBOXED(x)  (((int) (x)) &  0x0001)
# define UNBOX(x)    (((int) (x)) >> 1)
# define BOX(x)      ((((int) (x)) << 1) | 0x0001)

void* __start_custom_data;
void* __stop_custom_data;


typedef struct {
    int tag;
    char contents[0];
} data;

typedef struct {
    int tag;
    data contents;
} sexp;

void* BcreateArray(int bn, int* args) {
    int     i;
    data* r;
    int     n = UNBOX(bn);

    __pre_gc();

    // args + tag
    r = (data*)malloc(sizeof(int) * (n + 1));

    r->tag = ARRAY_TAG | (n << 3);

    for (i = 0; i < n; i++) {
        ((int*)r->contents)[i] = args[i];
    }

    __post_gc();

    return r->contents;
}

// args[0 : n - 1] --- sexp argumetns
// args[n]         --- tag
void* BcreateSexp(int bn, int* args) {
    int     i;
    int     ai;
    size_t* p;
    sexp* r;
    data* d;
    int n = UNBOX(bn);

    __pre_gc();

    // args + tag + hash
    r = (sexp*)malloc(sizeof(int) * (n + 2));
    d = &(r->contents);
    r->tag = 0;

    d->tag = SEXP_TAG | (n << 3);

    for (i = 0; i < n; i++) {
        ai = args[i];
        p = (size_t*)ai;
        ((int*)d->contents)[i] = ai;
    }

    r->tag = UNBOX(args[n]);

    __post_gc();

    return d->contents;
}

void* BcreateClosure(int bn, void* entry, int* args) {
    int     i, ai;
    data* r;
    int     n = UNBOX(bn);

    __pre_gc();

    r = (data*)malloc(sizeof(int) * (n + 2));

    r->tag = CLOSURE_TAG | ((n + 1) << 3);
    ((void**)r->contents)[0] = entry;

    // TAG | ENTRY + ARGS

    for (i = 0; i < n; i++) {
        ai = args[i];
        ((int*)r->contents)[i + 1] = ai;
    }

    __post_gc();

    return r->contents;
}


/* The unpacked representation of bytecode file */
typedef struct {
    char* string_ptr;              /* A pointer to the beginning of the string table */
    int* public_ptr;              /* A pointer to the beginning of publics table    */
    char* code_ptr;                /* A pointer to the bytecode itself               */
    int* global_ptr;              /* A pointer to the global area                   */
    int   stringtab_size;          /* The size (in bytes) of the string table        */
    int   global_area_size;        /* The size (in words) of global area             */
    int   public_symbols_number;   /* The number of public symbols                   */
    char  buffer[0];
} bytefile;

typedef struct State {
    int* args;
    int* locals;
    int* access;
} State_t;

typedef struct Function {
    char* ip;
    State_t* state;
    struct Function* callerFunction;
} Function_t;

void freeFunction(Function_t* f) {
    free(f->state->args);
    free(f->state->locals);
    free(f->state);
    free(f);
}

/* Gets a string from a string table by an index */
char* get_string(bytefile* f, int pos) {
    return &f->string_ptr[pos];
}

/* Gets a name for a public symbol */
char* get_public_name(bytefile* f, int i) {
    return get_string(f, f->public_ptr[i * 2]);
}

/* Gets an offset for a publie symbol */
int get_public_offset(bytefile* f, int i) {
    return f->public_ptr[i * 2 + 1];
}

int* lookup(bytefile* f, State_t* state, int l, int i) {
    switch (l) {
    case Global: {
#ifdef DEBUG
        printf("G(%d)", i);
#endif
        return &f->global_ptr[i];
    }
    case Local: {
#ifdef DEBUG
        printf("L(%d)", i);
#endif
        return &state->locals[i];
    }

    case Arg: {
#ifdef DEBUG
        printf("A(%d)", i);
#endif
        return &state->args[i];
    }

    case Access: {
#ifdef DEBUG
        printf("C(%d)", i);
#endif
        return &state->access[i];
    }

    default:
        printf("ERROR lookup: unsupported type\n");
        break;
    }
}

void assign(bytefile* f, State_t* state, int l, int i, int x) {
    switch (l)
    {
    case Global: {
#ifdef DEBUG
        printf("G(%d)", i);
#endif
        f->global_ptr[i] = x;
        break;
    }

    case Local: {
#ifdef DEBUG
        printf("L(%d)", i);
#endif
        state->locals[i] = x;
        break;
    }

    case Arg: {
#ifdef DEBUG
        printf("A(%d)", i);
#endif
        state->args[i] = x;
        break;
    }

    case Access: {
#ifdef DEBUG
        printf("C(%d)", i);
#endif  
        state->access[i] = x;
        break;
    }

    default:
        printf("ERROR assgn: usupported type\n");
        break;
    }
}

/* Reads a binary bytecode file by name and unpacks it */
bytefile* read_file(char* fname) {
    FILE* f = fopen(fname, "rb");
    long size;
    bytefile* file;

    if (f == 0) {
        failure("%s\n", strerror(errno));
    }

    if (fseek(f, 0, SEEK_END) == -1) {
        failure("%s\n", strerror(errno));
    }

    file = (bytefile*)malloc(sizeof(int) * 4 + (size = ftell(f)));

    if (file == 0) {
        failure("*** FAILURE: unable to allocate memory.\n");
    }

    rewind(f);

    if (size != fread(&file->stringtab_size, 1, size, f)) {
        failure("%s\n", strerror(errno));
    }

    fclose(f);

    file->string_ptr = &file->buffer[file->public_symbols_number * 2 * sizeof(int)];
    file->public_ptr = (int*)file->buffer;
    file->code_ptr = &file->string_ptr[file->stringtab_size];
    file->global_ptr = (int*)malloc(file->global_area_size * sizeof(int));

    return file;
}

# define  STACK_CAPACITY 10000
int buffer[STACK_CAPACITY];
int top = -1;

extern size_t __gc_stack_top;
extern size_t __gc_stack_bottom;

int stack_isEmpty() {
    return top == -1;
}

void stack_push(int v) {
    buffer[++top] = v;
    __gc_stack_top = buffer[top];
}

int stack_pop() {
    if (stack_isEmpty()) {

# ifdef DEBUG
        printf(" ERROR: stack is empty");
# endif
        return INT_MIN;
    }

    __gc_stack_top = buffer[top - 1];
    return buffer[top--];
}

int stack_top() {
    if (stack_isEmpty()) {
#ifdef DEBUG
        printf(" ERROR: stack is empty");
#endif
        return INT_MIN;
    }
    return buffer[top];
}

void eval(FILE* f, bytefile* bf) {

# define INT    (ip += sizeof (int), *(int*)(ip - sizeof (int)))
# define BYTE   *ip++
# define STRING get_string (bf, INT)
# define FAIL   failure (" ERROR: invalid opcode %d-%d\n", h, l)

    __gc_init();
    __gc_stack_bottom = &buffer[top];
    // main-function
    Function_t* curFunction = (Function_t*)malloc(sizeof(Function_t));
    curFunction->callerFunction = NULL;
    int lastCall = CALL;

    // stack_create();

    char* ip = bf->code_ptr;
    char* ops[] = { "+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!" };
    char* pats[] = { "=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun" };
    char* lds[] = { "LD", "LDA", "ST" };
    do {
        char x = BYTE,
            h = (x & 0xF0) >> 4,
            l = x & 0x0F;


#ifdef DEBUG
        fprintf(f, "0x%.8x:\t", ip - bf->code_ptr - 1);
#endif

        switch (h) {
        case 15:
            goto stop;

        case 0: {
#ifdef DEBUG
            fprintf(f, "BINOP\t%s", ops[l - 1]);
#endif

            int op = l - 1;
            int rhs = UNBOX(stack_pop());
            int lhs = UNBOX(stack_pop());

            switch (op) {
            case OpAdd: {
                int result = BOX(lhs + rhs);
                stack_push(result);
                break;
            }

            case OpSub: {
                int result = BOX(lhs - rhs);
                stack_push(result);
                break;
            }

            case OpMul: {
                int result = BOX(lhs * rhs);
                stack_push(result);
                break;
            }

            case OpDiv: {
                int result = BOX(lhs / rhs);
                stack_push(result);
                break;
            }

            case OpMod: {
                int result = BOX(lhs % rhs);
                stack_push(result);
                break;
            }

            case OpLt: {
                int result = BOX(lhs < rhs ? 1 : 0);
                stack_push(result);
                break;
            }

            case OpLeq: {
                int result = BOX(lhs <= rhs ? 1 : 0);
                stack_push(result);
                break;
            }

            case OpGt: {
                int result = BOX(lhs > rhs ? 1 : 0);
                stack_push(result);
                break;
            }

            case OpGeq: {
                int result = BOX(lhs >= rhs ? 1 : 0);
                stack_push(result);
                break;
            }

            case OpEq: {
                int result = BOX(lhs == rhs ? 1 : 0);
                stack_push(result);
                break;
            }

            case OpNeq: {
                int result = BOX(lhs != rhs ? 1 : 0);
                stack_push(result);
                break;
            }

            case OpAnd: {
                int result = BOX(lhs && rhs);
                stack_push(result);
                break;
            }

            case OpOr: {
                int result = BOX(lhs || rhs);
                stack_push(result);
                break;
            }

            default: {
                FAIL;
            }
            }
            break;
        }

        case 1: {
            switch (l) {
            case  CONST: {
                int value = INT;
#ifdef DEBUG
                fprintf(f, "CONST\t%d", value);
#endif
                stack_push(BOX(value));
                break;
            }

            case STR: {
                char* str = STRING;
#ifdef DEBUG
                fprintf(f, "STRING\t%s", str);
#endif
                int v = Bstring(str);
                stack_push(v);

                break;
            }

            case SEXP: {
                char* name = STRING;
                int nargs = INT;
#ifdef DEBUG
                fprintf(f, "SEXP\t%s", name);
                fprintf(f, " %d", nargs);
#endif
                int hash = LtagHash(name);
                int* args = (int*)malloc((nargs + 1) * sizeof(int)); // args + hash
                for (int i = nargs - 1; i >= 0; i--) {
                    args[i] = stack_pop();
                }
                args[nargs] = hash;
                int sexp = BcreateSexp(BOX(nargs), args);
                stack_push(sexp);
                free(args);

                break;
            }

            case STA: {
#ifdef DEBUG
                fprintf(f, "STA");
#endif
                int v = stack_pop();
                int index = stack_pop();
                int x = stack_pop();
                int vv = Bsta(v, index, x);
                stack_push(vv);

                break;
            }

            case JMP: {
                int label = INT;
#ifdef DEBUG
                fprintf(f, "JMP\t0x%.8x", label);
#endif
                ip = (char*)(bf->code_ptr + label);
                break;
            }

            case  END: {
#ifdef DEBUG
                fprintf(f, "END\t");
#endif

                if (curFunction->callerFunction == NULL) {
                    return;
                }

                Function_t* previous = curFunction;
                curFunction = curFunction->callerFunction;
                ip = curFunction->ip;
                freeFunction(previous);

                break;
            }
            case DROP: {
#ifdef DEBUG
                fprintf(f, "DROP");
#endif
                stack_pop();
                break;
            }

            case DUP: {
#ifdef DEBUG
                fprintf(f, "DUP");
#endif
                int dup = stack_top();
                stack_push(dup);
                break;
            }

            case ELEM: {
#ifdef DEBUG
                fprintf(f, "ELEM");
#endif
                int index = stack_pop();
                int s = stack_pop();
                int elem = Belem(s, index);
                stack_push(elem);
                break;
            }

            default:
                FAIL;
            }
            break;
        }

        case LD: {
#ifdef DEBUG
            fprintf(f, "%s\t", "LD");
#endif
            int index = INT;
            int value = *lookup(bf, curFunction->state, l, index);
#ifdef DEBUG
            fprintf(f, " DEBUG: value is %d", UNBOX(value));
#endif
            stack_push(value);
            break;
        }

        case LDA: {
#ifdef DEBUG
            fprintf(f, "%s\t", "LDA");
#endif
            int index = INT;
            int value = lookup(bf, curFunction->state, l, index);
#ifdef DEBUG
            fprintf(f, " DEBUG: value is %d", UNBOX(value));
#endif
            stack_push(value);
            stack_push(value);
            break;
        }

        case ST: {
#ifdef DEBUG
            fprintf(f, "%s\t", "ST");
#endif
            int index = INT;
            int value = stack_top();
            assign(bf, curFunction->state, l, index, value);
            break;
        }

        case 5: {
            switch (l) {
            case CJMPz: {
                unsigned int label = INT;

#ifdef DEBUG
                fprintf(f, "CJMPz\t0x%.8x", label);
#endif

                int z = UNBOX(stack_pop());
                if (z == 0) {
                    ip = (char*)(bf->code_ptr + label);
                }
                break;
            }

            case CJMPnz: {
                unsigned int label = INT;
#ifdef DEBUG
                fprintf(f, "CJMPnz\t0x%.8x", label);
#endif
                int z = UNBOX(stack_pop());
                if (z != 0) {
                    ip = (char*)(bf->code_ptr + label);
                }
                break;
            }

            case  BEGIN: {
                int nargs = INT;
                int nlocals = INT;
#ifdef DEBUG
                fprintf(f, "BEGIN\t%d ", nargs);
                fprintf(f, "%d", nlocals);
#endif

                if (lastCall != CALLC) {
                    curFunction->state = (State_t*)malloc(sizeof(State_t));
                    curFunction->state->access = NULL;
                    curFunction->state->args = (int*)malloc(nargs * sizeof(int));
                    // not a `main`-function
                    if (curFunction->callerFunction != NULL) {
                        for (int i = nargs - 1; i >= 0; i--) {
                            curFunction->state->args[i] = stack_pop();
                        }
                    }
                }

                curFunction->state->locals = (int*)malloc(nlocals * sizeof(int));

                break;
            }

            case CBEGIN: {
                int nargs = INT;
                int nlocals = INT;
#ifdef DEBUG
                fprintf(f, "CBEGIN\t%d %d", nargs, nlocals);
#endif
                curFunction->state->locals = (int*)malloc(nlocals * sizeof(int));
                break;
            }

            case CLOSURE: {
                int address = INT;
                int nargs = INT;
#ifdef DEBUG
                fprintf(f, "CLOSURE\t0x%.8x | %d ", address, nargs);
#endif
                int* args = (int*)malloc(nargs * sizeof(int));
                for (int i = 0; i < nargs; i++) {
                    int t = BYTE;
                    int index = INT;
                    args[i] = *lookup(bf, curFunction->state, t, index);
                }

                stack_push(BcreateClosure(BOX(nargs), (void*)address, args));
                free(args);
                break;
            }

            case CALLC: {
                int nargs = INT;
#ifdef DEBUG
                fprintf(f, "CALLC %d", nargs);
#endif

                int* args = (int*)malloc(nargs * sizeof(int));
                for (int i = nargs - 1; i >= 0; i--) {
                    args[i] = stack_pop();
                }

                data* closure = TO_DATA(stack_pop());
                int label = *(int*)closure->contents;

                Function_t* newFunction = (Function_t*)malloc(sizeof(Function_t));
                newFunction->callerFunction = curFunction;
                newFunction->state = (State_t*)malloc(sizeof(State_t));
                newFunction->state->access = (int*)(closure->contents + sizeof(int));
                newFunction->state->args = (int*)malloc(nargs * sizeof(int));

                for (int i = 0; i < nargs; i++) {
                    newFunction->state->args[i] = args[i];
                }

                free(args);

                curFunction->ip = ip;
                curFunction = newFunction;
                ip = (char*)(bf->code_ptr + label);
                lastCall = CALLC;

                break;
            }

            case CALL: {
                int funLabel = INT;
                int nargs = INT;
#ifdef DEBUG
                fprintf(f, "CALL\t0x%.8x ", funLabel);
                fprintf(f, "%d", nargs);
#endif
                curFunction->ip = ip;

                Function_t* newFunction = (Function_t*)malloc(sizeof(Function_t));
                newFunction->callerFunction = curFunction;
                curFunction = newFunction;
                ip = (char*)(bf->code_ptr + funLabel);
                lastCall = CALL;

                break;
            }

            case TAG: {
                char* name = STRING;
                int nargs = INT;
#ifdef DEBUG
                fprintf(f, "TAG\t%s ", name);
                fprintf(f, "%d", nargs);
#endif
                int hash = LtagHash(name);
                int patt = stack_pop();
                int matched = Btag(patt, hash, BOX(nargs));
                stack_push(matched);
                break;
            }

            case ARRAY: {
                int n = INT;
#ifdef DEBUG
                fprintf(f, "ARRAY\t%d", n);
#endif
                int patt = stack_pop();
                int matched = Barray_patt(patt, BOX(n));
                stack_push(matched);
                break;
            }

            case 10: {
                int line = INT;
#ifdef DEBUG
                fprintf(f, "DEBUG: LINE\t%d", line);
#endif
                break;
            }
            default:
                FAIL;
            }
            break;
        }

        case 6: {
#ifdef DEBUG
            fprintf(f, "PATT\t%s", pats[l]);
#endif

            switch (l) {
            case PATT_STR: {
                void* x = (void*)stack_pop();
                void* y = (void*)stack_pop();
                stack_push(Bstring_patt(x, y));
                break;
            }

            case PATT_STR_TAG: {
                void* x = (void*)stack_pop();
                stack_push(Bstring_tag_patt(x));
                break;
            }

            case PATT_ARRAY: {
                void* x = (void*)stack_pop();
                stack_push(Barray_tag_patt(x));
                break;
            }

            case PATT_SEXP: {
                void* x = (void*)stack_pop();
                stack_push(Bsexp_tag_patt(x));
                break;
            }

            case PATT_BOX: {
                void* x = (void*)stack_pop();
                stack_push(Bboxed_patt(x));
                break;
            }

            case PATT_UNBOX: {
                void* x = (void*)stack_pop();
                stack_push(Bunboxed_patt(x));
                break;
            }

            case PATT_FUN: {
                void* x = (void*)stack_pop();
                stack_push(Bclosure_tag_patt(x));
                break;
            }
            }

            break;
        }

        case 7: {
            switch (l) {
            case LREAD: {
#ifdef DEBUG
                fprintf(f, "CALL\tLread");
#endif
                int value = Lread();
                stack_push(value);
                break;
            }

            case LWRITE: {
#ifdef DEBUG
                fprintf(f, "CALL\tLwrite\n");
#endif
                int value = stack_pop();
                stack_push(Lwrite(value));
                break;
            }

            case LLENGTH: {
#ifdef DEBUG
                fprintf(f, "CALL\tLlength");
#endif          
                int s = stack_pop();
                int len = Llength(s);
                stack_push(len);
                break;
            }
            case LSTRING: {
#ifdef DEBUG
                fprintf(f, "CALL\tLstring");
#endif 
                int obj = stack_pop();
                int str = Lstring(obj);
                stack_push(str);
                break;
            }

            case BARRAY: {
                int n = INT;
#ifdef DEBUG
                fprintf(f, "CALL\tBarray\t%d", n);
#endif
                int* args = (int*)malloc(n * sizeof(int));
                for (int i = n - 1; i >= 0; i--) {
                    args[i] = stack_pop();
                }
                int arr = BcreateArray(BOX(n), args);
                stack_push(arr);
                free(args);
                break;
            }

            default:
                FAIL;
            }
            break;
        }
        default:
            FAIL;
        }

#ifdef DEBUG
        fprintf(f, "\n");
#endif
    } while (1);
stop:
#ifdef DEBUG
    free(curFunction);
    fprintf(f, "<end>\n");
#endif
    return;
}

/* Dumps the contents of the file */
void dump_file(FILE* f, bytefile* bf) {

#ifdef DEBUG
    int i;
    fprintf(f, "String table size       : %d\n", bf->stringtab_size);
    fprintf(f, "Global area size        : %d\n", bf->global_area_size);
    fprintf(f, "Number of public symbols: %d\n", bf->public_symbols_number);
    fprintf(f, "Public symbols          :\n");

    for (i = 0; i < bf->public_symbols_number; i++)
        fprintf(f, "   0x%.8x: %s\n", get_public_offset(bf, i), get_public_name(bf, i));

    fprintf(f, "Code:\n");
#endif

    eval(f, bf);
}

int main(int argc, char* argv[]) {
    bytefile* f = read_file(argv[1]);
    dump_file(stdout, f);
    free(f);
    return 0;
}
