/* Lama SM Bytecode interpreter */

# include <string.h>
# include <stdio.h>
# include <errno.h>
# include <malloc.h>
# include "../runtime/runtime.h"

// # define DEBUG 1

/* SM instructions */

# define BINOP   0

# define CONST   0
# define STR     1
# define SEXP    2
# define STA     4
# define JMP     5
# define END     6
# define DROP    8
# define DUP     9
# define ELEM    11

# define LD      2
# define LDA     3
# define ST      4


# define Global  0
# define Local   1
# define Arg     2

# define CJMPz   0
# define CJMPnz  1
# define BEGIN   2
# define CALL    6
# define TAG     7
# define ARRAY   8

# define LINE    10

# define BUILTIN 7
# define LREAD   0
# define LWRITE  1
# define LLENGTH 2
# define LSTRING 3
# define BARRAY  4


# define STRING_TAG  0x00000001
# define ARRAY_TAG   0x00000003
# define SEXP_TAG    0x00000005

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

    // args + tag
    r = (data*)malloc(sizeof(int) * (n + 1));

    r->tag = ARRAY_TAG | (n << 3);

    for (i = 0; i < n; i++) {
        ((int*)r->contents)[i] = args[i];
    }

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

    return d->contents;
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

const int STACK_CAPACITY = 10000;
typedef struct {
    int top;
    int* buffer;
} Stack_t;


Stack_t* stack_create() {
    Stack_t* stack = (Stack_t*)(malloc(sizeof(Stack_t)));
    stack->top = -1;
    stack->buffer = (int*)malloc(STACK_CAPACITY * sizeof(int));
    return stack;
}

int stack_isEmpty(Stack_t* stack) {
    return stack->top == -1;
}

void stack_push(Stack_t* stack, int v) {
    stack->buffer[++stack->top] = v;
}

int stack_pop(Stack_t* stack) {
    if (stack_isEmpty(stack)) {

# ifdef DEBUG
        printf("ERROR: stack is empty");
# endif
        return INT_MIN;
    }
    return stack->buffer[stack->top--];
}

int stack_top(Stack_t* stack) {
    if (stack_isEmpty(stack)) {
#ifdef DEBUG
        printf("ERROR: stack is empty");
#endif
        return INT_MIN;
    }
    return stack->buffer[stack->top];
}

void eval(FILE* f, bytefile* bf) {

# define INT    (ip += sizeof (int), *(int*)(ip - sizeof (int)))
# define BYTE   *ip++
# define STRING get_string (bf, INT)
# define FAIL   failure ("ERROR: invalid opcode %d-%d\n", h, l)

    // main-function
    Function_t* curFunction = (Function_t*)malloc(sizeof(Function_t));
    curFunction->callerFunction = NULL;

    Stack_t* stack = stack_create();

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

        case BINOP: {
#ifdef DEBUG
            fprintf(f, "BINOP\t%s", ops[l - 1]);
#endif

            char* op = ops[l - 1];
            int rhs = UNBOX(stack_pop(stack));
            int lhs = UNBOX(stack_pop(stack));

            if (strcmp(op, "+") == 0) {
                int result = BOX(lhs + rhs);
                stack_push(stack, result);
            }
            else if (strcmp(op, "-") == 0) {
                int result = BOX(lhs - rhs);
                stack_push(stack, result);
            }
            else if (strcmp(op, "*") == 0) {
                int result = BOX(lhs * rhs);
                stack_push(stack, result);
            }
            else if (strcmp(op, "/") == 0) {
                int result = BOX(lhs / rhs);
                stack_push(stack, result);
            }
            else if (strcmp(op, "%") == 0) {
                int result = BOX(lhs % rhs);
                stack_push(stack, result);
            }
            else if (strcmp(op, "<") == 0) {
                int result = BOX(lhs < rhs ? 1 : 0);
                stack_push(stack, result);
            }
            else if (strcmp(op, "<=") == 0) {
                int result = BOX(lhs <= rhs ? 1 : 0);
                stack_push(stack, result);
            }
            else if (strcmp(op, ">") == 0) {
                int result = BOX(lhs > rhs ? 1 : 0);
                stack_push(stack, result);
            }
            else if (strcmp(op, ">=") == 0) {
                int result = BOX(lhs >= rhs ? 1 : 0);
                stack_push(stack, result);
            }
            else if (strcmp(op, "==") == 0) {
                int result = BOX(lhs == rhs ? 1 : 0);
                stack_push(stack, result);
            }
            else if (strcmp(op, "!=") == 0) {
                int result = BOX(lhs != rhs ? 1 : 0);
                stack_push(stack, result);
            }
            else if (strcmp(op, "&&") == 0) {
                int result = BOX(lhs && rhs);
                stack_push(stack, result);
            }
            else if (strcmp(op, "!!") == 0) {
                int result = BOX(lhs || rhs);
                stack_push(stack, result);
            }
            else {
                FAIL;
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
                stack_push(stack, BOX(value));
                break;
            }

            case STR: {
                char* str = STRING;
#ifdef DEBUG
                fprintf(f, "STRING\t%s", str);
#endif
                int v = Bstring(str);
                stack_push(stack, v);

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
                    args[i] = stack_pop(stack);
                }
                args[nargs] = hash;
                int sexp = BcreateSexp(BOX(nargs), args);
                stack_push(stack, sexp);

                break;
            }

            case STA: {
#ifdef DEBUG
                fprintf(f, "STA");
#endif
                int v = stack_pop(stack);
                int index = stack_pop(stack);
                int x = stack_pop(stack);

                int vv = Bsta(v, index, x);

                stack_push(stack, vv);

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
                stack_pop(stack);
                break;
            }

            case DUP: {
#ifdef DEBUG
                fprintf(f, "DUP");
#endif
                int dup = stack_top(stack);
                stack_push(stack, dup);
                break;
            }

            case ELEM: {
#ifdef DEBUG
                fprintf(f, "ELEM");
#endif
                int index = stack_pop(stack);
                int s = stack_pop(stack);

                int elem = Belem(s, index);
                stack_push(stack, elem);
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
            fprintf(f, " DEBUG: value is %d", value);
#endif
            stack_push(stack, value);
            break;
        }

        case LDA: {
            int index = INT;
            int value = lookup(bf, curFunction->state, l, index);
#ifdef DEBUG
            fprintf(f, " DEBUG: value is %d", value);
#endif
            stack_push(stack, value);
            stack_push(stack, value);
            break;
        }

        case ST: {
#ifdef DEBUG
            fprintf(f, "%s\t", "ST");
#endif
            int index = INT;
            int value = stack_top(stack);
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

                int z = UNBOX(stack_pop(stack));
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
                int z = UNBOX(stack_pop(stack));
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
                curFunction->state = (State_t*)malloc(sizeof(State_t));
                curFunction->state->args = (int*)malloc(nargs * sizeof(int));
                curFunction->state->locals = (int*)malloc(nlocals * sizeof(int));

                // not a `main`-function
                if (curFunction->callerFunction != NULL) {
                    for (int i = nargs - 1; i >= 0; i--) {
                        curFunction->state->args[i] = stack_pop(stack);
                    }
                }

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
                int patt = stack_pop(stack);
                int matched = Btag(patt, hash, BOX(nargs));
                stack_push(stack, matched);
                break;
            }

            case ARRAY: {
                int n = INT;
#ifdef DEBUG
                fprintf(f, "ARRAY\t%d", n);
#endif
                int patt = stack_pop(stack);
                int matched = Barray_patt(patt, BOX(n));
                stack_push(stack, matched);
                break;
            }

            case LINE: {
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

        case BUILTIN: {
            switch (l) {
            case LREAD: {
#ifdef DEBUG
                fprintf(f, "CALL\tLread");
#endif
                int value = Lread();
                stack_push(stack, value);
                break;
            }

            case LWRITE: {
#ifdef DEBUG
                fprintf(f, "CALL\tLwrite\n");
#endif
                int value = stack_pop(stack);
                Lwrite(value);
                break;
            }

            case LLENGTH: {
#ifdef DEBUG
                fprintf(f, "CALL\tLlength");
#endif          
                int s = stack_pop(stack);
                int len = Llength(s);
                stack_push(stack, len);
                break;
            }
            case LSTRING: {
#ifdef DEBUG
                fprintf(f, "CALL\tLstring");
#endif 
                FAIL;
                // TODO: check
                // int obj = stack_pop(stack);
                // int str = Lstring(obj);
                // stack_push(stack, str);
                break;
            }

            case BARRAY: {
                int n = INT;
#ifdef DEBUG
                fprintf(f, "CALL\tBarray\t%d", n);
#endif
                int* args = (int*)malloc(n * sizeof(int));
                for (int i = n - 1; i >= 0; i--) {
                    args[i] = stack_pop(stack);
                }
                int arr = BcreateArray(BOX(n), args);
                stack_push(stack, arr);
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
