#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef enum {
  TK_LPAREN,
  TK_RPAREN,
  TK_DOT,
  TK_SINGLE_QUOTE,
  TK_SYMBOL,
  TK_NUM,
  TK_EOF,
  TK_TRUE,
  TK_FALSE,
} TokenKind;

typedef struct Token Token;

struct Token {
  TokenKind kind;
  Token *next;
  int val;
  char *str;
  // シンボルの長さ
  int length;
};

Token *token;

void print_token(Token *token) {
  while (token->kind != TK_EOF) {
    switch (token->kind) {
    case TK_LPAREN:
      printf("LPAREN\n");
      break;
    case TK_RPAREN:
      printf("RPAREN\n");
      break;
    case TK_DOT:
      printf("DOT\n");
      break;
    case TK_SINGLE_QUOTE:
      printf("SINGLE_QUOTE\n");
      break;
    case TK_SYMBOL:
      printf("SYMBOL %.*s\n", token->length, token->str);
      break;
    case TK_NUM:
      printf("NUM %d\n", token->val);
      break;
    case TK_TRUE:
      printf("TRUE\n");
      break;
    case TK_FALSE:
      printf("FALSE\n");
      break;
    case TK_EOF:
      printf("EOF\n");
      break;
    default:
      break;
    }
    token = token->next;
  }
}

void error(char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\n");
  exit(1);
}

bool consume_lparen() {
  if (token->kind != TK_LPAREN) {
    return false;
  }
  token = token->next;
  return true;
}

void expect_lparen() {
  if (token->kind != TK_LPAREN) {
    error("expected '('");
  }
  token = token->next;
}

bool consume_rparen() {
  if (token->kind != TK_RPAREN) {
    return false;
  }
  token = token->next;
  return true;
}

bool consume_single_quote() {
  if (token->kind != TK_SINGLE_QUOTE) {
    return false;
  }
  token = token->next;
  return true;
}

void expect_rparen() {
  if (token->kind != TK_RPAREN) {
    error("expected ')'");
  }
  token = token->next;
}

int expect_number() {
  if (token->kind != TK_NUM) {
    error("expected a number");
  }
  int val = token->val;
  token = token->next;
  return val;
}

bool at_eof() { return token->kind == TK_EOF; }

Token *new_token(TokenKind kind, Token *cur, char *str) {
  Token *tok = calloc(1, sizeof(Token));
  if (tok == NULL) {
    error("failed to calloc");
  }
  tok->kind = kind;
  tok->str = str;
  cur->next = tok;
  return tok;
}

bool is_symbol_char(char c) {
  return (isalnum(c) || c == '+' || c == '-' || c == '*' || c == '/' ||
          c == '<' || c == '>' || c == '=' || c == '?' || c == '!' ||
          c == '_' || c == '%' || c == '&' || c == '$' || c == '^' ||
          c == '~' || c == '@' || c == ':' || c == '{' || c == '}');
}

Token *tokenize(char *p) {
  Token head;
  head.next = NULL;
  Token *cur = &head;

  while (*p) {
    if (isspace(*p)) {
      p++;
      continue;
    }

    if (*p == '(') {
      cur = new_token(TK_LPAREN, cur, p);
      p++;
      continue;
    }

    if (*p == ')') {
      cur = new_token(TK_RPAREN, cur, p);
      p++;
      continue;
    }

    if (*p == '\'') {
      cur = new_token(TK_SINGLE_QUOTE, cur, p);
      p++;
      continue;
    }

    if (*p == '#' && *(p + 1) == 't') {
      cur = new_token(TK_TRUE, cur, p);
      p += 2;
      continue;
    }
    if (*p == '#' && *(p + 1) == 'f') {
      cur = new_token(TK_FALSE, cur, p);
      p += 2;
      continue;
    }

    if (*p == '-' && isdigit(*(p + 1))) {
      cur = new_token(TK_NUM, cur, p);
      p++;
      cur->val = -strtol(p, &p, 10);
      continue;
    }

    if (isdigit(*p)) {
      cur = new_token(TK_NUM, cur, p);
      char *q = p;
      int num = strtol(p, &p, 10);
      if (is_symbol_char(*p)) {
        cur->kind = TK_SYMBOL;
        while (is_symbol_char(*p)) {
          p++;
        }
        cur->length = p - q;
      } else {
        cur->val = num;
      }
      continue;
    }

    // symbol
    if (is_symbol_char(*p)) {
      cur = new_token(TK_SYMBOL, cur, p);
      char *q = p;
      while (is_symbol_char(*p)) {
        p++;
      }
      cur->length = p - q;
      continue;
    }

    error("unable to tokenize");
  }

  new_token(TK_EOF, cur, p);
  return head.next;
}

typedef enum {
  ND_NUM,
  ND_SYMBOL,
  ND_DEFINE,
  ND_LET,
  ND_LAMBDA,
  ND_LIST,
  ND_TRUE,
  ND_FALSE,
} NodeKind;

typedef struct Node Node;

struct Node {
  NodeKind kind;
  // ND_LIST
  Node **item;
  int item_length;
  // ND_DEFINE
  Node *define_symbol;
  // ND_LET ND_LAMBDA
  Node **symbols;
  int symbols_length;
  // ND_LET
  Node **let_value;
  // ND_DEFINE, ND_LET, ND_LAMBDA
  Node *body;
  // ND_NUM
  int val;
  // ND_SYMBOL
  char *str;
  int str_length;
};

typedef struct NodeArray {
  Node **node;
  int length;
  int max_length;
} NodeArray;

NodeArray *new_node_array() {
  NodeArray *node_array = calloc(1, sizeof(NodeArray));
  if (node_array == NULL) {
    error("failed to calloc");
  }
  node_array->node = calloc(100, sizeof(Node *));
  if (node_array->node == NULL) {
    error("failed to calloc");
  }
  node_array->length = 0;
  node_array->max_length = 100;
  return node_array;
}

void node_array_push(NodeArray *node_array, Node *node) {
  node_array->node[node_array->length] = node;
  node_array->length++;
  if (node_array->length >= node_array->max_length) {
    Node **new_node = realloc(node_array->node, node_array->max_length * 2);
    if (new_node == NULL) {
      error("failed to realloc");
    }
    node_array->node = new_node;
    node_array->max_length *= 2;
  }
}

void print_node(Node *node) {
  switch (node->kind) {
  case ND_NUM:
    printf("ND_NUM %d", node->val);
    break;
  case ND_SYMBOL:
    printf("ND_SYMBOL %.*s", node->str_length, node->str);
    break;
  case ND_DEFINE:
    printf("ND_DEFINE");
    printf("(");
    print_node(node->define_symbol);
    printf(", ");
    print_node(node->body);
    printf(")");
    break;
  case ND_LET:
    printf("ND_LET");
    printf("(");
    for (int i = 0; i < node->symbols_length; i++) {
      printf("(");
      print_node(node->symbols[i]);
      printf(", ");
      print_node(node->let_value[i]);
      printf("),");
    }
    printf("; BODY:");
    print_node(node->body);
    printf(")");
    break;
  case ND_LAMBDA:
    printf("ND_LAMBDA");
    printf("(");
    for (int i = 0; i < node->symbols_length; i++) {
      print_node(node->symbols[i]);
      printf(", ");
    }
    printf("; BODY:");
    print_node(node->body);
    printf(")");
    break;
  case ND_LIST:
    printf("ND_LIST");
    printf("(");
    for (int i = 0; i < node->item_length; i++) {
      print_node(node->item[i]);
      printf(", ");
    }
    printf(")");
    break;
  case ND_TRUE:
    printf("ND_TRUE");
    break;
  case ND_FALSE:
    printf("ND_FALSE");
    break;
  default:
    break;
  }
}

void print_node_array(NodeArray *node_array) {
  for (int i = 0; i < node_array->length; i++) {
    print_node(node_array->node[i]);
    printf("\n");
  }
}

Node *new_node_num(int val) {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_NUM;
  node->val = val;
  return node;
}

Node *new_node_symbol(char *str, int length) {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_SYMBOL;
  node->str = str;
  node->str_length = length;
  return node;
}

Node *new_node_define(Node *define_symbol, Node *body) {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_DEFINE;
  node->define_symbol = define_symbol;
  node->body = body;
  return node;
}

Node *new_node_let(Node **symbols, int symbols_length, Node **let_value,
                   Node *body) {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_LET;
  node->symbols = symbols;
  node->symbols_length = symbols_length;
  node->let_value = let_value;
  node->body = body;
  return node;
}

Node *new_node_lambda(Node **symbols, int symbols_length, Node *body,
                      int body_length) {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_LAMBDA;
  node->symbols = symbols;
  node->symbols_length = symbols_length;
  node->body = body;
  return node;
}

Node *new_node_list(Node **item, int item_length) {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_LIST;
  node->item = item;
  node->item_length = item_length;
  return node;
}

Node *new_node_true() {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_TRUE;
  return node;
}

Node *new_node_false() {
  Node *node = calloc(1, sizeof(Node));
  if (node == NULL) {
    error("failed to calloc");
  }
  node->kind = ND_FALSE;
  return node;
}

Node *expr();

Node *symbol() {
  if (token->kind == TK_SYMBOL) {
    Node *symbol = new_node_symbol(token->str, token->length);
    token = token->next;
    return symbol;
  } else {
    error("expected symbol");
  }
}

Node *num() {
  if (token->kind == TK_NUM) {
    Node *num = new_node_num(token->val);
    token = token->next;
    return num;
  } else {
    error("expected number");
  }
}

Node *node_boolean() {
  if (token->kind == TK_TRUE) {
    token = token->next;
    return new_node_true();
  }
  if (token->kind == TK_FALSE) {
    token = token->next;
    return new_node_false();
  }
  error("expected boolean");
}

Node *const_value(bool quoted);

Node *inner_list(bool quoted) {
  int max_item_length = 10;
  Node **item = calloc(max_item_length, sizeof(Node *));
  if (item == NULL) {
    error("failed to calloc");
  }
  int item_length = 0;
  while (!consume_rparen()) {
    if (quoted) {
      Node *node = const_value(1);
      item[item_length] = node;
    } else {
      Node *node = expr();
      item[item_length] = node;
    }
    item_length++;
    if (item_length > max_item_length) {
      Node **new_item = realloc(item, max_item_length * 2);
      if (new_item == NULL) {
        error("failed to realloc");
      }
      item = new_item;
      max_item_length *= 2;
    }
    if (at_eof()) {
      error("expected ')'");
    }
  }
  return new_node_list(item, item_length);
}

Node *list(bool quoted) {
  if (consume_lparen()) {
    return inner_list(quoted);
  } else {
    error("expected list");
  }
}

Node *quote() {
  if (consume_single_quote()) {
    Node *quote = new_node_symbol("quote", 5);
    Node *node = const_value(1);
    Node **item = calloc(2, sizeof(Node *));
    if (item == NULL) {
      error("failed to calloc");
    }
    item[0] = quote;
    item[1] = node;
    return new_node_list(item, 2);
  } else {
    error("expected quote");
  }
}

Node *const_value(bool quoted) {
  if (token->kind == TK_NUM) {
    return num();
  }
  if (token->kind == TK_SYMBOL) {
    return symbol();
  }
  if (token->kind == TK_LPAREN) {
    return list(quoted);
  }
  if (token->kind == TK_SINGLE_QUOTE) {
    return quote();
  }
  if (token->kind == TK_TRUE || token->kind == TK_FALSE) {
    return node_boolean();
  }
  error("expected const value");
}

Node *expr() {
  if (consume_lparen()) {
    if (token->kind == TK_SYMBOL &&
        strncmp(token->str, "define", token->length) == 0) {
      token = token->next;
      Node *define_symbol = expr();
      if (define_symbol->kind != ND_SYMBOL) {
        error("expected symbol");
      }
      Node *body = expr();
      expect_rparen();
      return new_node_define(define_symbol, body);
    }
    if (token->kind == TK_SYMBOL &&
        strncmp(token->str, "lambda", token->length) == 0) {
      token = token->next;
      int max_symbols_length = 10;
      Node **symbols = calloc(max_symbols_length, sizeof(Node *));
      if (symbols == NULL) {
        error("failed to calloc");
      }
      int symbols_length = 0;
      expect_lparen();
      while (!consume_rparen()) {
        Node *symbol = expr();
        symbols[symbols_length] = symbol;
        symbols_length++;
        if (symbols_length > max_symbols_length) {
          Node **new_symbols = realloc(symbols, max_symbols_length * 2);
          if (new_symbols == NULL) {
            error("failed to realloc");
          }
          symbols = new_symbols;
          max_symbols_length *= 2;
        }
        if (at_eof()) {
          error("expected ')'");
        }
      }
      Node *body = expr();
      expect_rparen();
      return new_node_lambda(symbols, symbols_length, body, 1);
    }
    if (token->kind == TK_SYMBOL &&
        strncmp(token->str, "let", token->length) == 0) {
      token = token->next;
      int max_symbols_length = 10;
      Node **symbols = calloc(max_symbols_length, sizeof(Node *));
      if (symbols == NULL) {
        error("failed to calloc");
      }
      Node **let_value = calloc(max_symbols_length, sizeof(Node *));
      if (let_value == NULL) {
        error("failed to calloc");
      }
      int symbols_length = 0;
      expect_lparen();
      while (!consume_rparen()) {
        expect_lparen();
        Node *symbol = expr();
        if (symbol->kind != ND_SYMBOL) {
          error("expected symbol");
        }
        Node *value = expr();
        symbols[symbols_length] = symbol;
        let_value[symbols_length] = value;
        symbols_length++;
        if (symbols_length > max_symbols_length) {
          Node **new_symbols = realloc(symbols, max_symbols_length * 2);
          Node **new_let_value = realloc(let_value, max_symbols_length * 2);
          if (new_symbols == NULL || new_let_value == NULL) {
            error("failed to realloc");
          }
          symbols = new_symbols;
          let_value = new_let_value;
          max_symbols_length *= 2;
        }
        if (at_eof()) {
          error("expected ')'");
        }
        expect_rparen();
      }
      Node *body = expr();
      expect_rparen();
      return new_node_let(symbols, symbols_length, let_value, body);
    }
    return inner_list(0);
  }
  return const_value(0);
  error("unimplemented");
}

typedef enum IRKind {
  IR_LD,
  IR_LDC,
  IR_LDG,
  IR_LDF,
  IR_ARGS,
  IR_APP,
  IR_RTN,
  IR_SEL,
  IR_JOIN,
  IR_POP,
  IR_DEF,
  IR_STOP,
  IR_SELRTN,
  IR_TAILAPP
} IRKind;

typedef struct IR IR;
typedef struct IRArray IRArray;

struct IR {
  IRKind kind;
  // IR_LD IR_DEF IR_LDG
  int frame;
  // IR_LD IR_ARGS
  int idx_num;
  // IR_LDC
  Node *node1;
  // IR_SEL, IR_LDF
  IRArray *code;
  // IR_SEL
  IRArray *cf;
};

struct IRArray {
  IR **ir;
  int length;
  int ir_idx;
  int max_length;
};

void print_ir(IR *ir) {
  switch (ir->kind) {
  case IR_LD:
    printf("LD (%d . %d);", ir->frame, ir->idx_num);
    break;
  case IR_LDC:
    printf("LDC ");
    print_node(ir->node1);
    printf(";");
    break;
  case IR_LDG:
    printf("LDG %d;", ir->frame);
    break;
  case IR_LDF:
    printf("LDF ");
    printf("(");
    for (int i = 0; i < ir->code->length; i++) {
      print_ir(ir->code->ir[i]);
      printf(", ");
    }
    printf(");");
    break;
  case IR_ARGS:
    printf("ARGS %d;", ir->idx_num);
    break;
  case IR_APP:
    printf("APP;");
    break;
  case IR_RTN:
    printf("RTN;");
    break;
  case IR_SEL:
    printf("SEL ");
    printf("(");
    for (int i = 0; i < ir->code->length; i++) {
      print_ir(ir->code->ir[i]);
      printf(", ");
    }
    printf("), (");
    for (int i = 0; i < ir->cf->length; i++) {
      print_ir(ir->cf->ir[i]);
      printf(", ");
    }
    printf(");");
    break;
  case IR_JOIN:
    printf("JOIN;");
    break;
  case IR_POP:
    printf("POP;");
    break;
  case IR_DEF:
    printf("DEF %d;", ir->frame);
    break;
  case IR_STOP:
    printf("STOP;");
    break;
  case IR_SELRTN:
    printf("SELRTN ");
    printf("(");
    for (int i = 0; i < ir->code->length; i++) {
      print_ir(ir->code->ir[i]);
      printf(", ");
    }
    printf("), (");
    for (int i = 0; i < ir->cf->length; i++) {
      print_ir(ir->cf->ir[i]);
      printf(", ");
    }
    printf(");");
    break;
  case IR_TAILAPP:
    printf("TAILAPP;");
    break;
  default:
    error("unimplemented");
    break;
  }
}

IR *new_ir_id(int frame, int idx_num) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_LD;
  ir->frame = frame;
  ir->idx_num = idx_num;
  return ir;
}

IR *new_ir_idc(Node *node1) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_LDC;
  ir->node1 = node1;
  return ir;
}

IR *new_ir_idg(int frame) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_LDG;
  ir->frame = frame;
  return ir;
}

IR *new_ir_idf(IRArray *code) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_LDF;
  ir->code = code;
  return ir;
}

IR *new_ir_args(int n) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_ARGS;
  ir->idx_num = n;
  return ir;
}

IR *new_ir_app() {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_APP;
  return ir;
}

IR *new_ir_rtn() {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_RTN;
  return ir;
}

IR *new_ir_sel(IRArray *ct, IRArray *cf) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_SEL;
  ir->code = ct;
  ir->cf = cf;
  return ir;
}

IR *new_ir_join() {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_JOIN;
  return ir;
}

IR *new_ir_pop() {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_POP;
  return ir;
}

IR *new_ir_def(int frame) {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_DEF;
  ir->frame = frame;
  return ir;
}

IR *new_ir_stop() {
  IR *ir = calloc(1, sizeof(IR));
  if (ir == NULL) {
    error("failed to calloc");
  }
  ir->kind = IR_STOP;
  return ir;
}

void print_ir_array(IRArray *ir_array) {
  for (int i = 0; i < ir_array->length; i++) {
    print_ir(ir_array->ir[i]);
    printf("\n");
  }
}

IRArray *new_ir_array() {
  IRArray *ir_array = calloc(1, sizeof(IRArray));
  if (ir_array == NULL) {
    error("failed to calloc");
  }
  ir_array->ir = calloc(100, sizeof(IR *));
  if (ir_array->ir == NULL) {
    error("failed to calloc");
  }
  ir_array->length = 0;
  ir_array->ir_idx = 0;
  ir_array->max_length = 100;
  return ir_array;
}

void ir_array_push(IRArray *ir_array, IR *ir) {
  ir_array->ir[ir_array->length] = ir;
  ir_array->length++;
  if (ir_array->length >= ir_array->max_length) {
    IR **new_ir = realloc(ir_array->ir, ir_array->max_length * 2);
    if (new_ir == NULL) {
      error("failed to realloc");
    }
    ir_array->ir = new_ir;
    ir_array->max_length *= 2;
  }
}

typedef enum ValueKind {
  ValueInt,
  ValueBool,
  ValueList,
  ValueSymbol,
  ValueClosure,
  ValuePrimitive,
  ValueNil,
  ValueFrame
} ValueKind;

typedef struct Frame Frame;
typedef struct Environment Environment;

typedef struct Value Value;

struct Value {
  ValueKind kind;
  union {
    int val;
    bool bool_val;
    struct {
      Value *car;
      Value *cdr;
    };
    char *str;
    struct {
      Environment *env;
      IRArray *code;
    };
    struct {
      char *primitive_name;
    };
    struct {
      Frame *frame;
    };
  };
};

void print_value(Value *value) {
  switch (value->kind) {
  case ValueInt:
    printf("%d", value->val);
    break;
  case ValueBool:
    if (value->bool_val) {
      printf("#t");
    } else {
      printf("#f");
    }
    break;
  case ValueList:
    printf("(");
    print_value(value->car);
    printf(", ");
    print_value(value->cdr);
    printf(")");
    break;
  case ValueSymbol:
    printf("'%s", value->str);
    break;
  case ValueClosure:
    printf("ValueClosure");
    printf("(");
    print_ir_array(value->code);
    printf(")");
    break;
  case ValuePrimitive:
    printf("ValuePrimitive %s", value->primitive_name);
    break;
  case ValueNil:
    printf("'()");
    break;
  case ValueFrame:
    printf("ValueFrame");
    break;
  default:
    break;
  }
}

Value *new_value_int(int val) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueInt;
  value->val = val;
  return value;
};

Value *new_value_bool(bool bool_val) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueBool;
  value->bool_val = bool_val;
  return value;
};

Value *new_value_symbol(char *str) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueSymbol;
  value->str = str;
  return value;
};

Value *new_value_list(Value *car, Value *cdr) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueList;
  value->car = car;
  value->cdr = cdr;
  return value;
};

Value *new_value_closure(Environment *env, IRArray *code) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueClosure;
  value->env = env;
  value->code = code;
  return value;
};

Value *new_value_primitive(char *primitive_name) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValuePrimitive;
  value->primitive_name = primitive_name;
  return value;
};

Value *new_value_nil() {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueNil;
  return value;
};

Value *new_value_frame(Frame *frame) {
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  value->kind = ValueFrame;
  value->frame = frame;
  return value;
};

struct Frame {
  Value **value;
  char **symbol;
  int length;
  int max_length;
};

Frame *new_frame(int size) {
  Frame *frame = calloc(1, sizeof(Frame));
  if (frame == NULL) {
    error("failed to calloc");
  }
  frame->value = calloc(size, sizeof(Value *));
  if (frame->value == NULL) {
    error("failed to calloc");
  }
  frame->symbol = calloc(size, sizeof(char *));
  if (frame->symbol == NULL) {
    error("failed to calloc");
  }
  frame->length = 0;
  frame->max_length = size;
  return frame;
}

void frame_new_symbol(Frame *frame, char *symbol) {
  frame->symbol[frame->length] = symbol;
  Value *value = calloc(1, sizeof(Value));
  if (value == NULL) {
    error("failed to calloc");
  }
  frame->value[frame->length] = value;
  frame->length++;
  if (frame->length > frame->max_length) {
    Value **new_value = realloc(frame->value, frame->max_length * 2);
    char **new_symbol = realloc(frame->symbol, frame->max_length * 2);
    if (new_value == NULL || new_symbol == NULL) {
      error("failed to realloc");
    }
    frame->value = new_value;
    frame->symbol = new_symbol;
    frame->max_length *= 2;
  }
}

int frame_find_symbol(Frame *frame, char *symbol) {
  for (int i = 0; i < frame->length; i++) {
    if (strcmp(frame->symbol[i], symbol) == 0) {
      return i;
    }
  }
  return -1;
}

Value *frame_get_value(Frame *frame, int idx_num) {
  Value *copy_value = calloc(1, sizeof(Value));
  if (copy_value == NULL) {
    error("failed to calloc");
  }
  memcpy(copy_value, frame->value[idx_num], sizeof(Value));
  return copy_value;
}

struct Environment {
  Frame **frame;
  int length;
  int max_length;
};

Environment *new_environment(int size) {
  Environment *environment = calloc(1, sizeof(Environment));
  if (environment == NULL) {
    error("failed to calloc");
  }
  environment->frame = calloc(size, sizeof(Frame *));
  if (environment->frame == NULL) {
    error("failed to calloc");
  }
  environment->length = 0;
  environment->max_length = size;
  return environment;
}

void environment_push(Environment *environment, Frame *frame) {
  environment->frame[environment->length] = frame;
  environment->length++;
  if (environment->length >= environment->max_length) {
    Frame **new_frame =
        realloc(environment->frame, environment->max_length * 2);
    if (new_frame == NULL) {
      error("failed to realloc");
    }
    environment->frame = new_frame;
    environment->max_length *= 2;
  }
}

void environment_pop(Environment *environment) {
  if (environment->length <= 0) {
    environment->length = 0;
  } else {
    environment->length--;
  }
}

Environment *deepcopy_environment(Environment *env) {
  Environment *new_env = new_environment(env->max_length);
  for (int i = 0; i < env->length; i++) {
    Frame *frame = env->frame[i];
    Frame *new_frame_ = new_frame(frame->max_length);
    memcpy(new_frame_, frame, sizeof(Frame));
    environment_push(new_env, new_frame_);
  }
  return new_env;
}

typedef struct Index {
  int frame;
  int idx_num;
} Index;

Index environment_find_symbol(Environment *environment, char *symbol) {
  for (int i = environment->length - 1; i >= 0; i--) {
    int idx_num = frame_find_symbol(environment->frame[i], symbol);
    if (idx_num != -1) {
      Index index;
      index.frame = i;
      index.idx_num = idx_num;
      return index;
    }
  }
  Index index;
  index.frame = -1;
  index.idx_num = -1;
  return index;
}

Frame *GlobalEnvironment;

void globalenv_push_default(char *symbol, Value *value) {
  GlobalEnvironment->symbol[GlobalEnvironment->length] = symbol;
  GlobalEnvironment->value[GlobalEnvironment->length] = value;
  GlobalEnvironment->length++;
  if (GlobalEnvironment->length >= GlobalEnvironment->max_length) {
    Value **new_value =
        realloc(GlobalEnvironment->value, GlobalEnvironment->max_length * 2);
    char **new_symbol =
        realloc(GlobalEnvironment->symbol, GlobalEnvironment->max_length * 2);
    if (new_value == NULL || new_symbol == NULL) {
      error("failed to realloc");
    }
    GlobalEnvironment->value = new_value;
    GlobalEnvironment->symbol = new_symbol;
    GlobalEnvironment->max_length *= 2;
  }
}

void tail_call_optimization(IRArray *ir_array) {
  if (ir_array->length < 2) {
    return;
  }
  IR *ir1 = ir_array->ir[ir_array->length - 1];
  IR *ir2 = ir_array->ir[ir_array->length - 2];
  if (ir1->kind != IR_RTN) {
    return;
  }
  if (ir2->kind == IR_APP) {
    ir2->kind = IR_TAILAPP;
    return;
  } else if (ir2->kind == IR_SEL) {
    IRArray *ct = ir2->code;
    IRArray *cf = ir2->cf;
    ct->ir[ct->length - 1]->kind = IR_RTN;
    cf->ir[cf->length - 1]->kind = IR_RTN;
    ir2->kind = IR_SELRTN;
    tail_call_optimization(ct);
    tail_call_optimization(cf);
    ir_array->length -= 1;
    return;
  }
}

void *ast_to_ir(IRArray *ir_array, Node *ast, Environment *env) {
  switch (ast->kind) {
  case ND_NUM:
    ir_array_push(ir_array, new_ir_idc(ast));
    break;
  case ND_TRUE:
    ir_array_push(ir_array, new_ir_idc(ast));
    break;
  case ND_FALSE:
    ir_array_push(ir_array, new_ir_idc(ast));
    break;
  case ND_SYMBOL: {
    char *symbol_name = calloc(ast->str_length + 1, sizeof(char));
    if (symbol_name == NULL) {
      error("failed to calloc");
    }
    strncpy(symbol_name, ast->str, ast->str_length);
    Index index = environment_find_symbol(env, symbol_name);
    if (index.frame == -1) {
      int frame = frame_find_symbol(GlobalEnvironment, symbol_name);
      if (frame == -1) {
        error("undefined symbol");
      }
      ir_array_push(ir_array, new_ir_idg(frame));
    } else {
      ir_array_push(ir_array, new_ir_id(index.frame, index.idx_num));
    }
    break;
  }
  case ND_LIST:
    if (ast->item_length == 0) {
      error("unexpected empty list");
    }
    if (ast->item[0]->kind == ND_SYMBOL &&
        strncmp(ast->item[0]->str, "quote", ast->item[0]->str_length) == 0) {
      if (ast->item_length != 2) {
        error("illegal argument length for quote");
      }
      ir_array_push(ir_array, new_ir_idc(ast->item[1]));
      break;
    }
    if (ast->item[0]->kind == ND_SYMBOL &&
        strncmp(ast->item[0]->str, "if", ast->item[0]->str_length) == 0) {
      if (ast->item_length != 4) {
        error("illegal argument length for if");
      }
      Node *cond = ast->item[1];
      ast_to_ir(ir_array, cond, env);
      Node *ct = ast->item[2];
      Node *cf = ast->item[3];
      IRArray *ct_ir_array = new_ir_array();
      IRArray *cf_ir_array = new_ir_array();
      ast_to_ir(ct_ir_array, ct, env);
      ir_array_push(ct_ir_array, new_ir_join());
      ast_to_ir(cf_ir_array, cf, env);
      ir_array_push(cf_ir_array, new_ir_join());
      ir_array_push(ir_array, new_ir_sel(ct_ir_array, cf_ir_array));
      break;
    }
    // else
    //  function call
    for (int i = ast->item_length - 1; i >= 1; i--) {
      ast_to_ir(ir_array, ast->item[i], env);
    }
    ir_array_push(ir_array, new_ir_args(ast->item_length - 1));
    ast_to_ir(ir_array, ast->item[0], env);
    ir_array_push(ir_array, new_ir_app());
    break;
  case ND_DEFINE:
    if (ast->define_symbol->kind != ND_SYMBOL) {
      error("expected symbol");
    }
    char *symbol_name =
        calloc(ast->define_symbol->str_length + 1, sizeof(char));
    if (symbol_name == NULL) {
      error("failed to calloc");
    }
    strncpy(symbol_name, ast->define_symbol->str,
            ast->define_symbol->str_length);
    int frame = frame_find_symbol(GlobalEnvironment, symbol_name);
    if (frame == -1) {
      frame_new_symbol(GlobalEnvironment, symbol_name);
      frame = GlobalEnvironment->length - 1;
    }
    ast_to_ir(ir_array, ast->body, env);
    ir_array_push(ir_array, new_ir_def(frame));
    break;
  case ND_LET:
    break;
  case ND_LAMBDA: {
    IRArray *body = new_ir_array();
    Frame *frame = new_frame(10);
    for (int i = 0; i < ast->symbols_length; i++) {
      char *symbol_name = calloc(ast->symbols[i]->str_length + 1, sizeof(char));
      if (symbol_name == NULL) {
        error("failed to calloc");
      }
      strncpy(symbol_name, ast->symbols[i]->str, ast->symbols[i]->str_length);
      frame_new_symbol(frame, symbol_name);
    }
    environment_push(env, frame);
    ast_to_ir(body, ast->body, env);
    ir_array_push(body, new_ir_rtn());
    tail_call_optimization(body);
    environment_pop(env);
    ir_array_push(ir_array, new_ir_idf(body));
    break;
  }
  }
}

typedef struct SECD SECD;
typedef struct SEC SEC;

typedef struct Dump {
  SEC **sec;
  int length;
  int max_length;
} Dump;

struct SECD {
  Value **stack;
  int stack_length;
  int stack_max_length;
  Environment *env;
  IRArray *code;
  Dump *dump;
};

struct SEC {
  Value **stack;
  int stack_length;
  int stack_max_length;
  Environment *env;
  IRArray *code;
};

SECD *new_secd(int stack_size, int dump_size, Environment *env, IRArray *code) {
  SECD *secd = calloc(1, sizeof(SECD));
  if (secd == NULL) {
    error("failed to calloc");
  }
  secd->stack = calloc(stack_size, sizeof(Value *));
  if (secd->stack == NULL) {
    error("failed to calloc");
  }
  secd->stack_length = 0;
  secd->stack_max_length = stack_size;
  secd->env = env;
  secd->code = code;
  secd->dump = calloc(1, sizeof(Dump));
  if (secd->dump == NULL) {
    error("failed to calloc");
  }
  secd->dump->sec = calloc(dump_size, sizeof(SEC *));
  if (secd->dump->sec == NULL) {
    error("failed to calloc");
  }
  secd->dump->length = 0;
  secd->dump->max_length = dump_size;
  return secd;
}

SEC *new_sec(int stack_size, Environment *env, IRArray *code) {
  SEC *sec = calloc(1, sizeof(SEC));
  if (sec == NULL) {
    error("failed to calloc");
  }
  sec->stack = calloc(stack_size, sizeof(Value *));
  if (sec->stack == NULL) {
    error("failed to calloc");
  }
  sec->stack_length = 0;
  sec->stack_max_length = stack_size;
  sec->env = env;
  sec->code = code;
  return sec;
}

void stack_push(SECD *secd, Value *value) {
  secd->stack[secd->stack_length] = value;
  secd->stack_length++;
  if (secd->stack_length >= secd->stack_max_length) {
    Value **new_stack = realloc(secd->stack, secd->stack_max_length * 2);
    if (new_stack == NULL) {
      error("failed to realloc");
    }
    secd->stack = new_stack;
    secd->stack_max_length *= 2;
  }
}

Value *stack_pop(SECD *secd) {
  if (secd->stack_length <= 0) {
    error("stack underflow");
  }
  secd->stack_length--;
  Value *value = secd->stack[secd->stack_length];
  return value;
}

void dump_push(Dump *dump, SEC *sec) {
  dump->sec[dump->length] = sec;
  dump->length++;
  if (dump->length >= dump->max_length) {
    printf("dump overflow\n");
    exit(1);
  }
}

SEC *dump_pop(Dump *dump) {
  if (dump->length <= 0) {
    error("dump underflow");
  }
  dump->length--;
  SEC *sec = dump->sec[dump->length];
  return sec;
}

Value *const_node_to_value(Node *node) {
  switch (node->kind) {
  case ND_NUM:
    return new_value_int(node->val);
  case ND_TRUE:
    return new_value_bool(true);
  case ND_FALSE:
    return new_value_bool(false);
  case ND_SYMBOL: {
    char *symbol_name = calloc(node->str_length + 1, sizeof(char));
    if (symbol_name == NULL) {
      error("failed to calloc");
    }
    strncpy(symbol_name, node->str, node->str_length);
    return new_value_symbol(symbol_name);
  }
  case ND_LIST: {
    Value *list = new_value_nil();
    for (int i = node->item_length - 1; i >= 0; i--) {
      Value *value = const_node_to_value(node->item[i]);
      list = new_value_list(value, list);
    }
    return list;
  }
  default:
    error("unimplemented");
  }
}

void run_virtual_machine(SECD *secd) {
  while (1) {
    IR *ir = secd->code->ir[secd->code->ir_idx];

    // if (secd->stack_length > 0) {
    //   printf("stack: ");
    //   for (int i = 0; i < secd->stack_length; i++) {
    //     print_value(secd->stack[i]);
    //     printf(", ");
    //   }
    //   printf("\n\n");
    // }
    // printf("ir: ");
    // print_ir(ir);
    // printf("%d", secd->code->ir_idx);
    // printf("\n");

    secd->code->ir_idx++;
    switch (ir->kind) {
    case IR_LD: {
      Value *value = secd->env->frame[ir->frame]->value[ir->idx_num];
      stack_push(secd, value);
      break;
    }
    case IR_LDC: {
      Value *value = const_node_to_value(ir->node1);
      stack_push(secd, value);
      break;
    }
    case IR_LDG: {
      Value *value = GlobalEnvironment->value[ir->frame];
      stack_push(secd, value);
      break;
    }
    case IR_LDF: {
      Value *value = new_value_closure(secd->env, ir->code);
      stack_push(secd, value);
      break;
    }
    case IR_ARGS: {
      int args_length = ir->idx_num;
      Frame *frame = new_frame(args_length);
      for (int i = 0; i < args_length; i++) {
        Value *value = stack_pop(secd);
        frame->value[i] = value;
        frame->length++;
      }
      stack_push(secd, new_value_frame(frame));
      break;
    }
    case IR_TAILAPP:
    case IR_APP: {
      Value *func = stack_pop(secd);
      Value *args = stack_pop(secd);
      if (func->kind == ValuePrimitive) {
        if (strcmp(func->primitive_name, "+") == 0) {
          int result = 0;
          for (int i = 0; i < args->frame->length; i++) {
            Value *value = args->frame->value[i];
            if (value->kind != ValueInt) {
              error("expected int");
            }
            result += value->val;
          }
          stack_push(secd, new_value_int(result));
        } else if (strcmp(func->primitive_name, "-") == 0) {
          if (args->frame->length == 0) {
            error("wrong argument length");
          }
          if (args->frame->value[0]->kind != ValueInt) {
            error("expected int");
          }
          int result = args->frame->value[0]->val;
          for (int i = 1; i < args->frame->length; i++) {
            Value *value = args->frame->value[i];
            if (value->kind != ValueInt) {
              error("expected int");
            }
            result -= value->val;
          }
          stack_push(secd, new_value_int(result));
        } else if (strcmp(func->primitive_name, "*") == 0) {
          int result = 1;
          for (int i = 0; i < args->frame->length; i++) {
            Value *value = args->frame->value[i];
            if (value->kind != ValueInt) {
              error("expected int");
            }
            result *= value->val;
          }
          stack_push(secd, new_value_int(result));
        } else if (strcmp(func->primitive_name, "/") == 0) {
          if (args->frame->length == 0) {
            error("wrong argument length");
          }
          if (args->frame->value[0]->kind != ValueInt) {
            error("expected int");
          }
          int result = args->frame->value[0]->val;
          for (int i = 1; i < args->frame->length; i++) {
            Value *value = args->frame->value[i];
            if (value->kind != ValueInt) {
              error("expected int");
            }
            result /= value->val;
          }
          stack_push(secd, new_value_int(result));
        } else if (strcmp(func->primitive_name, "=") == 0) {
          Value *result = new_value_bool(true);
          for (int i = 0; i < args->frame->length - 1; i++) {
            Value *value1 = args->frame->value[i];
            Value *value2 = args->frame->value[i + 1];
            if (value1->kind != ValueInt || value2->kind != ValueInt) {
              error("expected int");
            }
            if (value1->val != value2->val) {
              result->bool_val = false;
              break;
            }
          }
          stack_push(secd, result);
        }
      } else if (ir->kind == IR_APP && func->kind == ValueClosure) {
        Frame *frame = new_frame(args->frame->length);
        frame->value = args->frame->value;
        IRArray *code = calloc(1, sizeof(IRArray));
        if (code == NULL) {
          error("failed to calloc");
        }
        memcpy(code, func->code, sizeof(IRArray));
        SEC *sec = new_sec(secd->stack_length, secd->env, secd->code);
        sec->stack = secd->stack;
        sec->stack_length = secd->stack_length;
        sec->stack_max_length = secd->stack_max_length;
        Environment *env = deepcopy_environment(func->env);
        environment_push(env, frame);
        secd->stack_max_length = 100;
        secd->stack = calloc(secd->stack_max_length, sizeof(Value *));
        if (secd->stack == NULL) {
          error("failed to calloc");
        }
        secd->stack_length = 0;
        secd->env = env;
        secd->code = code;
        dump_push(secd->dump, sec);
      } else if (ir->kind == IR_TAILAPP && func->kind == ValueClosure) {
        Frame *frame = new_frame(args->frame->length);
        frame->value = args->frame->value;
        IRArray *code = calloc(1, sizeof(IRArray));
        if (code == NULL) {
          error("failed to calloc");
        }
        memcpy(code, func->code, sizeof(IRArray));
        Environment *env = deepcopy_environment(func->env);
        environment_push(env, frame);
        secd->env = env;
        secd->code = code;
      } else {
        error("expected closure");
      }
      break;
    }
    case IR_RTN: {
      SEC *sec = dump_pop(secd->dump);
      Value *return_value = stack_pop(secd);
      secd->stack = sec->stack;
      secd->stack_length = sec->stack_length;
      secd->stack_max_length = sec->stack_max_length;
      secd->env = sec->env;
      secd->code = sec->code;
      stack_push(secd, return_value);
      break;
    }
    case IR_SEL: {
      Value *cond = stack_pop(secd);
      if (cond->kind == ValueBool && !cond->bool_val) {
        SEC *sec = new_sec(0, secd->env, secd->code);
        IRArray *code = calloc(1, sizeof(IRArray));
        if (code == NULL) {
          error("failed to calloc");
        }
        memcpy(code, ir->cf, sizeof(IRArray));
        secd->code = code;
        dump_push(secd->dump, sec);
      } else {
        SEC *sec = new_sec(0, secd->env, secd->code);
        IRArray *code = calloc(1, sizeof(IRArray));
        if (code == NULL) {
          error("failed to calloc");
        }
        memcpy(code, ir->code, sizeof(IRArray));
        secd->code = code;
        dump_push(secd->dump, sec);
      }
      break;
    }
    case IR_SELRTN: {
      Value *cond = stack_pop(secd);
      if (cond->kind == ValueBool && !cond->bool_val) {
        IRArray *code = calloc(1, sizeof(IRArray));
        if (code == NULL) {
          error("failed to calloc");
        }
        memcpy(code, ir->cf, sizeof(IRArray));
        secd->code = code;
      } else {
        IRArray *code = calloc(1, sizeof(IRArray));
        if (code == NULL) {
          error("failed to calloc");
        }
        memcpy(code, ir->code, sizeof(IRArray));
        secd->code = code;
      }
      break;
    }
    case IR_JOIN: {
      SEC *sec = dump_pop(secd->dump);
      secd->code = sec->code;
      break;
    }
    case IR_DEF: {
      Value *value = stack_pop(secd);
      GlobalEnvironment->value[ir->frame] = value;
      break;
    }
    case IR_STOP: {
      return;
    }
    default:
      error("unimplemented");
    }
  }
}

int main(int argc, char **argv) {
  if (argc != 2) {
    error("引数の個数が正しくありません");
    return 1;
  }

  GlobalEnvironment = new_frame(100);
  globalenv_push_default("+", new_value_primitive("+"));
  globalenv_push_default("-", new_value_primitive("-"));
  globalenv_push_default("*", new_value_primitive("*"));
  globalenv_push_default("/", new_value_primitive("/"));
  globalenv_push_default("<", new_value_primitive("<"));
  globalenv_push_default("=", new_value_primitive("="));
  globalenv_push_default("car", new_value_primitive("car"));
  globalenv_push_default("cdr", new_value_primitive("cdr"));
  globalenv_push_default("cons", new_value_primitive("cons"));

  clock_t start = clock();
  // トークナイズする
  token = tokenize(argv[1]);

  NodeArray *node_array = new_node_array();
  while (token->kind != TK_EOF) {
    Node *node = expr();
    node_array_push(node_array, node);
  }
  Environment *env = new_environment(100);
  IRArray *ir_array = new_ir_array();
  for (int i = 0; i < node_array->length; i++) {
    ast_to_ir(ir_array, node_array->node[i], env);
  }
  ir_array_push(ir_array, new_ir_stop());
  // print_ir_array(ir_array);

  SECD *secd = new_secd(100, 1000000, env, ir_array);
  run_virtual_machine(secd);
  clock_t end = clock();
  printf("%f ms\n", (double)(end - start) / CLOCKS_PER_SEC * 1000);
  Value *value = stack_pop(secd);
  print_value(value);

  return 0;
}
