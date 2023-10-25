#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  TK_LPAREN,
  TK_RPAREN,
  TK_DOT,
  TK_SINGLE_QUOTE,
  TK_SYMBOL,
  TK_NUM,
  TK_EOF,
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
  default:
    break;
  }
}

Node *new_node_num(int val) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_NUM;
  node->val = val;
  return node;
}

Node *new_node_symbol(char *str, int length) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_SYMBOL;
  node->str = str;
  node->str_length = length;
  return node;
}

Node *new_node_define(Node *define_symbol, Node *body) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_DEFINE;
  node->define_symbol = define_symbol;
  node->body = body;
  return node;
}

Node *new_node_let(Node **symbols, int symbols_length, Node **let_value,
                   Node *body) {
  Node *node = calloc(1, sizeof(Node));
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
  node->kind = ND_LAMBDA;
  node->symbols = symbols;
  node->symbols_length = symbols_length;
  node->body = body;
  return node;
}

Node *new_node_list(Node **item, int item_length) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_LIST;
  node->item = item;
  node->item_length = item_length;
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

Node *inner_list() {
  int max_item_length = 10;
  Node **item = calloc(max_item_length, sizeof(Node *));
  int item_length = 0;
  while (!consume_rparen()) {
    Node *node = expr();
    item[item_length] = node;
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

Node *list() {
  if (consume_lparen()) {
    return inner_list();
  } else {
    error("expected list");
  }
}

Node *const_value();

Node *quote() {
  if (consume_single_quote()) {
    Node *quote = new_node_symbol("quote", 5);
    Node *node = const_value();
    Node **item = calloc(2, sizeof(Node *));
    item[0] = quote;
    item[1] = node;
    return new_node_list(item, 2);
  } else {
    error("expected quote");
  }
}

Node *const_value() {
  if (token->kind == TK_NUM) {
    return num();
  }
  if (token->kind == TK_SYMBOL) {
    return symbol();
  }
  if (token->kind == TK_LPAREN) {
    return list();
  }
  if (token->kind == TK_SINGLE_QUOTE) {
    return quote();
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
      Node **let_value = calloc(max_symbols_length, sizeof(Node *));
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
    return inner_list();
  }
  if (token->kind == TK_LPAREN) {
    Node *list_ = list();
    return list_;
  }
  if (token->kind == TK_SYMBOL) {
    Node *symbol_ = symbol();
    return symbol_;
  }
  if (token->kind == TK_NUM) {
    Node *num_ = num();
    return num_;
  }
  if (token->kind == TK_SINGLE_QUOTE) {
    Node *quote_ = quote();
    return quote_;
  }
  error("unimplemented");
}

int main(int argc, char **argv) {
  if (argc != 2) {
    error("引数の個数が正しくありません");
    return 1;
  }

  // トークナイズする
  token = tokenize(argv[1]);
  Node *node = expr();
  if (!at_eof()) {
    error("すべての入力が消費されませんでした。");
  };
  print_node(node);

  return 0;
}

typedef enum IRKind {
  IR_ID,
  IR_IDC,
  IR_IDG,
  IR_IDF,
  IR_ARGS,
  IR_APP,
  IR_RTN,
  IR_SEL,
  IR_JOIN,
  IR_POP,
  IR_DEF,
  IR_STOP,
} IRKind;

typedef struct IR {
  IRKind kind;
} IR;
