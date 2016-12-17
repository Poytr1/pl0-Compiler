#include <stdio.h>


#define NRW        18     // number of reserved words

#define TXMAX      500    // length of identifier table
#define MAXNUMLEN  14     // maximum number of digits in numbers
#define NSYM       14     // maximum number of symbols in array ssym and csym
#define MAXIDLEN   10     // length of identifiers

#define MAXADDRESS 32767  // maximum address
#define MAXLEVEL   32     // maximum depth of nesting block
#define CXMAX      500    // size of code array

#define MAXDIM     5
#define AXMAX      10
#define MAXSYM     30     // maximum number of symbols  

#define STACKSIZE  1000   // maximum storage

enum symtype
{
	SYM_NULL,//0
	SYM_IDENTIFIER,//1
	SYM_NUMBER,//2
	SYM_PLUS,//3
	SYM_MINUS,//4
	SYM_TIMES,//5
	SYM_SLASH,//6
	SYM_ODD,//7
	SYM_EQU,//8
	SYM_NEQ,//9
	SYM_LES,//10
	SYM_LEQ,//11
	SYM_GTR,//12
	SYM_GEQ,//13
    SYM_AND,//14
    SYM_OR,//15
	SYM_NOT,//16
	SYM_LPAREN,//17
	SYM_RPAREN,//18
	SYM_COMMA,//19
	SYM_SEMICOLON,//20
	SYM_PERIOD,//21
	SYM_BECOMES,//22
    SYM_BEGIN,//23
	SYM_BREAK,//24
	SYM_ELSE,//25
	SYM_END,//26
	SYM_EXIT,//27
	SYM_FOR,//28
	SYM_IF,//29
	SYM_THEN,//30
	SYM_WHILE,//31
	SYM_DO,//32
	SYM_CALL,//33
	SYM_CONST,//34
	SYM_VAR,//35
	SYM_PROCEDURE,//36
	SYM_COLON,//37
	SYM_ARRAY,//38
	SYM_RMATCH,//39
	SYM_WRITE,//40
	SYM_READ, //41
	SYM_CONTINUE//42

};

enum idtype
{
	ID_CONSTANT, ID_VARIABLE, ID_PROCEDURE, ID_ARRAY
};

enum opcode
{
	LIT, OPR, LOD, STO, CAL, INT, JMP, JPC, POPA,
	REVA, JPF, JPT, JEQ, JNE, JL, JLE, JG, JGE, LODA, STOA, WRITE,WRITEA, READ, READA
};

enum oprcode
{
	OPR_RET, OPR_NEG, OPR_ADD, OPR_MIN,
	OPR_MUL, OPR_DIV, OPR_ODD, OPR_EQU,
	OPR_NEQ, OPR_LES, OPR_LEQ, OPR_GTR,
	OPR_GEQ, OPR_CPY, OPR_OPP, OPR_AND,
    OPR_OR
};


typedef struct
{
	int f; // function code
	int l; // level
	int a; // displacement address
} instruction;

//////////////////////////////////////////////////////////////////////
char* err_msg[] =
{
/*  0 */    "",
/*  1 */    "Found ':=' when expecting '='.",
/*  2 */    "There must be a number to follow '='.",
/*  3 */    "There must be an '=' to follow the identifier.",
/*  4 */    "There must be an identifier to follow 'const', 'var', or 'procedure'.",
/*  5 */    "Missing ',' or ';'.",
/*  6 */    "Incorrect procedure name.",
/*  7 */    "Statement expected.",
/*  8 */    "Follow the statement is an incorrect symbol.",
/*  9 */    "'.' expected.",
/* 10 */    "';' expected.",
/* 11 */    "Undeclared identifier.",
/* 12 */    "Illegal assignment.",
/* 13 */    "':=' expected.",
/* 14 */    "There must be an identifier to follow the 'call'.",
/* 15 */    "A constant or variable can not be called.",
/* 16 */    "'then' expected.",
/* 17 */    "';' or 'end' expected.",
/* 18 */    "'do' expected.",
/* 19 */    "Incorrect symbol.",
/* 20 */    "Relative operators expected.",
/* 21 */    "Procedure identifier can not be in an expression.",
/* 22 */    "Missing ')'.",
/* 23 */    "The symbol can not be followed by a factor.",
/* 24 */    "The symbol can not be as the beginning of an expression.",
/* 25 */    "The number is too great.",
/* 26 */    "There are too many actual parameters.",
/* 27 */    "There are too few actual parameters.",
/* 28 */    "Missing ':'.",
/* 29 */    "vardeclaration expected",
/* 30 */    "",
/* 31 */    "",
/* 32 */    "There are too many levels."
};

//////////////////////////////////////////////////////////////////////
char ch;         // last character read
int  sym;        // last symbol read
char id[MAXIDLEN + 1]; // last identifier read
int  num;        // last number read
int  cc;         // character count
int  ll;         // line length
int  kk;
int  err;
int  cx;         // index of current instruction to be generated.
int  level = 0;
int  tx = 0;
int  ax = 0;
int  scx[100] = {0};       //index for short-circuit logic operation
int  andOr[100] = {-1};             //0 stand for and,1 stand for or
int  ccx = 0;
int  m = 0;
////////////////for break
int loop_level;
int loop_begin[20];
struct break_link_list{
	int break_point;
	struct break_link_list *next;
};
struct break_link_list *breaks[20];
int exit_point[20];
/////////////////

char line[80];

instruction code[CXMAX];
char* word[NRW + 1] =
{
	"", /* place holder */

	"begin", "break","call", "const","continue", "do", "else","end","exit","for","if",

	"odd", "procedure","read", "then", "var", "while","write"
};

int wsym[NRW + 1] =
{

	SYM_NULL, SYM_BEGIN,SYM_BREAK, SYM_CALL, SYM_CONST,SYM_CONTINUE, SYM_DO,SYM_ELSE, SYM_END,SYM_EXIT,SYM_FOR,
	SYM_IF, SYM_ODD, SYM_PROCEDURE, SYM_READ, SYM_THEN, SYM_VAR, SYM_WHILE, SYM_WRITE
};

int ssym[NSYM + 1] =
{
	SYM_NULL, SYM_PLUS, SYM_MINUS, SYM_TIMES, SYM_SLASH,
	SYM_LPAREN, SYM_RPAREN, SYM_EQU, SYM_COMMA, SYM_PERIOD,
    SYM_SEMICOLON, SYM_COLON, SYM_AND, SYM_OR, SYM_NOT
};

char csym[NSYM + 1] =
{
	' ', '+', '-', '*', '/', '(', ')', '=', ',', '.', ';', ':', '&', '|', '!'
};

#define MAXINS   23
char* mnemonic[MAXINS] =
{
	"LIT", "OPR", "LOD", "STO", "CAL", "INT", "JMP", "JPC", "POPA", "REVA",
	"JPF", "JPT", "JEQ", "JNE", "JL", "JLE", "JG", "JGE", "LODA", "STOA", "WRITE", "WRITEA","READ"
};

typedef struct
{
	char name[MAXIDLEN + 1];
	int  kind;
	int  value;
} comtab;

typedef struct mask
{
	char  name[MAXIDLEN + 1];
	int   kind;
	int   value;
	short level;
	short address;
	struct mask * para_link;
	short para_num;
} mask;

typedef struct
{
	char name[MAXIDLEN + 1];
	int n_dim;
	int sum;
	int dim[MAXDIM];
	int size[MAXDIM];
	int first_adr;
} arr;

arr array_temp,table_arr[AXMAX];
mask table[TXMAX];
FILE* infile;

// EOF PL0.h
