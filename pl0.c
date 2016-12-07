// pl0 compiler source code

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include "PL0.h"
#include "set.c"
//////////////////////////////////////////////////////////////////////
// print error message.
void error(int n)
{
	int i;

	printf("      ");
	for (i = 1; i <= cc - 1; i++)
		printf(" ");
	printf("^\n");
	printf("Error %3d: %s\n", n, err_msg[n]);
	err++;
} // error

//////////////////////////////////////////////////////////////////////
void free_para_link(mask *begin, mask *end) {
	for (; begin != end; ++ begin) {
		if ((begin->kind == SYM_PROCEDURE) && (begin->para_link != NULL)) {
			mask *p = begin->para_link;
			mask *pre = NULL;
			assert(begin->para_num > 0);
			while (1) {
				if (p->para_link == NULL) {
					free(p);
					break;
				}
				else {
					pre = p;
					p = p->para_link;
					free(pre);
				}
			}
		}
	}
} // free the parameter link

//////////////////////////////////////////////////////////////////////
void getch(void)
{
	if (cc == ll)
	{
		if (feof(infile))
		{
			printf("\nPROGRAM INCOMPLETE\n");
			exit(1);
		}
		ll = cc = 0;
		printf("%5d  ", cx);
		while ( (!feof(infile)) // added & modified by alex 01-02-09
			    && ((ch = getc(infile)) != '\n'))
		{
			printf("%c", ch);
			line[++ll] = ch;
		} // while
		printf("\n");
		line[++ll] = ' ';
	}
	ch = line[++cc];
} // getch

//////////////////////////////////////////////////////////////////////
// gets a symbol from input stream.
void getsym(void)
{
	int i, j, k;
	char a[MAXIDLEN + 1];
L:
	while (ch == ' ') {
		//printf("eatup space");
		getch();
	}

	if (isalpha(ch))
	{ // symbol is a reserved word or an identifier.
		k = 0;
		do
		{
			if (k < MAXIDLEN)
				a[k++] = ch;
			getch();
		}
		while (isalpha(ch) || isdigit(ch));
		a[k] = 0;
		strcpy(id, a);
		//optimization: using bsearch to judge 'id' is a reserved word or not  
		i = 1;
		j = NRW;
		do {
			k = (i + j) / 2;
			if (strcmp(id, word[k]) <= 0) {
				j = k - 1;
			}
			if (strcmp(id, word[k]) >= 0) {
				i = k + 1;
			}
		}while (i <= j);
		if (i - 1 > j) {
			sym = wsym[k];// symbol is a reserved word
		}else {
			sym = SYM_IDENTIFIER;// symbol is an identifier
		}
	}
	else if (isdigit(ch))
	{ // symbol is a number.
		k = num = 0;
		sym = SYM_NUMBER;
		do
		{
			num = num * 10 + ch - '0';
			k++;
			getch();
		}
		while (isdigit(ch));
		if (k > MAXNUMLEN)
			error(25);     // The number is too great.
	}
	else if (ch == ':')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_BECOMES; // :=
			getch();
		}
		else
		{
			sym = SYM_NULL;       // illegal?
		}
	}
	else if (ch == '>')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_GEQ;     // >=
			getch();
		}
		else
		{
			sym = SYM_GTR;     // >
		}
	}
	else if (ch == '<')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_LEQ;     // <=
			getch();
		}
		else if (ch == '>')
		{
			sym = SYM_NEQ;     // <>
			getch();
		}
		else
		{
			sym = SYM_LES;     // <
		}
	}
	else if (ch == '/') {      // to handle the notes beginning with "/*"
		getch();
		if (ch == '*') {
		L1:
			do {
				getch();
			} while (ch != '*');
		L2:
			getch();
			if (ch == '/') {
				getch();
				goto L;
			} else if (ch == '*') {
				goto L2;
			} else {
				goto L1;
			}
		} 
		else if (ch == '/') {    // to handle the notes beginning with "//"
			cc = ll;
			getch();
			goto L;
		}
		else {
			error(0);
		}
	}
	else
	{ // other tokens
		i = NSYM;
		csym[0] = ch;
		while (csym[i--] != ch);
		//printf("%d\n",i);
		if (++i)
		{
			//printf("%d\n",i);
			sym = ssym[i];
			getch();
		}
		else
		{
			printf("Fatal Error: Unknown character.\n");
			exit(1);
		}
	}
} // getsym

//////////////////////////////////////////////////////////////////////
// generates (assembles) an instruction.
void gen(int x, int y, int z)
{
	if (cx > CXMAX)
	{
		printf("Fatal Error: Program too long.\n");
		exit(1);
	}
	code[cx].f = x;
	code[cx].l = y;
	code[cx++].a = z;
} // gen

//////////////////////////////////////////////////////////////////////
// tests if error occurs and skips all symbols that do not belongs to s1 or s2.
void test(symset s1, symset s2, int n)
{
	symset s;

	if (! inset(sym,s1))
	{
		error(n);
		s = uniteset(s1, s2);
		while(! inset(sym, s))
			getsym();
		destroyset(s);
	}
} // test

//////////////////////////////////////////////////////////////////////
int dx;  // data allocation index

// enter object(constant, variable or procedre) into table.
void enter(int kind)
{
	mask* mk;

	tx++;
	strcpy(table[tx].name, id);
	table[tx].kind = kind;
	switch (kind)
	{
	case ID_CONSTANT:
		if (num > MAXADDRESS)
		{
			error(25); // The number is too great.
			num = 0;
		}
		table[tx].value = num;
		break;
	case ID_VARIABLE:
		mk = (mask*) &table[tx];
		mk->level = level;
		mk->address = dx++;
		break;
	case ID_PROCEDURE:
		mk = (mask*) &table[tx];
		mk->level = level;
		break;
	} // switch
} // enter

//////////////////////////////////////////////////////////////////////
// locates identifier in symbol table.
int position(char* id)
{
	int i;
	strcpy(table[0].name, id);
	i = tx + 1;
	while (strcmp(table[--i].name, id) != 0);
	return i;
} // position

//////////////////////////////////////////////////////////////////////
void constdeclaration(void)
{
	if (sym == SYM_IDENTIFIER)
	{
		getsym();
		if (sym == SYM_EQU || sym == SYM_BECOMES)
		{
			if (sym == SYM_BECOMES)
				error(1); // Found ':=' when expecting '='.
			getsym();
			if (sym == SYM_NUMBER)
			{
				enter(ID_CONSTANT);
				getsym();
			}
			else
			{
				error(2); // There must be a number to follow '='.
			}
		}
		else
		{
			error(3); // There must be an '=' to follow the identifier.
		}
	} else	error(4);
	 // There must be an identifier to follow 'const', 'var', or 'procedure'.
} // constdeclaration

//////////////////////////////////////////////////////////////////////
void vardeclaration(void)
{
	if (sym == SYM_IDENTIFIER)
	{
		enter(ID_VARIABLE);
		getsym();
	}
	else
	{
		error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
	}
} // vardeclaration

//////////////////////////////////////////////////////////////////////
void listcode(int from, int to)
{
	int i;
	
	printf("\n");
	for (i = from; i < to; i++)
	{
		printf("%5d %s\t%d\t%d\n", i, mnemonic[code[i].f], code[i].l, code[i].a);
	}
	printf("\n");
} // listcode

//////////////////////////////////////////////////////////////////////
void factor(symset fsys)
{
	void expression(symset fsys);
	int i;
	symset set;
	
	test(facbegsys, fsys, 24); // The symbol can not be as the beginning of an expression.

	while (inset(sym, facbegsys))
	{
		if (sym == SYM_IDENTIFIER)
		{
			if ((i = position(id)) == 0)
			{
				error(11); // Undeclared identifier.
			}
			else
			{
				switch (table[i].kind)
				{
					mask* mk;
				case ID_CONSTANT:
					gen(LIT, 0, table[i].value);
					break;
				case ID_VARIABLE:
					//printf("this is a variable");
					mk = (mask*) &table[i];
					gen(LOD, level - mk->level, mk->address);
					break;
				case ID_PROCEDURE:
					error(21); // Procedure identifier can not be in an expression.
					break;
				} // switch
			}
			getsym();
		}
		else if (sym == SYM_NUMBER)
		{
			if (num > MAXADDRESS)
			{
				error(25); // The number is too great.
				num = 0;
			}
			gen(LIT, 0, num);
			getsym();
		}
		else if (sym == SYM_LPAREN)
		{
			getsym();
			set = uniteset(createset(SYM_RPAREN, SYM_NULL), fsys);
			expression(set);
			destroyset(set);
			if (sym == SYM_RPAREN)
			{
				getsym();
			}
			else
			{
				error(22); // Missing ')'.
			}
		}
		test(fsys, createset(SYM_LPAREN,SYM_NULL), 23);
	} // while
} // factor

//////////////////////////////////////////////////////////////////////
void term(symset fsys)
{
	int mulop;
	symset set;
	
	set = uniteset(fsys, createset(SYM_TIMES, SYM_SLASH, SYM_NULL));
	factor(set);
	while (sym == SYM_TIMES || sym == SYM_SLASH)
	{
		mulop = sym;
		getsym();
		factor(set);
		if (mulop == SYM_TIMES)
		{
			gen(OPR, 0, OPR_MUL);
		}
		else
		{
			gen(OPR, 0, OPR_DIV);
		}
	} // while
	destroyset(set);
} // term

//////////////////////////////////////////////////////////////////////
void expression(symset fsys)
{
	int addop;
	symset set;

	set = uniteset(fsys, createset(SYM_PLUS, SYM_MINUS, SYM_NULL));
	if (sym == SYM_PLUS || sym == SYM_MINUS)
	{
		addop = sym;
		getsym();
		term(set);
		if (addop == SYM_MINUS)
		{
			gen(OPR, 0, OPR_NEG);
		}
	}
	else
	{
		term(set);
	}

	while (sym == SYM_PLUS || sym == SYM_MINUS)
	{
		addop = sym;
		getsym();
		term(set);
		if (addop == SYM_PLUS)
		{
			gen(OPR, 0, OPR_ADD);
		}
		else
		{
			gen(OPR, 0, OPR_MIN);
		}
	} // while

	destroyset(set);
} // expression

//////////////////////////////////////////////////////////////////////
void actual_parameters_line(symset fsys, mask const *prcd)
{
    symset set, set1;
	assert(prcd != NULL);
	while (1) {
        set1 = createset(SYM_COMMA, SYM_NULL);
        set = uniteset(fsys, set1);
		expression(set);
		if (prcd->para_link == NULL) {
			error(26);
		}
		else {
			prcd = prcd->para_link;
			gen(OPR, 0, OPR_CPY);
		}
		if (sym == SYM_COMMA) {
			getsym();
		}
		else {
			if (prcd->para_link != NULL) {
				error(27);
			}
			break;
		}
	}

}// actual parameters line

//////////////////////////////////////////////////////////////////////
void conditionFactor(symset fsys) {
    void condition(symset fsys);
    symset set = uniteset(fsys,createset(SYM_RPAREN, SYM_NOT));

    if (sym == SYM_LPAREN) {
        getsym();
        condition(set);
        if (sym == SYM_RPAREN) {
            getsym();
        } else {
            error(22);
        }
    } else {
        expression(set);
    }
}


//////////////////////////////////////////////////////////////////////
void conditionTerm(symset fsys) {
    int relop;
    symset set;

    if (sym == SYM_ODD) {
        getsym();
        expression(fsys);
        gen(OPR, 0, 6);
    }
    else {
        set = uniteset(relset, fsys);
        conditionFactor(set);
        destroyset(set);
        if (!inset(sym, relset)) {
            return;
        } else {
            relop = sym;
            getsym();
            conditionFactor(fsys);
            switch (relop) {
                case SYM_EQU:
                    gen(OPR, 0, OPR_EQU);
                    break;
                case SYM_NEQ:
                    gen(OPR, 0, OPR_NEQ);
                    break;
                case SYM_LES:
                    gen(OPR, 0, OPR_LES);
                    break;
                case SYM_GEQ:
                    gen(OPR, 0, OPR_GEQ);
                    break;
                case SYM_GTR:
                    gen(OPR, 0, OPR_GTR);
                    break;
                case SYM_LEQ:
                    gen(OPR, 0, OPR_LEQ);
                    break;
            } // switch
        } // else
    } // else
}

//////////////////////////////////////////////////////////////////////
void condition(symset fsys) {

	int conditionOp;
	symset set = uniteset(fsys, logicSet);
    int ccx = 0;

	if (sym == SYM_NOT) {
		getsym();
		conditionTerm(set);
		gen(OPR, 0, OPR_OPP);
	} else {
		conditionTerm(set);
	}
    if (sym == SYM_AND) {
        scx[ccx++] = cx;
        gen(JPF, 0, 0);
    } else {
        scx[ccx++] = cx;
        gen(JPT, 0, 0);
    }
	while (sym == SYM_AND || sym == SYM_OR) {
		conditionOp = sym;
		getsym();
		conditionTerm(set);
		if (conditionOp == SYM_AND) {
            scx[ccx++] = cx;
			gen(JPF, 0, 0);
		} else {
            scx[ccx++] = cx;
			gen(JPT, 0, 0);
		}
	}
	destroyset(set);
}

//////////////////////////////////////////////////////////////////////
void statement(symset fsys)
{
	int i, cx1, cx2;
	symset set1, set;

	if (sym == SYM_IDENTIFIER)
	{ // variable assignment
		mask* mk;
		if (! (i = position(id)))
		{
			error(11); // Undeclared identifier.
		}
		else if (table[i].kind != ID_VARIABLE)
		{
			error(12); // Illegal assignment.
			i = 0;
		}
		getsym();
		if (sym == SYM_BECOMES)
		{
			getsym();
		}
		else
		{
			error(13); // ':=' expected.
		}
		expression(fsys);
		mk = (mask*) &table[i];
		if (i)
		{
			gen(STO, level - mk->level, mk->address);
		}
	}
	else if (sym == SYM_CALL)
	{ // procedure call
		getsym();
		if (sym != SYM_IDENTIFIER)
		{
			error(14); // There must be an identifier to follow the 'call'.
		}
		else
		{
			if (! (i = position(id)))
			{
				error(11); // Undeclared identifier.
			}
			else if (table[i].kind == ID_PROCEDURE)
			{
				getsym();
				mask* mk;
				mk = (mask*) &table[i];
				if (sym == SYM_LPAREN) {
					getsym();
                    set1 = createset(SYM_RPAREN, SYM_NULL);
					set = uniteset(fsys, set1);
					actual_parameters_line(set, mk);
					gen(REVA, 0, mk->para_num);
					gen(CAL, level - mk->level, mk->address);
					gen(POPA, 0, mk->para_num);
					if (sym == SYM_RPAREN) {
						getsym();
					}
					else {
						error(22);
					}
				}
				else {
					gen(CAL, level - mk->level, mk->address);
				}
			}
			else
			{
				error(15); // A constant or variable can not be called. 
			}
			getsym();
		}
	} 
	else if (sym == SYM_IF)
	{ // if statement
		getsym();
		set1 = createset(SYM_THEN, SYM_DO, SYM_NULL);
		set = uniteset(set1, fsys);
		condition(set);
		destroyset(set1);
		destroyset(set);
		if (sym == SYM_THEN)
		{
			getsym();
		}
		else
		{
			error(16); // 'then' expected.
		}
		cx1 = cx;
		gen(JPC, 0, 0);
        for (int j = 0; j < 100; ++j) {
            if (scx[j] != 0) {
                code[scx[j]].a = cx;
            } else {
                break;
            }
        }
		statement(fsys);
		code[cx1].a = cx;
	}
	else if (sym == SYM_BEGIN)
	{ // block
		getsym();
		set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
		set = uniteset(set1, fsys);
		statement(set);
		while (sym == SYM_SEMICOLON || inset(sym, statbegsys))
		{
			if (sym == SYM_SEMICOLON)
			{
				getsym();
			}
			else
			{
				error(10);
			}
			statement(set);
		} // while
		destroyset(set1);
		destroyset(set);
		if (sym == SYM_END)
		{
			getsym();
		}
		else
		{
			error(17); // ';' or 'end' expected.
		}
	}
	else if (sym == SYM_WHILE)
	{ // while statement
		cx1 = cx;
		getsym();
		set1 = createset(SYM_DO, SYM_NULL);
		set = uniteset(set1, fsys);
		condition(set);
		destroyset(set1);
		destroyset(set);
		cx2 = cx;
		gen(JPC, 0, 0);
		if (sym == SYM_DO)
		{
			getsym();
		}
		else
		{
			error(18); // 'do' expected.
		}
		statement(fsys);
		gen(JMP, 0, cx1);
		code[cx2].a = cx;
	}
	test(fsys, phi, 19);
} // statement

//////////////////////////////////////////////////////////////////////
void formal_parameter_line() 
{
	mask *prcd = &table[tx];
	mask *const ppro = prcd;
	ppro->para_num = 0;
	assert(prcd->para_link == NULL);

	while (1) {
        if (sym == SYM_VAR) {
            getsym();
            vardeclaration();
        }
        else error(29);
		/*if (sym == SYM_COLON) {
			getsym();
		}
		else {
			error(28);
		}*/
		++(ppro->para_num);
		table[tx].address = -(ppro->para_num);
		prcd->para_link = (mask*)malloc(sizeof(mask));
		if (prcd->para_link == NULL) {
			printf("STACK OVERFLOW");
			exit(1);
		}
		*(prcd->para_link) = table[tx];
		prcd = prcd->para_link;
		assert(prcd->para_link == NULL);
		prcd->para_link == NULL;
		if (sym == SYM_SEMICOLON) {
			getsym();
		}
		else {
			break;
		}
	}
} // formal_parameters_line

//////////////////////////////////////////////////////////////////////
void block(symset fsys, int tx0);
void procedure_declare(symset fsys)
{
	int savedTx = 0;
    symset  set, set1;
	assert(sym == SYM_PROCEDURE);
	getsym();
	if (sym == SYM_IDENTIFIER) {
		enter(ID_PROCEDURE);
		getsym();
	}
	else {
		error(4);
	}
	++level;
	savedTx = tx;
	table[tx].address = cx;
	if (sym == SYM_LPAREN) {
		getsym();
		formal_parameter_line();   //this will change tx
		if (sym == SYM_RPAREN) {
			getsym();
		}
		else {
			error(22);
		}
	}
	/*if (sym = SYM_COLON) {
		getsym();
	}
	else {
		error(28);
	}*/
	//assert(table[savedTx].kind == SYM_PROCEDURE);
	//getsym();
	if (sym == SYM_SEMICOLON) {
		getsym();
	}
	else {
		error(17);
	}
    set = createset(SYM_SEMICOLON, SYM_NULL);
	block(uniteset(set, fsys), savedTx);
	free_para_link(table + savedTx + 1, table + tx + 1);
	tx = savedTx;
	--level;
	if (sym == SYM_SEMICOLON) {
		getsym();
        set = createset(SYM_IDENTIFIER, SYM_PROCEDURE, SYM_NULL);
        set1 = uniteset(statbegsys, set);
		test(set1, fsys, 6);
	}
	else {
		error(5);
	}
} // procedure declare

//////////////////////////////////////////////////////////////////////
void block(symset fsys, int tx0)
{
	int cx0; // initial code index
	mask* mk;
	int block_dx;
	//int savedTx;
	symset set1, set;

	dx = 3;
	block_dx = dx;
	mk = (mask*) &table[tx0];
	mk->address = cx;
	gen(JMP, 0, 0);
	if (level > MAXLEVEL)
	{
		error(32); // There are too many levels.
	}
	do
	{
		if (sym == SYM_CONST)
		{ // constant declarations
			getsym();
			do
			{
				constdeclaration();
				while (sym == SYM_COMMA)
				{
					getsym();
					constdeclaration();
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if

		if (sym == SYM_VAR)
		{ // variable declarations
			getsym();
			do
			{
				vardeclaration();
				while (sym == SYM_COMMA)
				{
					getsym();
					vardeclaration();
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
//			block = dx;
		} // if

		while (sym == SYM_PROCEDURE)
		{ // procedure declarations
			procedure_declare(fsys);
			/*getsym();
			if (sym == SYM_IDENTIFIER)
			{
				enter(ID_PROCEDURE);
				getsym();
			}
			else
			{
				error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
			}


			if (sym == SYM_SEMICOLON)
			{
				getsym();
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}

			level++;
			savedTx = tx;
			set1 = createset(SYM_SEMICOLON, SYM_NULL);
			set = uniteset(set1, fsys);
			block(set, tx);
			destroyset(set1);
			destroyset(set);
			tx = savedTx;
			level--;

			if (sym == SYM_SEMICOLON)
			{
				getsym();
				set1 = createset(SYM_IDENTIFIER, SYM_PROCEDURE, SYM_NULL);
				set = uniteset(statbegsys, set1);
				test(set, fsys, 6);
				destroyset(set1);
				destroyset(set);
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}*/
		} // while
		set1 = createset(SYM_IDENTIFIER, SYM_NULL);
		set = uniteset(statbegsys, set1);
		test(set, declbegsys, 7);
		destroyset(set1);
		destroyset(set);
	}
	while (inset(sym, declbegsys));

	code[mk->address].a = cx;
	mk->address = cx;
	cx0 = cx;
	gen(INT, 0, block_dx);
	set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
	set = uniteset(set1, fsys);
	statement(set);
	destroyset(set1);
	destroyset(set);
	gen(OPR, 0, OPR_RET); // return
	test(fsys, phi, 8); // test for error: Follow the statement is an incorrect symbol.
	listcode(cx0, cx);
} // block

//////////////////////////////////////////////////////////////////////
int base(int stack[], int currentLevel, int levelDiff)
{
	int b = currentLevel;
	
	while (levelDiff--)
		b = stack[b];
	return b;
} // base

//////////////////////////////////////////////////////////////////////
// interprets and executes codes.
void interpret()
{
	int pc;        // program counter
	int stack[STACKSIZE];
	int top;       // top of stack
	int b;         // program, base, and top-stack register
	instruction i; // instruction register
	int first = 0;
	int last = 0;
    int tmp;
	printf("Begin executing PL/0 program.\n");

	pc = 0;
	b = 1;
	top = 3;
	stack[1] = stack[2] = stack[3] = 0;
	do
	{
		i = code[pc++];
		switch (i.f)
		{
		case LIT:
			stack[++top] = i.a;
			break;
		case OPR:
			switch (i.a) // operator
			{
			case OPR_RET:
				top = b - 1;
				pc = stack[top + 3];
				b = stack[top + 2];
				break;
			case OPR_NEG:
				stack[top] = -stack[top];
				break;
			case OPR_ADD:
				top--;
				stack[top] += stack[top + 1];
				break;
			case OPR_MIN:
				top--;
				stack[top] -= stack[top + 1];
				break;
			case OPR_MUL:
				top--;
				stack[top] *= stack[top + 1];
				break;
			case OPR_DIV:
				top--;
				if (stack[top + 1] == 0)
				{
					fprintf(stderr, "Runtime Error: Divided by zero.\n");
					fprintf(stderr, "Program terminated.\n");
					continue;
				}
				stack[top] /= stack[top + 1];
				break;
			case OPR_ODD:
				stack[top] %= 2;
				break;
			case OPR_EQU:
				top--;
				stack[top] = stack[top] == stack[top + 1];
				break;
			case OPR_NEQ:
				top--;
				stack[top] = stack[top] != stack[top + 1];
			case OPR_LES:
				top--;
				stack[top] = stack[top] < stack[top + 1];
				break;
			case OPR_GEQ:
				top--;
				stack[top] = stack[top] >= stack[top + 1];
			case OPR_GTR:
				top--;
				stack[top] = stack[top] > stack[top + 1];
				break;
			case OPR_LEQ:
				top--;
				stack[top] = stack[top] <= stack[top + 1];
                break;
            case OPR_CPY:
                tmp = stack[top];
                memcpy(&stack[top], &tmp, sizeof(int));
                break;
            case OPR_OPP:
                stack[top] = !stack[top];
                break;
			} // switch
			break;
		case LOD:
			stack[++top] = stack[base(stack, b, i.l) + i.a];
			break;
		case STO:
			stack[base(stack, b, i.l) + i.a] = stack[top];
			printf("%d\n", stack[top]);
			top--;
			break;
		case CAL:
			stack[top + 1] = base(stack, b, i.l);
			// generate new block mark
			stack[top + 2] = b;
			stack[top + 3] = pc;
			b = top + 1;
			pc = i.a;
			break;
		case INT:
			top += i.a;
			break;
		case JMP:
			pc = i.a;
			break;
		case JPC:
			if (stack[top] == 0)
				pc = i.a;
			top--;
			break;
        case JPF:
            if (stack[top] == 0)
                pc = i.a;
            break;
        case JPT:
            if (stack[top] != 0)
                pc = i.a;
            break;
		case POPA:
			top -= i.a;
			break;
	    case REVA:
			first = top - i.a + 1;
			last = top + 1;
			if (last - first >= 2) {
				for (; first < (last--); ++first) {
					int temp = stack[first];
					stack[first] = stack[last];
					stack[last] = temp;
				}
			}
			break;
		} // switch
	}
	while (pc);

	printf("End executing PL/0 program.\n");
} // interpret

//////////////////////////////////////////////////////////////////////
void main ()
{
	FILE* hbin;
	char s[80];
	int i;
	symset set, set1, set2;

	printf("Please input source file name: "); // get file name to be compiled
	scanf("%s", s);
	if ((infile = fopen(s, "r")) == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}

	phi = createset(SYM_NULL);
	relset = createset(SYM_EQU, SYM_NEQ, SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ, SYM_NULL);
    logicSet = createset(SYM_AND, SYM_OR);

    // create begin symbol sets
	declbegsys = createset(SYM_CONST, SYM_VAR, SYM_PROCEDURE, SYM_NULL);
	statbegsys = createset(SYM_BEGIN, SYM_CALL, SYM_IF, SYM_WHILE, SYM_NULL);
	facbegsys = createset(SYM_IDENTIFIER, SYM_NUMBER, SYM_LPAREN, SYM_NULL);

	err = cc = cx = ll = 0; // initialize global variables
	ch = ' ';
	kk = MAXIDLEN;

	getsym();

	set1 = createset(SYM_PERIOD, SYM_NULL);
	set2 = uniteset(declbegsys, statbegsys);
	set = uniteset(set1, set2);
	block(set, tx);
	destroyset(set1);
	destroyset(set2);
	destroyset(set);
	destroyset(phi);
	destroyset(relset);
	destroyset(declbegsys);
	destroyset(statbegsys);
	destroyset(facbegsys);

	if (sym != SYM_PERIOD)
		error(9); // '.' expected.
	if (err == 0)
	{
		hbin = fopen("hbin.txt", "w");
		for (i = 0; i < cx; i++)
			fwrite(&code[i], sizeof(instruction), 1, hbin);
		fclose(hbin);
	}
	if (err == 0)
		interpret();
	else
		printf("There are %d error(s) in PL/0 program.\n", err);
	listcode(0, cx);
} // main

//////////////////////////////////////////////////////////////////////
// eof pl0.c
