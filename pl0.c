// pl0 compiler source code

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <stdbool.h>
#include <printf.h>

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
		}
		else
		{
			if(ch == '[')
			{
				sym = SYM_ARRAY;
			}
			else {
				sym = SYM_IDENTIFIER;// symbol is an identifier
			}
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
	else if(ch == ']')
	{
		getch();
		sym = SYM_RMATCH;
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
            do {
                getch();
            } while (ch != '*');
            while (1) {
                getch();
                if (ch == '/') {
                    getch();
                    getsym();
                    break;
                } else {
                    do {
                        getch();
                    } while (ch != '*');
                }
            }
        } else if (ch == '/') {    // to handle the notes beginning with "//"
                cc = ll;
                getch();
                getsym();
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
bool isArray = false;

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

void enter_array()
{
	int i;
	ax++;
	table_arr[ax] = array_temp;
	strcpy(table_arr[ax].name, id);
	enter(ID_VARIABLE);
	table_arr[ax].first_adr = tx;
	for(i = table_arr[ax].sum -1 ; i >0; i--)
		enter(ID_VARIABLE);
}
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

int array_position()
{
	int i = 0;
	while(strcmp(table_arr[++i].name, id));
	if(i <= ax)
		return i;
	else
		return 0;
}

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
	int i,wide = 0;
	if (sym == SYM_IDENTIFIER)
	{
		enter(ID_VARIABLE);
        isArray = false;
		getsym();
	}
	else if(sym == SYM_ARRAY)
	{
		while(ch == '[')
		{
			wide++;
			getch();
			getsym();
			array_temp.dim[wide-1] = num;
			getsym();
		}
		array_temp.n_dim = wide;
		array_temp.size[wide-1] = 1;
		for(i = wide-1; i >0; i--)
			array_temp.size[i-1] = array_temp.size[i] * array_temp.dim[i];
		array_temp.sum = array_temp.size[0] * array_temp.dim[0];
		enter_array();
        isArray = true;
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
	int i,j;
	int wide = 0;
	symset set;
	mask* mk;
	
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
		else if(sym == SYM_ARRAY)
		{
			if(!(i = array_position()))
				error(11);
			else
			{
				j = table_arr[i].first_adr;
				mk = (mask*) &table[j];
				gen(LIT, 0, 0);
				while(ch == '[')
				{
					wide++;
					getch();
					getsym();
					expression(fsys);
					gen(LIT, 0, table_arr[i].size[wide-1]);
					gen(OPR, 0, OPR_MUL);
					gen(OPR, 0, OPR_ADD);
				}
				gen(LODA, level - mk->level, mk->address);
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
    mask* mk;
	assert(prcd != NULL);
	while (1) {
        set1 = createset(SYM_COMMA, SYM_NULL);
        set = uniteset(fsys, set1);
        if ((*(prcd->para_link)).kind != ID_ARRAY)
		    expression(set);
        else {
            int i;
            if(!(i = array_position()))
                error(11);
            else
                for (int j = table_arr[i].first_adr + table_arr[i].sum - 1; j >= table_arr[i].first_adr; j--) {
                    mk = (mask*) &table[j];
                    gen(LOD, mk->level, mk->address);
                }
            getsym();
        }
		if (prcd->para_link == NULL) {
			error(26);
		}
		else {
			prcd = prcd->para_link;
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

} // actual parameters line

//////////////////////////////////////////////////////////////////////
void conditionFactor(symset fsys,int * start,int * end, bool * inParen)
{
    void condition(symset fsys,int * start,int * end, bool * inParen);
    symset set = uniteset(fsys,createset(SYM_RPAREN, SYM_NOT));

    if (sym == SYM_LPAREN) {
        getsym();
        *inParen = true;
        condition(set,start,end,inParen);
        if (sym == SYM_RPAREN) {
            *inParen = false;
            getsym();
        } else {
            error(22);
        }
    } else {
        expression(set);
    }
}

//////////////////////////////////////////////////////////////////////
void conditionTerm(symset fsys,int * start,int * end,bool * inParen)
{
    int relop;
    symset set;

    if (sym == SYM_ODD) {
        getsym();
        expression(fsys);
        gen(OPR, 0, 6);
    }
    else {
        set = uniteset(relset, fsys);
        conditionFactor(set, start, end, inParen);
        destroyset(set);
        if (*inParen) {
            if (sym == SYM_OR || sym == SYM_AND) {
                return;
            } else if (!inset(sym, relset)) {
                return;
            } else {
                relop = sym;
                getsym();
                conditionFactor(fsys,start,end,inParen);
                switch (relop) {
                    case SYM_EQU:
                        gen(OPR, 0, OPR_LES);
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
        } else {
            if (!inset(sym, relset)) {
                gen(LIT, 0, 0);
                gen(JNE, 0, 0);
                return;
            } else {
                relop = sym;
                getsym();
                conditionFactor(fsys,start,end,inParen);
                switch (relop) {
                    case SYM_EQU:
                        gen(JEQ, 0, 0);
                        break;
                    case SYM_NEQ:
                        gen(JNE, 0, 0);
                        break;
                    case SYM_LES:
                        gen(JL, 0, 0);
                        break;
                    case SYM_GEQ:
                        gen(JGE, 0, 0);
                        break;
                    case SYM_GTR:
                        gen(JG, 0, 0);
                        break;
                    case SYM_LEQ:
                        gen(JLE, 0, 0);
                        break;
                } // switch
            } // else
        }

//        if (sym == SYM_OR || sym == SYM_AND) {
//            return;
//        } else if (!inset(sym, relset)) {
//            gen(LIT, 0, 0);
//            gen(JNE, 0, 0);
//            return;
//        } else {
//            relop = sym;
//            getsym();
//            conditionFactor(fsys,start,end,hasParen);
//            switch (relop) {
//                case SYM_EQU:
//                    gen(JEQ, 0, 0);
//                    break;
//                case SYM_NEQ:
//                    gen(JNE, 0, 0);
//                    break;
//                case SYM_LES:
//                    gen(JL, 0, 0);
//                    break;
//                case SYM_GEQ:
//                    gen(JGE, 0, 0);
//                    break;
//                case SYM_GTR:
//                    gen(JG, 0, 0);
//                    break;
//                case SYM_LEQ:
//                    gen(JLE, 0, 0);
//                    break;
//            } // switch
//        } // else
    } // else
}

//////////////////////////////////////////////////////////////////////
void condition(symset fsys,int * start,int * end,bool * inParen)
{

	int conditionOp;
	symset set = uniteset(fsys, logicSet);

	if (sym == SYM_NOT) {
		getsym();
		conditionTerm(set,start,end,inParen);
        switch (code[cx-1].f) {
            case JEQ:
                code[cx-1].f = JNE;
                break;
            case JNE:
                code[cx-1].f = JEQ;
                break;
            case JL:
                code[cx-1].f = JGE;
                break;
            case JLE:
                code[cx-1].f = JG;
                break;
            case JG:
                code[cx-1].f = JLE;
                break;
            case JGE:
                code[cx-1].f = JL;
                break;
            default:
                break;
        }
        scx[*end] = cx-1;
        andOr[(*end)++] = 3;
        ccx++;
	} else {
		conditionTerm(set,start,end,inParen);
	}
    if (sym == SYM_OR) {
        if (!(*inParen)) {
            scx[*end] = cx-1;
            andOr[(*end)++] = 2;
            ccx++;
        }
    } else {
        if (!(*inParen)) {
            switch (code[cx-1].f) {
                case JEQ:
                    code[cx-1].f = JNE;
                    break;
                case JNE:
                    code[cx-1].f = JEQ;
                    break;
                case JL:
                    code[cx-1].f = JGE;
                    break;
                case JLE:
                    code[cx-1].f = JG;
                    break;
                case JG:
                    code[cx-1].f = JLE;
                    break;
                case JGE:
                    code[cx-1].f = JL;
                    break;
                default:
                    break;
            }
            scx[*end] = cx-1;
            andOr[(*end)++] = 3;
            ccx++;
        }
    }
//	else{
//        andOr[*end] = 2;
//        scx[(*end)++] = cx-1;
//        ccx++;
//		destroyset(set);
//        return;
//	}
	while (sym == SYM_AND || sym == SYM_OR) {

        if (*inParen) {
            conditionOp = sym;
            getsym();
            conditionTerm(set,start,end,inParen);
            if (conditionOp != SYM_OR) {
                gen(OPR,0,OPR_AND);
            } else {
                gen(OPR,0,OPR_OR);
            }
        } else {
            conditionOp = sym;
            getsym();
            conditionTerm(set,start,end,inParen);
            if (conditionOp != SYM_OR) {
                switch (code[cx-1].f) {
                    case JEQ:
                        code[cx-1].f = JNE;
                        break;
                    case JNE:
                        code[cx-1].f = JEQ;
                        break;
                    case JL:
                        code[cx-1].f = JGE;
                        break;
                    case JLE:
                        code[cx-1].f = JG;
                        break;
                    case JG:
                        code[cx-1].f = JLE;
                        break;
                    case JGE:
                        code[cx-1].f = JL;
                        break;
                }
                scx[*end] = cx-1;
                andOr[(*end)++] = 3;
                ccx++;
            } else {
                scx[*end] = cx-1;
                andOr[(*end)++] = 2;
                ccx++;
            }
        }
	}
    if (conditionOp == SYM_OR && !(*inParen)) {
        gen(JMP,0,0);
        scx[*end] = cx-1;
        andOr[(*end)++] = 2;
        ccx++;
    }
	destroyset(set);
}

//////////////////////////////////////////////////////////////////////
void statement(symset fsys)
{
	int cx1, cx2;
	int i,j;
	int wide = 0;
	symset set1, set;
	mask* mk;

	if (sym == SYM_IDENTIFIER)
	{ // variable assignment

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
	else if(sym == SYM_ARRAY)
	{
		if(!(i = array_position()))
			error(11);
		else {
			j = table_arr[i].first_adr;
			mk = (mask *) &table[j];
			gen(LIT, 0, 0);
			while (ch == '[') {
				wide++;
				getch();
				getsym();
				expression(fsys);
				gen(LIT, 0, table_arr[i].size[wide - 1]);
				gen(OPR, 0, OPR_MUL);
				gen(OPR, 0, OPR_ADD);
			}
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
		if (i)
		{
			gen(STOA, level - mk->level, mk->address);
		}

	}
	else if(sym == SYM_WRITE)
	{
		while(sym != SYM_SEMICOLON)
		{
			getsym();
			if(sym == SYM_IDENTIFIER)
			{
				if(!(i = position(id)))
				{
					error(11);
				}
				else if(table[i].kind != ID_VARIABLE)
				{
					error(12);
					i = 0;
				}
				mk =(mask *) &table[i];
				if (i)
				{
					gen(WRITE, level - mk->level, mk->address);
				}
			}
			else if(sym == SYM_ARRAY) {
				wide = 0;
				if (!(i = array_position()))
					error(11);
				else {
					j = table_arr[i].first_adr;
					mk = (mask *) &table[j];
					gen(LIT, 0, 0);
					while (ch == '[') {
						wide++;
						getch();
						getsym();
						expression(fsys);
						gen(LIT, 0, table_arr[i].size[wide - 1]);
						gen(OPR, 0, OPR_MUL);
						gen(OPR, 0, OPR_ADD);
					}
					gen(WRITEA, level - mk->level, mk->address);
				}
			}
			getsym();
		}
	}
	else if(sym == SYM_READ)
	{
		while(sym != SYM_SEMICOLON)
		{
			getsym();
			if(sym == SYM_IDENTIFIER)
			{
				if (! (i = position(id)))
				{
					error(11); // Undeclared identifier.
				}
				else if (table[i].kind != ID_VARIABLE)
				{
					error(12); // Illegal assignment.
					i = 0;
				}
				mk =(mask *) &table[i];
				if (i)
				{
					gen(READ, level - mk->level, mk->address);
				}
			}
			else if(sym == SYM_ARRAY)
			{
				wide = 0;
				if (!(i = array_position()))
					error(11);
				else {
					j = table_arr[i].first_adr;
					mk = (mask *) &table[j];
					gen(LIT, 0, 0);
					while (ch == '[') {
						wide++;
						getch();
						getsym();
						expression(fsys);
						gen(LIT, 0, table_arr[i].size[wide - 1]);
						gen(OPR, 0, OPR_MUL);
						gen(OPR, 0, OPR_ADD);
					}
					gen(READA, level - mk->level, mk->address);
				}
			}
			getsym();
		}
	}
	else if(sym == SYM_CALL)
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
			else {
                error(15); // A constant or variable can not be called.
                getsym();
            }
		}
	} 
	else if (sym == SYM_IF)
	{ // if statement
		int sym1,cc1,cx3,cx4;//for else
        int start = ccx;
        int end = ccx;
        bool inParen = false;
        getsym();
        set1 = createset(SYM_THEN, SYM_ELSE,SYM_DO, SYM_NULL);
        set = uniteset(set1, fsys);
        condition(set,&start,&end,&inParen);
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
//        gen(JMP,0,0);
        cx2 = cx;
        statement(fsys);
//        code[cx2-1].a = cx;
		cx3=cx;
		gen(JMP,0,0);
        for (int m = start; m < end; ++m) {
            if (scx[m] != 0) {
                if (andOr[m] == 3) {
                    code[scx[m]].a = cx;
                } else {
                    if (m == end - 1) {
                        code[scx[m]].a = cx;
                    } else {
                        code[scx[m]].a = cx2;
                    }
                }
            } else {
                break;
            }
        }
		//////////////else
		getsym();
		if (sym==SYM_ELSE)
		{
			getsym();
			code[cx2].a=cx;
			statement(fsys);
			code[cx3].a=cx;

		}
		else
		{	
			code[cx3].a=cx;
			statement(fsys);
		}
	}
	else if (sym == SYM_BEGIN)
	{ // block
		int i;//for loop
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
		int cx3,i,cx4;
        int start = ccx;
        int end = ccx;
        bool inParen = false;
		loop_level++;
        cx1 = cx;
        getsym();
        set1 = createset(SYM_DO,SYM_BREAK,SYM_NULL);
        set = uniteset(set1, fsys);
        condition(set,&start,&end,&inParen);
        destroyset(set1);
        destroyset(set);
        cx3 = cx;
//        gen(JMP, 0, 0);
        if (sym == SYM_DO)
        {
            getsym();
        }
        else
        {
            error(18); // 'do' expected.
        }
        cx2 = cx;
        statement(fsys);
        gen(JMP, 0, cx1);
//        code[cx3].a = cx;
		////////////////////////for while
		i=0;
		while(break_point[loop_level][i]!=-1&&i<20)//most 20  break 
		{
			code[break_point[loop_level][i]].a=cx;
			break_point[loop_level][i]=-1;
			i++;
		}
		loop_level--;
		////////////////////////////////
//        code[cx3].a = cx;
        for (int m = start; m < end; ++m) {
            if (scx[m] != 0) {
                if (andOr[m] == 3) {
                    code[scx[m]].a = cx;
                } else {
                    if (m == end-1) {
                        code[scx[m]].a = cx;
                    } else {
                        code[scx[m]].a = cx2;
                    }
                }
            } else {
                break;
            }
        }
    }
	else if(sym==SYM_FOR)
	{
		int i,cx3,cx4;
        int start = ccx;
        int end = ccx;
        bool inParen = false;
		loop_level++;
		getsym();
		if(sym==SYM_LPAREN)
		{
			getsym();
		}
		statement(fsys);//initialize
		cx1=cx;//condition
		getsym();
		set1 = createset(SYM_BREAK,SYM_NULL,SYM_SEMICOLON);
        set = uniteset(set1, fsys);
        condition(set,&start,&end,&inParen);
        destroyset(set1);
        destroyset(set);
        cx2 = cx;//get out
        gen(JPC, 0, 0);
		cx3 = cx;//skip loop step
		gen(JMP,0,0);
		getsym();
		statement(fsys);
		getsym();//get ')'
		//printf("\n\n\n\n%d\n\n\n\n",sym);
		gen(JMP,0,cx1);
		code[cx3].a=cx;
		getsym();
		statement(fsys);
		gen(JMP,0,cx3+1);
		code[cx2].a=cx;
		//////////////for break
		i=0;
		while(break_point[loop_level][i]!=-1&&i<20)//most 20  break 
		{
			code[break_point[loop_level][i]].a=cx;
			break_point[loop_level][i]=-1;
			i++;
		}
		loop_level--;
		/////////////for break
		for (int j = 0; j < 100; ++j) {
            if (scx[j] != 0) {
                if (code[scx[j]].f == JPF) {
                    code[scx[j]].a = cx;
                } else {
                    code[scx[j]].a = cx3;
                }
            } else {
                break;
            }
        }
		loop_level--;


		
	}
	else if(sym==SYM_BREAK)
	{
		int i =0;
		cx1=cx;
		gen(JMP,0,0);
		while(break_point[loop_level][i]!=-1)
		{
			i++;
		}
		break_point[loop_level][i]=cx1;
		getsym();		//get ;
	}
	else if(sym==SYM_EXIT)
	{
		int i=0;
		cx1=cx;
		gen(JMP,0,0);
		while(exit_point[i]!=-1)
		{
			i++;
		}
		exit_point[i]=cx1;
		getsym();
	}
} // statement

///////////////////////////////////////////////////////////////////////
void control_initialize(void)
{
	int i,j;
	loop_level=0;
	for(i=0;i!=5;i++)
	{
		exit_point[i]=-1;
		for(j=0;j!=5;j++)
			break_point[i][j]=-1;
	}
} // control_initialize

//////////////////////////////////////////////////////////////////////
void formal_parameter_line() 
{
    int savedTx = tx;
    int savedTx1;
	mask *prcd = &table[tx];
	mask *const ppro = prcd;
	ppro->para_num = 0;
	assert(prcd->para_link == NULL);

	while (1) {
        if (sym == SYM_VAR) {
            getsym();
            savedTx1 = tx;
            vardeclaration();
        }
        else error(29);
		/*if (sym == SYM_COLON) {
			getsym();
		}
		else {
			error(28);
		}*/
        ppro->para_num = tx - savedTx;
		table[savedTx1+1].address = -(ppro->para_num);
        if (isArray) {
            table[tx].kind = ID_ARRAY;
            //table[savedTx1+1].address = -(ppro->para_num) + 1;
        }
		prcd->para_link = (mask*)malloc(sizeof(mask));
		if (prcd->para_link == NULL) {
			printf("STACK OVERFLOW");
			exit(1);
		}
		*(prcd->para_link) = table[tx];
		prcd = prcd->para_link;
		assert(prcd->para_link == NULL);
		prcd->para_link = NULL;
		if (sym == SYM_COMMA) {
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
	int cx0,cx1,i; // initial code index
	mask* mk;
	//int block_dx;
	//int savedTx;
	symset set1, set;

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
	gen(INT, 0, dx);
	set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
	set = uniteset(set1, fsys);
	statement(set);
	destroyset(set1);
	destroyset(set);
	cx1=cx;
	gen(OPR, 0, OPR_RET); // return
	/////////////////////for exit
	i=0;
	while(exit_point[i]!=-1)
	{
			exit_point[i]=cx1;
			i++;
	}
	//////////////////////
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
	int temp;
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
            case OPR_OPP:
                stack[top] = !stack[top];
                break;
            case OPR_AND:
                top--;
                stack[top] = stack[top] && stack[top + 1];
                break;
            case OPR_OR:
                top--;
                stack[top] = stack[top] || stack[top + 1];
                break;
			} // switch
			break;
		case LOD:
			stack[++top] = stack[base(stack, b, i.l) + i.a];
			break;
		case LODA:
			stack[top] = stack[base(stack, b, i.l) + i.a+ stack[top]] ;
			break;
		case STO:
			stack[base(stack, b, i.l) + i.a] = stack[top];
			printf("%d\n", stack[top]);
			top--;
			break;
		case STOA:
			stack[base(stack, b, i.l) + i.a + stack[top -1]] = stack[top];
			//printf("%d\n", stack[top]);
			top--;
			break;
		case WRITE:
			printf("%d\n",stack[base(stack, b, i.l) + i.a]);
			break;
		case WRITEA:
			printf("%d\n",stack[base(stack, b, i.l) + i.a+ stack[top]]);
			break;
		case READ:
			scanf("%d",&temp);
			stack[base(stack, b, i.l) + i.a] = temp;
			break;
		case READA:
			scanf("%d",&temp);
			stack[base(stack, b, i.l) + i.a+ stack[top]] = temp;
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
        case JEQ:
            if (stack[top-1] == stack[top])
                pc = i.a;
            top-=2;
            break;
        case JNE:
            if (stack[top-1] != stack[top])
                pc = i.a;
            top-=2;
            break;
        case JL:
            if (stack[top-1] < stack[top])
                pc = i.a;
            top-=2;
            break;
        case JLE:
            if (stack[top-1] <= stack[top])
                pc = i.a;
            top-=2;
            break;
        case JG:
            if (stack[top-1] > stack[top])
                pc = i.a;
            top-=2;
            break;
        case JGE:
            if (stack[top-1] >= stack[top])
                pc = i.a;
            top-=2;
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
int main()
{
	FILE* hbin;
	char s[80];
	int i;
	symset set, set1, set2;
	dx = 3;

	printf("Please input source file name: "); // get file name to be compiled
	scanf("%s", s);
	if ((infile = fopen(s, "r")) == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}
	/////////////////for break
	control_initialize();
	/////////////
	phi = createset(SYM_NULL);
	relset = createset(SYM_EQU, SYM_NEQ, SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ, SYM_NULL);
    logicSet = createset(SYM_AND, SYM_OR);

    // create begin symbol sets
	declbegsys = createset(SYM_CONST, SYM_VAR, SYM_PROCEDURE, SYM_NULL);
	statbegsys = createset(SYM_BEGIN, SYM_CALL, SYM_WRITE, SYM_READ, SYM_IF, SYM_WHILE, SYM_NULL);
	facbegsys = createset(SYM_IDENTIFIER, SYM_ARRAY, SYM_NUMBER, SYM_LPAREN, SYM_NULL);

	err = cc = cx = ll = 0; // initialize global variables
	ch = ' ';
	kk = MAXIDLEN;

	getsym();

	set1 = createset(SYM_PERIOD,SYM_RMATCH, SYM_NULL);
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
