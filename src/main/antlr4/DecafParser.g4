parser grammar DecafParser;

options {
	tokenVocab = DecafLexer;
}

// Classes and fields

topLevel: classDef*;

classDef: ABSTRACT? CLASS id extendsClause? '{' field* '}';

extendsClause: EXTENDS id;

field: varDef | methodDef;

varDef: var ';';

methodDef:
	STATIC? type id '(' varList ')' stmtBlock
	| ABSTRACT type id '(' varList ')' ';';

var: type id;

varList: var (',' var)* | /* empty */;

// Types

type:
	INT							# intType
	| BOOL						# boolType
	| STRING					# stringType
	| VOID						# voidType
	| CLASS id					# classType
	| elemType = type '[' ']'	# arrayType
	| type '(' typeList ')'		# lambdaType;

typeList: (type (',' type)*)?;

// Statements

stmt:
	stmtBlock		# block
	| simple ';'	# simpleStmt
	| IF '(' cond = expr ')' trueBranch = stmt (
		ELSE falseBranch = stmt
	)?																			# if
	| WHILE '(' cond = expr ')' body = stmt										# while
	| FOR '(' init = simple ';' cond = expr ';' update = simple ')' body = stmt	# for
	| BREAK ';'																	# break
	| RETURN expr? ';'															# return
	| PRINT '(' exprList ')' ';'												# print;

stmtBlock: '{' stmt* '}';

simple:
	lValue '=' expr				# assign
	| var ('=' expr)?			# localVarDef
	| expr						# eval
	| /* empty */				# skip
	| VAR__KEYWORD id '=' expr	# localVarDef;

lValue: (expr '.')? id					# lValueVar
	| array = expr '[' index = expr ']'	# lValueIndex;

// Expressions

expr:
	lit															# literal
	| THIS														# this
	| READ_INTEGER '(' ')'										# readInt
	| READ_LINE '(' ')'											# readLine
	| NEW id '(' ')'											# newClass
	| NEW elemType = type '[' length = expr ']'					# newArray
	| INSTANCEOF '(' expr ',' id ')'							# classTest
	| '(' expr ')'												# paren
	| id														# singlePath
	| expr '.' id												# path
	| expr '(' exprList ')'										# call
	| array = expr '[' index = expr ']'							# indexSel
	| '(' CLASS id ')' expr										# classCast
	| prefix = ('-' | '!') expr									# unary
	| lhs = expr infix = ('*' | '/' | '%') rhs = expr			# binary
	| lhs = expr infix = ('+' | '-') rhs = expr					# binary
	| lhs = expr infix = ('<=' | '<' | '>=' | '>') rhs = expr	# binary
	| lhs = expr infix = ('==' | '!=') rhs = expr				# binary
	| lhs = expr infix = '&&' rhs = expr						# binary
	| lhs = expr infix = '||' rhs = expr						# binary
	| FUN '(' varList ')' RA expr								# expressionLambda
	| FUN '(' varList ')' stmtBlock								# blockLambda;

lit:
	INT_LIT														# intLit
	| BOOL_LIT													# boolLit
	| NULL_LIT													# nullLit
	| OPEN_STRING stringChar* (CLOSE_STRING | UNTERM_STRING)	# stringLit;

stringChar: ERROR_NEWLINE | ESC | BAD_ESC | VALID_CHAR;

exprList: expr (',' expr)* | /* empty */;

id: ID;
