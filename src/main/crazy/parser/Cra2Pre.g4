grammar Cra2Pre;

options {
    language=Python3;
}

@lexer::header {
from lexererr import *
}

program	returns [String s]
	: PROGRAM IDENT SEMICOLON v=var_decls p=proc_decls b=block_stmt DOT EOF
	  {$s = f'[[{$v.s}],[{$p.s}],{$b.s}]. '}
	;

var_decls returns [String s]
    : var_decl* {$s = ','.join([decl.s for decl in $ctx.var_decl()])}
    ;

var_decl returns [String s]
	: VAR ident_list COLON t=data_type SEMICOLON {$s = ','.join([f'var({ident},{$t.s})' for ident in $ident_list.l])}
	| CONST IDENT EQ c=constant SEMICOLON {$s = f'const({$IDENT.text},{$c.s})'}
	;

ident_list returns [List<String> l]
    : IDENT (COMMA IDENT)* {$l = list(map(lambda x: x.getText(), $ctx.IDENT()))}
    ;

proc_decls returns [String s]
    : proc_decl* {$s = ','.join([decl.s for decl in $ctx.proc_decl()])}
    ;

proc_decl returns [String s]
    : FUNC IDENT '(' p=param_list ')' COLON t=primitive_type SEMICOLON b=block_stmt SEMICOLON
    {$s = f'func({$IDENT.text},{$p.s},{$t.s},{$b.s})'}
    | PROC IDENT '(' p=param_list ')' SEMICOLON b=block_stmt SEMICOLON
    {$s = f'proc({$IDENT.text},{$p.s},{$b.s})'}
    ;

param_list returns [String s]
    : param (SEMICOLON param)* {$s = f'[{",".join([p.s for p in $ctx.param()])}]'}
    | {$s = ''}
    ;

param returns [String s]
    : IDENT (COMMA IDENT)* COLON t=data_type
    {$s = ','.join([f'par({i.getText()},{$t.s})' for i in $ctx.IDENT()])}
    ;

data_type returns [String s]
	: pt=primitive_type {$s = $pt.s}
	| at=array_type {$s = $at.s}
	;
	
primitive_type returns [String s]
    : INTEGER {$s = 'integer' }
	| REAL	  {$s = 'real' }
	| BOOLEAN {$s = 'boolean' }
	| STRING  {$s = 'string'}
	;

array_type returns [String s]
    : ARRAY ('[' INTLIT ']')+ OF pt=primitive_type
    {$s = f'arr([{",".join([token.getText() for token in $ctx.INTLIT()])}],{$pt.s})'}
    ;

block_stmt returns [String s]
	: BEGIN v=var_decls stmts END {$s = f'[{$v.s + "," if $v.s else ""}{$stmts.s}]'}
	;

stmts returns [String s]
    : stmt+ {$s = ','.join([stmt.s for stmt in $ctx.stmt()])}
    | {$s = ''}
    ;
	
stmt returns [String s]
	: t=block_stmt {$s = $t.s}
	| t1=assign_stmt {$s = $t1.s}
	| if_stmt {$s = $if_stmt.s}
	| call_stmt {$s = $call_stmt.s}
	| loop_stmt {$s = $loop_stmt.s}
	| while_stmt {$s = $while_stmt.s}
	| do_while_stmt {$s = $do_while_stmt.s}
	| continue_stmt {$s = $continue_stmt.s}
	| break_stmt {$s = $break_stmt.s}
	;

assign_stmt returns [String s]
	: {b = ''}(IDENT{b = $IDENT.text} | array_subscript{b = $array_subscript.s}) WALRUS a=arg SEMICOLON {$s = f'assign({b},{$a.s})'}
	;

if_stmt returns [String s]
    : IF expr THEN stmt ELSE stmt {$s = f'if({$expr.s},{$ctx.stmt(0).s},{$ctx.stmt(1).s})'}
    | IF expr THEN stmt {$s = f'if({$expr.s},{$stmt.s})'}
    ;

loop_stmt returns [String s]
    : LOOP e=expr DO stmt {$s = f'loop({$e.s},{$stmt.s})'}
    ;

while_stmt returns [String s]
    : WHILE e=expr DO stmt {$s = f'while({$e.s},{$stmt.s})'}
    ;

do_while_stmt returns [String s]
    : DO stmts WHILE e=expr SEMICOLON {$s = f'do([{$stmts.s}],{$e.s})'}
    ;

call_stmt returns [String s]
    : IDENT '(' al=arg_list ')' SEMICOLON {$s = f'call({$IDENT.text},[{$al.s}])'}
    ;

arg_list returns [String s]
    : arg (COMMA arg)* {$s = ','.join([arg.s for arg in $ctx.arg()])}
    | {$s = ''}
    ;

arg returns [String s]
    : expr {$s = $expr.s}
    | a=array_lit {$s = $a.s}
    ;

break_stmt returns [String s]
    : BREAK SEMICOLON {$s = 'break(null)'}
    ;

continue_stmt returns [String s]
    : CONTINUE SEMICOLON {$s = 'continue(null)'}
    ;

expr returns [String s]
    : expr AND expr {$s = f'band({$ctx.expr(0).s},{$ctx.expr(1).s})'}
	| expr OR expr {$s = f'bor({$ctx.expr(0).s},{$ctx.expr(1).s})'}
	| expr{o = ''} (LT{o = 'less'} | LE{o = 'le'} | GT{o = 'greater'} | GE{o = 'ge'}) expr {$s = f'{o}({$ctx.expr(0).s},{$ctx.expr(1).s})'}
	| expr{o = ''} (EQ{o = 'eql'} | NOTEQ{o = 'ne'}) expr {$s = f'{o}({$ctx.expr(0).s},{$ctx.expr(1).s})'}
	| expr{o = ''} (MUL{o = 'times'} | SLASH{o = 'rdiv'} | DIV{o = 'idiv'} | MOD{o = 'mod'}) expr {$s = f'{o}({$ctx.expr(0).s},{$ctx.expr(1).s})'}
	| expr{o = ''} (PLUS{o = 'add'} | SUB{o = 'sub'}) expr {$s = f'{o}({$ctx.expr(0).s},{$ctx.expr(1).s})'}
	| expr1 {$s = $expr1.s}
    ;

expr1 returns [String s]
    : {o = ''}(SUB{o = 'sub'} | NOT{o = 'bnot'}) expr2 {$s = f'{o}({$ctx.expr2().s})'}
    | expr2 {$s = $expr2.s}
    ;

expr2 returns [String s]
    : c=constant {$s = $c.s}
	| '(' expr ')' {$s = $expr.s}
	| f=func_call {$s = $f.s}
	| IDENT {$s = $IDENT.text}
	| a=array_subscript {$s = $a.s}
    ;

// TODO: is array_lit | stringlit an expression
array_lit returns [String s]
    : '[' array_element (COMMA array_element)* ']'
    {$s = f'array([{",".join([e.s for e in $ctx.array_element()])}])'}
    ;

array_element returns [String s]
    : INTLIT {$s = $INTLIT.text}
    | REALLIT {$s = $REALLIT.text}
    | a=array_lit {$s = $a.s}
    ;

constant returns [String s]
    : INTLIT {$s = $INTLIT.text}
	| BOOLLIT {$s = $BOOLLIT.text}
	| REALLIT {$s = $REALLIT.text}
	| STRINGLIT {$s = 'str("'+$STRINGLIT.text[1:-1].replace("\'\'", "\'")+'")'}
	;

array_subscript returns [String s]
    : IDENT '[' expr ']' ('[' expr ']')*
    {$s = f'ele({$ctx.IDENT().getText()},[{",".join([e.s for e in $ctx.expr()])}])'}
    ;

func_call returns [String s]
    : IDENT '(' al=arg_list ')' {$s = f'call({$IDENT.text},[{$al.s}])'}
    ;

// Seperators
DOT         : '.';
SEMICOLON   : ';';
COLON       : ':';
COMMA       : ',';

// Operators
WALRUS  : ':=';
EQ      : '=';
GT      : '>';
LT      : '<';
GE      : '>=';
LE      : '<=';
NOTEQ   : '<>';
PLUS    : '+';
SUB     : '-';
MUL     : '*';
SLASH   : '/';

// Keywords
AND         : 'and';
CONTINUE    : 'continue';
OF          : 'of';
THEN        : 'then';
ARRAY       : 'array';
DIV         : 'div';
FUNC        : 'function';
OR          : 'or';
BEGIN       : 'begin' ;
DO          : 'do';
IF          : 'if';
LOOP        : 'loop';
PROC        : 'procedure';
BOOLEAN     : 'boolean';
INTEGER     : 'integer' ;
PROGRAM     : 'program' ;
VAR         : 'var';
BREAK       : 'break';
ELSE        : 'else';
MOD         : 'mod';
REAL        : 'real' ;
WHILE       : 'while';
CONST       : 'const';
END         : 'end' ;
NOT         : 'not';
STRING      : 'string';

// Literals
fragment FRACTION   : DOT ('0' | [0-9]*[1-9]);
fragment EXP        : [eE][-]?[0-9]+;

REALLIT : INTLIT (FRACTION EXP? | EXP) | FRACTION EXP?;
INTLIT  : '0' | [1-9][0-9]* ;
BOOLLIT : 'true' | 'false';

fragment STR_CHAR: ~[\n\t\\'] | '\\'[nt\\] | '\'\'';
STRINGLIT: '\'' STR_CHAR* '\'';

IDENT: [a-z][a-zA-Z0-9]*;

COMMENT: ('//' .*? '\n' | '/*' .*? '*/') -> skip;
WS : [ \t\r\n]+ -> skip;

ERROR_UNCLOSED_STRING: '\'' STR_CHAR* ('\n' | EOF) {raise UncloseString(self.text[:-1] if self.text[-1] == '\n' else self.text)};

ERROR_ILLEGAL_ESCAPE: '\'' STR_CHAR* '\\'~[nt\\] {raise IllegalEscape(self.text)};

ERROR_TOKEN : . {raise ErrorToken(self.text)};
