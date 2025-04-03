grammar Expr;

expr
    : atom
    | sexpr
    ;

atom
    : VAR
    ;

sexpr
    : lneg
    | lor
    | land
    | limpl
    | lequiv
    | parexpr
    ;

lneg
    : LPAR LNEG expr RPAR
    ;

lor
    : LPAR LOR expr expr RPAR
    ;

land
    : LPAR LAND expr expr RPAR
    ;

limpl
    : LPAR IMPL expr expr RPAR
    ;

lequiv
    : LPAR EQUIV expr expr RPAR
    ;

parexpr
    : LPAR expr RPAR
    ;

VAR
    : 'x' ('1' .. '9')('0' .. '9')*
    ;

LPAR
    : '('
    ;

RPAR
    : ')'
    ;

LNEG
    : 'not'
    ;

LOR
    : 'or'
    ;

LAND
    : 'and'
    ;

IMPL
    : 'impl'
    ;

EQUIV
    : 'equiv'
    ;

WS
   : [ \r\n\t]+ -> skip
   ;