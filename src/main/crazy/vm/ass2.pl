%main program
go :- 	open('input.txt',read,Stream),
		read_term(Stream,Y,[]),
		close(Stream),
		open('output.txt',write,Stream1),
		set_output(Stream1),
		catch(reduce_prog(Y),Exception,process(Exception))
		,close(Stream1).
% The first three predicates are used to do type checking while the last two do executing the input program
reduce_prog([Vars, Funcs, Body]) :-
		create_env(Vars,env([], 0, 0), Env),
		type_check_func(Env, Funcs, Env1),
		type_check_body(Env1, Body, _),
		create_runtime_env(Env1, REnv),
		reduce_stmt(config(Body, REnv), _).

%For type checking

% Error handling

% Type checking

process(type_mismatch(X)):- write('Type mismatch: '),write(X),!. 
process(undeclare_identifier(X)):- write('Undeclared identifier: '),write(X),!. 
process(wrong_number_of_argument(X)):- write('Wrong number of arguments: '),write(X),!.
process(redeclare_identifier(X)):- write('Redeclared identifier: '),write(X),!. 
process(redeclare_function(X)):- write('Redeclared function: '),write(X),!. 
process(redeclare_procedure(X)):- write('Redeclared procedure: '),write(X),!. 
process(undeclare_function(X)):- write('Undeclared function: '),write(X),!. 
process(undeclare_procedure(X)):- write('Undeclared procedure: '),write(X),!. 
process(break_not_in_loop(X)):- write('Break not in a loop: '),write(X),!. 
process(continue_not_in_loop(X)):- write('Continue not in a loop: '),write(X),!. 
process(cannot_assign(X)) :- write('Cannot assign to a constant: '),write(X),!.

% Runtime error
process(outofbound(X)):- write('Index out of bound: '),write(X),!.
process(invalid_expression(X)):- write('Invalid expression: '),write(X),!.		

%lookup(symbol table,id,entry)
lookup(env([], _, _), X, _):- throw(undeclare_identifier(X)).
lookup(env([id(X, Y, Z)|_],_,_), X, id(X, Y, Z)) :- !.
lookup(env([_ | L], B, T), X, Y):- lookup(env(L,B,T),X,Y).

%atom1 check X is an identifier in the input program
atom1(true) :- !,fail.
atom1(false) :- !,fail.
atom1([]) :- !,fail.
atom1(X) :- atom(X).

%check X is a boolean constant
boolean(true).
boolean(false).

all_integer(_, []) :- !.
all_integer(Env, [E | ES]) :- 
    get_type_expression(Env, E, T),!,
    T == integer,
    all_integer(Env, ES).

%get type of expression Y based on the symbol table Env. T is the return type
% TODO

% get_type_expression(Env, ele(E1, E2), T) :- 

get_type_array_prime(_, array([]), Length, arr([Length | _], _)) :- !.
get_type_array_prime(Env, array([E | L]), Length, arr([Length2 | Dims], T)) :- 
    get_type_expression(Env, E, arr(Dims, T)),
    Length1 is Length + 1,
    get_type_array_prime(Env, array(L), Length1, arr([Length2 | Dims], T)),!.
get_type_array_prime(Env, array([E | L]), Length, arr([Length2], T)) :- 
    get_type_expression(Env, E, T),
    Length1 is Length + 1,
    get_type_array_prime(Env, array(L), Length1, arr([Length2], T)),!.

get_type_array(Env, A, T) :- 
    get_type_array_prime(Env, A, 0, T),!.
get_type_array(_, A, _) :- 
    throw(type_mismatch(A)).

get_type_expression(Env, array(E), T) :- 
    catch(get_type_array(Env, array(E), T), _, throw(type_mismatch(array(E)))),!.

get_type_expression(Env, Y, T) :- 
    atom1(Y),
    lookup(Env, Y, id(Y, K, T)),
    K == var,!.
get_type_expression(Env, Y, T) :- 
    atom1(Y),
    lookup(Env, Y, id(Y, K, T)),
    K == par,!.
get_type_expression(Env, Y, T) :- 
    atom1(Y),
    lookup(Env, Y, id(Y, K, V)),
    K == const,!,
    get_type_expression(Env, V, T).
get_type_expression(Env, call(Y, Args), T) :- 
    atom1(Y),
    lookup(Env, Y, id(Y, K, F)),
    K == func,!,
    F =.. [func, Pars, T, _],
    type_check_params_args(Env, call(Y, Args), Args, Pars),!.
get_type_expression(_, call(Y, Args), _) :- 
    throw(type_mismatch(call(Y, Args))).

get_type_expression(Env, ele(E1, E2), T) :- 
    get_type_expression(Env, E1, arr(Dims, T)),
    length(E2, V1),
    length(Dims, V2),
    V1 =:= V2,
    all_integer(Env, E2),!.
get_type_expression(_, ele(E1, E2), _) :- 
    throw(type_mismatch(ele(E1, E2))).

get_type_expression(_, Y, integer) :- integer(Y),!.
get_type_expression(_, Y, real) :- float(Y),!.
get_type_expression(_, str(_), string) :- !.
get_type_expression(_, Y, boolean) :- boolean(Y),!.
get_type_expression(Env, add(X, Y), integer):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == integer,!.
get_type_expression(Env, add(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == real,!.
get_type_expression(Env, add(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == real,
    TY == integer,!.
get_type_expression(_, add(X, Y), _):- 
    throw(type_mismatch(add(X, Y))).

get_type_expression(Env, sub(X, Y), integer):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == integer,!.
get_type_expression(Env, sub(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == real,!.
get_type_expression(Env, sub(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == real,
    TY == integer,!.
get_type_expression(_, sub(X, Y), _):- 
    throw(type_mismatch(sub(X, Y))).

get_type_expression(Env, sub(X), integer):- 
    get_type_expression(Env, X, TX),
    TX == integer,!.
get_type_expression(Env, sub(X), real):- 
    get_type_expression(Env, X, TX),
    TX == real,!.
get_type_expression(_, sub(X), _):- 
    throw(type_mismatch(sub(X))).

get_type_expression(Env, times(X, Y), integer):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == integer,!.
get_type_expression(Env, times(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == real,!.
get_type_expression(Env, times(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == real,
    TY == integer,!.
get_type_expression(_, times(X, Y), _):- 
    throw(type_mismatch(times(X, Y))).

get_type_expression(Env, rdiv(X, Y), integer):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == integer,!.
get_type_expression(Env, rdiv(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == real,!.
get_type_expression(Env, rdiv(X, Y), real):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == real,
    TY == integer,!.
get_type_expression(_, rdiv(X, Y), _):- 
    throw(type_mismatch(rdiv(X, Y))).

get_type_expression(Env, idiv(X, Y), integer):- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == integer,!.
get_type_expression(_, idiv(X, Y), _) :- 
    throw(type_mismatch(idiv(X, Y))).

get_type_expression(Env, imod(X, Y), integer) :- 
    get_type_expression(Env, X, TX),
    get_type_expression(Env, Y, TY),
    TX == integer,
    TY == integer,!.
get_type_expression(_, imod(X, Y), _) :- 
    throw(type_mismatch(imod(X, Y))).

get_type_expression(Env, bnot(E), boolean) :- 
    get_type_expression(Env, E, TE),
    TE == boolean,!.
get_type_expression(_, bnot(E), _) :- 
    throw(type_mismatch(bnot(E))).

get_type_expression(Env, band(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == boolean,
    T2 == boolean,!.
get_type_expression(_, band(E1, E2), _) :- 
    throw(type_mismatch(band(E1, E2))),!.

get_type_expression(Env, bor(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == boolean,
    T2 == boolean,!.
get_type_expression(_, bor(E1, E2), _) :- 
    throw(type_mismatch(bor(E1, E2))),!.

get_type_expression(Env, greater(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == integer,!.
get_type_expression(Env, greater(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == real,!.
get_type_expression(Env, greater(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == real,
    T2 == integer,!.
get_type_expression(_, greater(E1, E2), _) :- 
    throw(type_mismatch(greater(E1, E2))).

get_type_expression(Env, less(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == integer,!.
get_type_expression(Env, less(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == real,!.
get_type_expression(Env, less(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == real,
    T2 == integer,!.
get_type_expression(_, less(E1, E2), _) :- 
    throw(type_mismatch(less(E1, E2))).

get_type_expression(Env, ge(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == integer,!.
get_type_expression(Env, ge(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == real,!.
get_type_expression(Env, ge(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == real,
    T2 == integer,!.
get_type_expression(_, ge(E1, E2), _) :- 
    throw(type_mismatch(ge(E1, E2))).

get_type_expression(Env, le(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == integer,!.
get_type_expression(Env, le(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == real,!.
get_type_expression(Env, le(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == real,
    T2 == integer,!.
get_type_expression(_, le(E1, E2), _) :- 
    throw(type_mismatch(le(E1, E2))).

get_type_expression(Env, ne(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == integer,!.
get_type_expression(Env, ne(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == boolean,
    T2 == boolean,!.
get_type_expression(_, ne(E1, E2), _) :- 
    throw(type_mismatch(ne(E1, E2))).

get_type_expression(Env, eql(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == integer,
    T2 == integer,!.
get_type_expression(Env, eql(E1, E2), boolean) :- 
    get_type_expression(Env, E1, T1),
    get_type_expression(Env, E2, T2),
    T1 == boolean,
    T2 == boolean,!.
get_type_expression(_, eql(E1, E2), _) :- 
    throw(type_mismatch(eql(E1, E2))).

% TODO
type_check_assignment(_, id(I, const, _), Expr) :- 
    throw(cannot_assign(assign(I, Expr))).
type_check_assignment(Env, id(I, var, T), Expr) :- 
    get_type_expression(Env, Expr, T1),
    (T \= T1 -> throw(type_mismatch(assign(I, Expr)))
              ; !).

% type checking one statement
type_check_stmt(env(Syms, _, T), L, Ctx) :- 
    is_list(L),
    type_check_body(env(Syms, T, T), L, Ctx).

type_check_stmt(Env, assign(X, Y), _) :- 
    lookup(Env, X, T),
    type_check_assignment(Env, T, Y).

type_check_stmt(Env, if(Expr, S1, S2), Ctx) :- 
    get_type_expression(Env, Expr, T),
    (T \= boolean -> throw(type_mismatch(if(Expr, S1, S2)))
                   ; type_check_stmt(Env, S1, Ctx),
                     type_check_stmt(Env, S2, Ctx)),!.

type_check_stmt(Env, if(Expr, S), Ctx) :- 
    get_type_expression(Env, Expr, T),
    (T \= boolean -> throw(type_mismatch(if(Expr, S)))
                   ; type_check_stmt(Env, S, Ctx)),!.

type_check_stmt(Env, while(Expr, S), _) :- 
    get_type_expression(Env, Expr, T),
    (T \= boolean -> throw(type_mismatch(while(Expr, S)))
                   ; type_check_stmt(Env, S, loop)),!.

type_check_stmt(Env, do(S, Expr), _) :- 
    get_type_expression(Env, Expr, T),
    (T \= boolean -> throw(type_mismatch(do(S, Expr)))
                   ; type_check_stmt(Env, S, loop)),!.

type_check_stmt(Env, loop(Expr, S), _) :- 
    get_type_expression(Env, Expr, T),
    (T \= integer -> throw(type_mismatch(loop(Expr, S)))
                   ; type_check_stmt(Env, S, loop)),!.

type_check_stmt(Env, call(writeInt, [X]), _) :- 
    get_type_expression(Env, X, T),!,
    T == integer, !.
type_check_stmt(_, call(writeInt, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeInt, L))).
type_check_stmt(_, call(writeInt, [Arg]), _) :- 
    throw(type_mismatch(call(writeInt, [Arg]))).

type_check_stmt(_, call(readInt, []), _) :- !.
type_check_stmt(_, call(readInt, L), _) :- 
    length(L, V),
    V \= 0,
    throw(wrong_number_of_argument(call(readInt, L))).

type_check_stmt(Env, call(writeIntLn, [X]), _) :- 
    get_type_expression(Env, X, integer), !.
type_check_stmt(_, call(writeIntLn, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeIntLn, L))).
type_check_stmt(_, call(writeIntLn, [Arg]), _) :- 
    throw(type_mismatch(call(writeIntLn, [Arg]))).

type_check_stmt(_, call(readReal, []), _) :- !.
type_check_stmt(_, call(readReal, L), _) :- 
    length(L, V),
    V \= 0,
    throw(wrong_number_of_argument(call(readReal, L))).

type_check_stmt(Env, call(writeReal, [X]), _) :- 
    get_type_expression(Env, X, real), !.
type_check_stmt(_, call(writeReal, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeReal, L))).
type_check_stmt(_, call(writeReal, [Arg]), _) :- 
    throw(type_mismatch(call(writeReal, [Arg]))).

type_check_stmt(Env, call(writeRealLn, [X]), _) :- 
    get_type_expression(Env, X, real), !.
type_check_stmt(_, call(writeRealLn, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeRealLn, L))).
type_check_stmt(_, call(writeRealLn, [Arg]), _) :- 
    throw(type_mismatch(call(writeRealLn, [Arg]))).

type_check_stmt(_, call(readBool, []), _) :- !.
type_check_stmt(_, call(readBool, L), _) :- 
    length(L, V),
    V \= 0,
    throw(wrong_number_of_argument(call(readBool, L))).

type_check_stmt(Env, call(writeBool, [X]), _) :- 
    get_type_expression(Env, X, boolean), !.
type_check_stmt(_, call(writeBool, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeBool, L))).
type_check_stmt(_, call(writeBool, [Arg]), _) :- 
    throw(type_mismatch(call(writeBool, [Arg]))).

type_check_stmt(Env, call(writeBoolLn, [X]), _) :- 
    get_type_expression(Env, X, boolean), !.
type_check_stmt(_, call(writeBoolLn, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeBoolLn, L))).
type_check_stmt(_, call(writeBoolLn, [Arg]), _) :- 
    throw(type_mismatch(call(writeBoolLn, [Arg]))).

type_check_stmt(Env, call(writeStr, [X]), _) :- 
    get_type_expression(Env, X, string), !.
type_check_stmt(_, call(writeStr, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeStr, L))).
type_check_stmt(_, call(writeStr, [Arg]), _) :- 
    throw(type_mismatch(call(writeStr, [Arg]))).

type_check_stmt(Env, call(writeStrLn, [X]), _) :- 
    get_type_expression(Env, X, string), !.
type_check_stmt(_, call(writeStrLn, L), _) :- 
    length(L, V),
    V \= 1,
    throw(wrong_number_of_argument(call(writeStrLn, L))).
type_check_stmt(_, call(writeStrLn, [Arg]), _) :- 
    throw(type_mismatch(call(writeStrLn, [Arg]))).

type_check_stmt(_, call(writeLn, []), _) :- !.
type_check_stmt(_, call(writeLn, L), _) :- 
    length(L, V),
    V \= 0,
    throw(wrong_number_of_argument(call(writeLn, L))).

type_check_stmt(Env, call(Id, Args), _) :- 
    lookup(Env, Id, id(_, _, proc(Pars, _))),
    type_check_params_args(Env, call(Id, Args), Args, Pars),!.
type_check_stmt(Env, call(Id, Args), _) :- 
    lookup(Env, Id, id(_, _, func(Pars, _, _))),
    type_check_params_args(Env, call(Id, Args), Args, Pars),!.

type_check_stmt(_, continue(null), Ctx) :- Ctx == loop,!.
type_check_stmt(_, continue(null), _) :- 
    throw(continue_not_in_loop(continue(null))).
type_check_stmt(_, break(null), Ctx) :- Ctx == loop,!.
type_check_stmt(_, break(null), _) :- 
    throw(break_not_in_loop(break(null))).

type_check_params_args(_, _, [], []) :- !.
type_check_params_args(_, Stmt, [], [_ | _]) :- 
    throw(wrong_number_of_argument(Stmt)).
type_check_params_args(_, Stmt, [_ | _], []) :- 
    throw(wrong_number_of_argument(Stmt)).

type_check_params_args(Env, Stmt, [Arg | Args], [par(_, T2) | Pars]) :- 
    get_type_expression(Env, Arg, T1),
    T1 == T2,!,
    type_check_params_args(Env, Stmt, Args, Pars),!.
type_check_params_args(_, Stmt, _, _) :- 
    throw(type_mismatch(Stmt)).

%type check one block
type_check_body(_, [], _) :- !.
type_check_body(Env, [var(X, Y) | _], _) :- 
    has_declared(X, Env), !,
    throw(redeclare_identifier(var(X, Y))).
type_check_body(env(L, B, T), [var(X, Y) | L1], Ctx) :- 
    T1 is T + 1,
    type_check_body(env([id(X, var, Y) | L], B, T1), L1, Ctx),!.
type_check_body(Env, [const(X, Y) | _], _) :- 
    has_declared(X, Env),!,
    throw(redeclare_identifier(const(X, Y))).
type_check_body(env(L, B, T), [const(X, Y) | L1], Ctx) :- 
    T1 is T + 1,
    type_check_body(env([id(X, const, Y) | L], B, T1), L1, Ctx),!.

type_check_body(Env, [X | L], Ctx) :- 
    type_check_stmt(Env, X, Ctx),
    type_check_body(Env, L, Ctx).

%type checking a procedure
type_check_one_func(Env, proc(_, Y, Z)):- 
    create_env(Y, Env, env(L, B, T)),
    type_check_body(env(L, B, T), Z, _).
type_check_one_func(Env, func(_, Pars, _, Body)) :- 
    create_env(Pars, Env, env(L, B, T)),
    type_check_body(env(L, B, T), Body, _).

%type checking a list of procedures
type_check_func(Env, [], Env) :- !.

type_check_func(_, [proc(X, _, _) | _], _) :- is_builtin(X), !, throw(redeclare_procedure(X)).
type_check_func(Env,[proc(X, _, _) | _], _) :- has_declared(X, Env), !, throw(redeclare_procedure(X)).

type_check_func(env(Env, B, T), [proc(X, Y, Z) | L], Env1) :- 
    T1 is T+1,
    type_check_one_func(env([id(X, proc, proc(Y, Z)) | Env], T1, T1), proc(X, Y, Z)), !,
    type_check_func(env([id(X, proc, proc(Y, Z)) | Env], B, T1), L, Env1).

type_check_func(_, [func(X, _, _, _) | _], _) :- is_builtin(X), !, throw(redeclare_function(X)).
type_check_func(Env, [func(X, _, _, _) | _], _) :- has_declared(X, Env), !, throw(redeclare_function(X)).

type_check_func(env(Env, B, T), [func(Id, Pars, ReturnType, Body) | L], Env1) :- 
    T1 is T + 1,
    type_check_one_func(env([id(Id, func, func(Pars, ReturnType, Body)) | Env], T1, T1), func(Id, Pars, ReturnType, Body)), !,
    type_check_func(env([id(Id, func, func(Pars, ReturnType, Body)) | Env], B, T1), L, Env1).

%check if X has been declared in the symbol table from B+1 to T
has_declared(X,env([id(X,_,_)|_],B,T)):- T > B ,!.
has_declared(X,env([_|L],B,T)) :- T1 is T - 1, has_declared(X,env(L,B,T1)).

%create a symbol table from the list of variable or constant declarations
% As a suggestion, we may implement a symbol table as the functor env(list,bottom,top)
% where list contains the list of entries id(identifier,kind,type), bottom
% is the index of the first element in the current scope minus 1, and top is the
% index of the last element in the current scope. 
% We have the right to implement the symbol table in a different way.
create_env([],L,L).
create_env([var(X, Y)|_],env(_,0,_),_):- is_builtin(X),!,throw(redeclare_identifier(var(X,Y))).
create_env([var(X, Y)|_],L1,_):-has_declared(X,L1),!,throw(redeclare_identifier(var(X,Y))).
create_env([var(X, Y)|L],env(L1,B,T),L2):- T1 is T+1, create_env(L,env([id(X,var,Y)|L1],B,T1),L2).

create_env([const(X, Y) | _], env(_, 0, _), _) :- is_builtin(X),!,throw(redeclare_identifier(const(X,Y))).
create_env([const(X, Y) | _], Env, _) :- has_declared(X, Env), !, throw(redeclare_identifier(const(X,Y))).
create_env([const(X, Y) | L], env(L1, B, T), L2) :- T1 is T+1, create_env(L, env([id(X, const, Y) | L1], B, T1), L2).

create_env([proc(X, Y) | _], env(_, 0, _), _) :- is_builtin(X),!,throw(redeclare_identifier(proc(X,Y))).
create_env([proc(X, Y) | _], Env, _) :- has_declared(X, Env), !, throw(redeclare_identifier(proc(X,Y))).
create_env([proc(X, Y) | L], env(L1, B, T), L2) :- T1 is T+1, create_env(L, env([id(X, proc, Y) | L1], B, T1), L2).

create_env([func(X, Y) | _], env(_, 0, _), _) :- is_builtin(X),!,throw(redeclare_identifier(func(X,Y))).
create_env([func(X, Y) | _], Env, _) :- has_declared(X, Env), !, throw(redeclare_identifier(func(X,Y))).
create_env([func(X, Y) | L], env(L1, B, T), L2) :- T1 is T+1, create_env(L, env([id(X, func, Y) | L1], B, T1), L2).

create_env([par(X, Y) | _], env(_, 0, _), _) :- is_builtin(X),!,throw(redeclare_identifier(par(X,Y))).
create_env([par(X, Y) | _], Env, _) :- has_declared(X, Env), !, throw(redeclare_identifier(par(X,Y))).
create_env([par(X, Y) | L], env(L1, B, T), L2) :- T1 is T+1, create_env(L, env([id(X, par, Y) | L1], B, T1), L2).

is_builtin(readInt).
is_builtin(writeIntLn).
is_builtin(writeInt).
is_builtin(readReal).
is_builtin(writeRealLn).
is_builtin(writeReal).
is_builtin(readBool).
is_builtin(writeBoolLn).
is_builtin(writeBool).
is_builtin(writeLn).
is_builtin(writeStrLn).
is_builtin(writeStr).

% For runtime
%TODO

is_same_type(E1, E2) :- integer(E1), integer(E2), !.
is_same_type(E1, E2) :- float(E1), float(E2), !.
is_same_type(E1, E2) :- boolean(E1), boolean(E2), !.
is_same_type(E1, E2) :- string(E1), string(E2), !.

is_literal(V) :- number(V), !.
is_literal(V) :- boolean(V), !.
is_literal(V) :- string(V), !.

create_runtime_env(env([], _, _), env([[]], [])) :- !.
create_runtime_env(env([id(I, var, _) | Tail], B, T), env([[(I, undef) | Syms]], Fns)) :- 
    create_runtime_env(env(Tail, B, T), env([Syms], Fns)), !.
create_runtime_env(env([id(I, const, V) | Tail], B, T), env([[(I, V) | Syms]], Fns)) :- 
    create_runtime_env(env(Tail, B, T), env([Syms], Fns)), !.
create_runtime_env(env([id(I, K, T) | Tail], B, Top), env(Vars, [(I, K, T) | Fns])) :- 
    create_runtime_env(env(Tail, B, Top), env(Vars, Fns)), !.

update_local_runtime([(I, _) | L], I, V, [(I, V) | L]) :- !.
update_local_runtime([(I, V1) | L], I, V, [(I, V1) | L1]) :- 
    update_local_runtime(L, I, V, L1).

update_runtime(env([LEnv | L], F), I, V, env([Env | L], F)) :- 
    update_local_runtime(LEnv, I, V, Env),!.
update_runtime(env([LEnv | L], F), I, V, env([LEnv | X], F)) :- 
    update_runtime_env(env(L, F), I, V, env(X, F)).

update_array(_, array([_ | L]), [0], V, array([V | L])) :- !.
update_array(E, _, [Idx], _, _) :- 
    Idx < 0,
    throw(outofbound(E)).
update_array(E, array([]), [Idx], _, _) :- 
    Idx > 0,
    throw(outofbound(E)).
update_array(E1, array([E | L]), [Idx], V, array([E | X])) :- 
    Idx1 is Idx - 1,
    update_array(E1, array(L), [Idx1], V, array(X)),!.
update_array(E1, array([A | As]), [0 | L], V, array([A1 | As])) :- 
    update_array(E1, A, L, V, A1), !.
update_array(E, _, [Idx | _], _, _) :- 
    Idx < 0,
    throw(outofbound(E)).
update_array(E, array([]), [Idx | _], _, _) :- 
    Idx > 0,
    throw(outofbound(E)).
update_array(E1, array([A | As]), [Idx | Idxs], V, array([A | X])) :- 
    Idx1 is Idx - 1,
    update_array(E1, array(As), [Idx1 | Idxs], V, array(X)), !.

lookup_runtime_env2([(I, undef) | _], I, _) :- throw(invalid_expression(I)).
lookup_runtime_env2([(I, V) | _], I, V) :- !.
lookup_runtime_env2([_ | L], I, V) :- lookup_runtime_env2(L, I, V), !.

lookup_runtime(env(Ls, _), I, V) :- 
    append(Ls, L),
    lookup_runtime_env2(L, I, V).

lookup_func(env(_, [(I, K, T) | _]), I, (K, T)) :- !.
lookup_func(env(_, [_ | L]), I, F) :- lookup_func(env(_, L), I, F).

reduce(config(add(E1,E2),Env),config(R,Env2)) :- 
    reduce_all(config(E1,Env),config(V1,Env1)),
    reduce_all(config(E2,Env1),config(V2,Env2)),
    R is V1+V2.

reduce(config(sub(E1,E2),Env),config(R,Env2)) :-  
    reduce_all(config(E1,Env),config(V1,Env1)),
    reduce_all(config(E2,Env1),config(V2,Env2)),
    R is V1-V2.

reduce(config(sub(E), Env), config(R, Env1)) :- 
    reduce_all(config(E, Env), config(V, Env1)),
    R is -V.


reduce(config(times(E1,E2),Env),config(R,Env2)) :-  
    reduce_all(config(E1,Env),config(V1,Env1)),
    reduce_all(config(E2,Env1),config(V2,Env2)),
    R is V1*V2.

reduce(config(rdiv(E1,E2),Env),config(R,Env2)) :-  
    reduce_all(config(E1,Env),config(V1,Env1)),
    reduce_all(config(E2,Env1),config(V2,Env2)),
    R is V1/V2.


reduce(config(idiv(E1,E2),Env),config(R,Env2)) :-  
    reduce_all(config(E1,Env),config(V1,Env1)),
    reduce_all(config(E2,Env1),config(V2,Env2)),
    R is div(V1, V2).


reduce(config(imod(E1,E2),Env),config(R,Env2)) :-  
    reduce_all(config(E1,Env),config(V1,Env1)),
    reduce_all(config(E2,Env1),config(V2,Env2)),
    R is mod(V1, V2).

reduce(config(greater(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 > V2, !,
    R = true.
reduce(config(greater(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 =< V2, !,
    R = false.
reduce(config(greater(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce_all(config(E2, Env1), config(V2, Env2)),
    reduce(config(greater(V1, V2), Env2), config(R, Env2)).

reduce(config(less(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 > V2, !,
    R = false.
reduce(config(less(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 =< V2, !,
    R = true.
reduce(config(less(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce_all(config(E2, Env1), config(V2, Env2)),
    reduce(config(less(V1, V2), Env2), config(R, Env2)).

reduce(config(ge(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 >= V2, !,
    R = true.
reduce(config(ge(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 < V2, !,
    R = false.
reduce(config(ge(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce_all(config(E2, Env1), config(V2, Env2)),
    reduce(config(ge(V1, V2), Env2), config(R, Env2)).

reduce(config(le(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 =< V2, !,
    R = true.
reduce(config(le(V1, V2), Env), config(R, Env)) :- 
    number(V1),
    number(V2),
    V1 > V2, !,
    R = false.
reduce(config(le(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce_all(config(E2, Env1), config(V2, Env2)),
    reduce(config(le(V1, V2), Env2), config(R, Env2)).

reduce(config(ne(V1, V2), Env), config(R, Env)) :- 
    is_same_type(V1, V2),
    V1 \= V2, !,
    R = true.
reduce(config(ne(V1, V2), Env), config(R, Env)) :- 
    is_same_type(V1, V2),
    V1 =:= V2, !,
    R = false.
reduce(config(ne(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce_all(config(E2, Env1), config(V2, Env2)),
    reduce(config(ne(V1, V2), Env2), config(R, Env2)).

reduce(config(eql(V1, V2), Env), config(R, Env)) :- 
    integer(V1),
    integer(V2),
    V1 =:= V2,
    R = true.
reduce(config(eql(V1, V2), Env), config(R, Env)) :- 
    boolean(V1),
    boolean(V2),
    V1 == V2,
    R = true.
reduce(config(eql(V1, V2), Env), config(R, Env)) :- 
    integer(V1),
    integer(V2),
    V1 \= V2,
    R = false.
reduce(config(eql(V1, V2), Env), config(R, Env)) :- 
    boolean(V1),
    boolean(V2),
    V1 \= V2,
    R = false.
reduce(config(eql(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce_all(config(E2, Env1), config(V2, Env2)),
    reduce(config(eql(V1, V2), Env2), config(R, Env2)).

reduce(config(bnot(V), Env), config(V1, Env)) :- 
    boolean(V),
    V == true,
    V1 = false,!.
reduce(config(bnot(V), Env), config(V1, Env)) :- 
    boolean(V),
    V == false,
    V1 = true,!.
reduce(config(bnot(E), Env), config(R, Env1)) :- 
    reduce_all(config(E, Env), config(V, Env1)),
    reduce(config(bnot(V), Env1), config(R, Env1)).

reduce(config(band(V1, _), Env), config(R, Env)) :- 
    boolean(V1),
    V1 == false,
    R = false,!.
reduce(config(band(V1, E2), Env), config(R, Env1)) :- 
    boolean(V1),
    reduce_all(config(E2, Env), config(V2, Env1)),
    V2 == false,
    R = false,!.
reduce(config(band(V1, V2), Env), config(R, Env)) :- 
    boolean(V1),
    boolean(V2),
    R = true,!.
reduce(config(band(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce(config(band(V1, E2), Env1), config(R, Env2)).

reduce(config(bor(V1, _), Env), config(R, Env)) :- 
    boolean(V1),
    V1 == true,
    R = true,!.
reduce(config(bor(V1, E2), Env), config(R, Env1)) :- 
    boolean(V1),
    reduce_all(config(E2, Env), config(V2, Env1)),
    V2 == true,
    R = true,!.
reduce(config(bor(V1, V2), Env), config(R, Env)) :- 
    boolean(V1),
    boolean(V2),
    R = false,!.
reduce(config(bor(E1, E2), Env), config(R, Env2)) :- 
    reduce_all(config(E1, Env), config(V1, Env1)),
    reduce(config(bor(V1, E2), Env1), config(R, Env2)).

reduce_exprs(config([], Env), config([], Env)) :- !.
reduce_exprs(config([E | Es], Env), config([V | X], Env2)) :- 
    reduce_all(config(E, Env), config(V, Env1)),
    reduce_exprs(config(Es, Env1), config(X, Env2)).

reduce_array_subscript(E, _, [Idx | _], _) :- 
    Idx < 0,
    throw(outofbound(E)).
reduce_array_subscript(E, array([]), [Idx | _], _) :- 
    Idx > 0,
    throw(outofbound(E)).
reduce_array_subscript(_, array([V | _]), [0], V) :- !.
reduce_array_subscript(E, array([_ | Vs]), [Idx], V) :- 
    Idx1 is Idx - 1,
    reduce_array_subscript(E, array(Vs), [Idx1], V), !.
reduce_array_subscript(E, array([A | _]), [0 | Idxs], V) :- 
    reduce_array_subscript(E, A, Idxs, V), !.
reduce_array_subscript(E, array([_ | As]), [Idx | Idxs], V) :- 
    Idx1 is Idx - 1,
    reduce_array_subscript(E, array(As), [Idx1 | Idxs], V), !.

reduce_all(config(V, Env),config(V, Env)):- number(V),!.
reduce_all(config(V, Env),config(V, Env)):- boolean(V),!.
reduce_all(config(V, Env),config(V, Env)):- string(V),!.
reduce_all(config(I, Env),config(V, Env)):- atom1(I), lookup_runtime(Env, I, V), !.
reduce_all(config(ele(I, Exprs), Env), config(V, Env1)) :- 
    lookup_runtime(Env, I, Arr),
    reduce_exprs(config(Exprs, Env), config(Vs, Env1)),
    reduce_array_subscript(ele(I, Exprs), Arr, Vs, V), !.
reduce_all(config(call(Id, []), Env), config(V, Env)) :- 
    member(Id, [readInt, readReal, readBool]),
    read(V),!.
reduce_all(config(call(Id, Args), env(Syms, Fns)), config(V, env(T, Fns))) :- 
    lookup_func(env(Syms, Fns), Id, (func, func(Pars, Body))),
    reduce_exprs(config(Args, env(Syms, Fns)), config(Vs, env(Syms1, Fns))),
    map_params_args(Pars, Vs, LocalEnv),
    reduce_stmt(config(Body, env([[(Id, undef) | LocalEnv] | Syms1], Fns)), env([LocalEnv1 | T], Fns)),
    lookup_runtime(env([LocalEnv1 | T], Fns), Id, V).

reduce_all(config(E, Env),config(E2, Env)):- 
		reduce(config(E, Env),config(E1, Env)),!, 
		reduce_all(config(E1,Env),config(E2,Env)).

reduce_stmt(config([], Env), Env) :- !.
reduce_stmt(config([Stmt | Stmts], Env), Env2) :- 
    reduce_stmt(config(Stmt, Env), Env1),
    reduce_stmt(config(Stmts, Env1), Env2).

% X is Id or array subscript
reduce_stmt(config(assign(ele(Id, Exprs), Expr), Env), Env3) :- 
    lookup_runtime(Env, Id, A),
    reduce_exprs(config(Exprs, Env), config(Vs, Env1)),
    reduce_all(config(Expr, Env1), config(V, Env2)),
    update_array(ele(Id, Exprs), A, Vs, V, R),
    update_runtime(Env2, Id, R, Env3), !.

reduce_stmt(config(assign(X, Expr), Env), Env1) :-
    is_literal(Expr),!,
    atom1(X),
    update_runtime(Env, X, Expr, Env1), !.

reduce_stmt(config(assign(X, Expr), Env), Env2) :-
    reduce_all(config(Expr, Env), config(V, Env1)),
    reduce_stmt(config(assign(X, V), Env1), Env2), !.

reduce_stmt(config(if(false, _, S), Env), Env1) :- 
    reduce_stmt(config(S, Env), Env1).
reduce_stmt(config(if(true, S, _), Env), Env1) :- 
    reduce_stmt(config(S, Env), Env1).
reduce_stmt(config(if(E, S1, S2), Env), Env2) :- 
    reduce_all(config(E, Env), config(V, Env1)),
    reduce_stmt(config(if(V, S1, S2), Env1), Env2).

reduce_stmt(config(if(false, _), Env), Env) :- !.
reduce_stmt(config(if(true, S), Env), Env1) :- 
    reduce_stmt(config(S, Env), Env1).
reduce_stmt(config(if(Expr, S), Env), Env2) :- 
    reduce_all(config(Expr, Env), config(V, Env1)),
    reduce_stmt(config(if(V, S), Env1), Env2).

reduce_stmt(config(while(false, _), Env), Env) :- !.
reduce_stmt(config(while(Expr, S), Env), Env2) :-
    reduce_all(config(Expr, Env), config(V, Env1)),
    (V == true -> reduce_stmt(config([S, while(Expr, S)], Env1), Env2)
                ; reduce_stmt(config(while(false, _), Env1), Env2)).

reduce_stmt(config(do(L, Expr), Env), Env1) :- 
    reduce_stmt(config([L, while(Expr, L)], Env), Env1).

reduce_stmt(config(loop(0, _), Env), Env) :- !.
reduce_stmt(config(loop(V, S), Env), Env1) :- 
    integer(V),
    V > 0,
    V1 is V - 1,
    reduce_stmt(config([S, loop(V1, S)], Env), Env1).
reduce_stmt(config(loop(V, _), _), _) :- 
    integer(V),
    V < 0,
    fail,!.
reduce_stmt(config(loop(Expr, S), Env), Env2) :- 
    reduce_all(config(Expr, Env), config(V, Env1)),
    reduce_stmt(config(loop(V, S), Env1), Env2).

reduce_stmt(config(var(Id, _), env([ L | L1 ], F)), env([[(Id, undef) | L] | L1], F)) :- !.
reduce_stmt(config(const(Id, V), env([ L | L1 ], F)), env([[(Id, V) | L] | L1], F)) :- !.

reduce_stmt(config(call(Id, [Arg]), Env), Env1) :- 
    member(Id, [writeInt, writeReal, writeBool, writeStr]),
    reduce_all(config(Arg, Env), config(V, Env1)),
    write(V),!.
reduce_stmt(config(call(Id, [Arg]), Env), Env1) :- 
    member(Id, [writeIntLn, writeRealLn, writeBoolLn, writeStrLn]),
    reduce_all(config(Arg, Env), config(V, Env1)),
    writeln(V),!.
reduce_stmt(config(call(writeLn, []), Env), Env) :- 
    writeln(''),!.

reduce_stmt(config(call(Id, Args), env(Syms, Fns)), env(T, Fns)) :- 
    lookup_func(env(Syms, Fns), Id, (proc, proc(Pars, Body))),
    reduce_exprs(config(Args, env(Syms, Fns)), config(Vs, env(Syms1, Fns))),
    map_params_args(Pars, Vs, LocalEnv),
    reduce_stmt(config(Body, env([LocalEnv | Syms1], Fns)), env([_ | T], Fns)).

map_params_args([], [], []) :- !.
map_params_args([par(Id, _) | Pars], [Arg | Args], [(Id, Arg) | X]) :- 
    map_params_args(Pars, Args, X), !.

% vim: set ft=prolog

% create_env([var(a, integer), var(b, integer)], env([], 0, 0), Env), create_runtime_env(Env, REnv), reduce_stmt(config([assign(a, 0), assign(b, 1), do([assign(b, times(b, 2))], ne(a, 0))], REnv), Env1).
% create_env([var(a, integer), var(b, integer)], env([], 0, 0), Env), create_runtime_env(Env, REnv), reduce_stmt(config([assign(a, 0), assign(b, 1), loop(10, assign(b, add(b, 1)))], REnv), Env1).
