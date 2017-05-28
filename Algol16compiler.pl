


compile(In, Out) :-
	phrase(lexer(Tokens), In),
	phrase(parse(AST), Tokens),
	unfold(AST, UnfoldedAST, [], 5, LastNumber, _, [], [], Functions, []),
	clean(Functions, CleanedFunctions),
	insertAll(CleanedFunctions, CleanedFunctions, FunctionsAfterInsert),
	insertToBody(FunctionsAfterInsert, UnfoldedAST, TheBestAstThereEverWas),
	comp(TheBestAstThereEverWas, LastNumber, _,  65535, [( 4,[0,0,0,2])] , PreOut, []),
	NofVars is LastNumber - 5,
	allocateMem(NofVars, PreOut, AlocOut ),
	numToHex(LastNumber, Hex),
	Out = [ [9,8,0,0],Hex, [9,1,0,0], [0,0,0,0], [f,f,f,f]|AlocOut ].

%Lexer 

aut(Input) :-
	phrase(lexer(Tokens), Input),
	%write(Tokens),
	phrase(parse(AST), Tokens),
	unfold(AST, UnfoldedAST, [], 5, LastNumber, Vars, [], [], Func, []),
	nl,
	write(UnfoldedAST),
	nl,
	write(LastNumber),
	nl,
	write(Vars),
	nl,
	write(Func),
	nl,
	clean(Func, CleanedFunctions),
	write(CleanedFunctions),
	insertAll(CleanedFunctions, CleanedFunctions, FunctionsAfterInsert),
	nl,
	nl,
	write(FunctionsAfterInsert),
	nl,
	nl,
	insertToBody(FunctionsAfterInsert, UnfoldedAST, TheBestAstThereEverWas),
	write(TheBestAstThereEverWas),
	nl,
	nl,
	comp(TheBestAstThereEverWas, LastNumber, _,  65535, [( 4,[0,0,0,2])] , PreOut, []),
	NofVars is LastNumber - 5,
	allocateMem(NofVars, PreOut, AlocOut ),
	numToHex(LastNumber, Hex),
	Out = [ [9,8,0,0],Hex, [9,1,0,0], [0,0,0,0], [f,f,f,f]|AlocOut ],
	write(Out).

parsable(Input) :- 
	phrase(lexer(Tokens), Input),
	write(Tokens),
	nl,
	phrase(parse(AST), Tokens),
	write(AST),
	nl.

lexer(Tokens) -->
	whiteSpace, %%biale znaki na poczatku
	(
		(
			operator(Token),!;
			liczba(Token),!;
			identyfikator(Token),!
		),
		{Tokens = [Token|Rest]},
		lexer(Rest)
		;
		%%pusty ciag
		"",{Tokens=[]}
	).

whiteSpace -->
	"(*",!, endOfcomment.
whiteSpace -->
	[X], {code_type(X, space)},!, whiteSpace.
whiteSpace -->
	"".
endOfcomment -->
	"*)",!, whiteSpace.
endOfcomment -->
	[_], !, endOfcomment.

operator(eq) --> 
	"=", !.
operator(diff) --> 
	"<>", !.
operator(plus) --> 
	"+", !.
operator(minus) --> 
	"-", !.
operator(mult) --> 
	"*", !.
operator(less) --> 
	"<=", !.
operator(more) --> 
	">=", !.
operator(sless) --> 
	"<", !.
operator(smore) --> 
	">", !.
operator(assign) -->
	":=", !.
operator(part) -->
	";", !.
operator(comma) -->
	",", !.
operator(lp) -->
	"(", !.
operator(rp) -->
	")", !.

liczba(Token) -->
	cyfra(D),
	cyfry(Rest),
	{ number_chars(N, [D|Rest]), Token = num(N) }.

cyfra(Digit) -->
	[Digit],
	{ code_type(Digit, digit) }.

cyfry([D|Rest]) -->
	cyfra(D),!,
	cyfry(Rest).
cyfry([]) -->
	"".

identyfikator(Token) -->
	litera(L),
	wczytaj(Rest),
	(
		{ key([L|Rest], Token),! };
		{ Token = variable([L|Rest]) } 
	).

litera(L) -->
	[L], { code_type(L, alpha) }.

wczytaj([L|Rest]) -->
	(litera(L), !; cyfra(L),!; "_",!; "'", !),
	wczytaj(Rest).
wczytaj([]) -->
	"".	

key("and",and) :- !.
key("begin",begin) :- !.
key("call", call) :- !.
key("div", div) :- !.
key("do", do) :- !.
key("done", done) :- !.
key("else", else) :- !.
key("end", end) :- !.
key("fi", fi) :- !.	 
key("if", if) :- !.
key("local", local) :- !.
key("mod", mod) :- !.
key("not", not) :- !.
key("or", or) :- !.
key("procedure", procedure) :- !.
key("program", program) :- !.
key("read", read) :- !.
key("return", return) :- !.
key("then", then) :- !.
key("value", value) :- !.
key("while", while) :- !.
key("write", write).



/* Parse tokens and build AST */

% parse(AST, Lista Oznaczajaca zagłębienie)
parse(program(variable(Name), Dek, Inst) ) -->
	[program], !,
	[variable(Name)],
	blok(Dek, Inst).

	


blok( deklaracje(Vars, Proc), instrukcje(Inst) ) -->
	deklaracje( VarsUn, Proc ),
	{sort(VarsUn,Vars)},
	[begin],
	instrukcje(InstRev),
	{reverse(InstRev, InstRev2)},
	{reverse([return(num(0))|InstRev2], Inst)},
	[end].




deklaracje( Vars, Proc ) -->
	[local],!, zmienne(Vars1),
	{append(Vars1,Vars2, Vars)},
	deklaracje(Vars2, Proc);
	[procedure],!, [variable(Name)], [lp], arguments( TrueArgs, ValArgs ), [rp], blok(Dek, Inst),
	{Proc = [fun(variable(Name), TrueArgs, ValArgs, Dek, Inst)|NProc]},
	deklaracje(Vars, NProc).
deklaracje( [], []) --> []. 

zmienne(Vars) -->
	[variable(Name)],
	([comma],!, {Vars = [variable(Name)|Prev]}, zmienne(Prev);
	{Vars = [variable(Name)]}).

arguments( TrueArgs, ValArgs ) -->
	[value],!, [variable(Name)], {ValArgs = [variable(Name)|ValArgs1]},( [comma], !, arguments(TrueArgs, ValArgs1); { TrueArgs = [], ValArgs1 = [] });
	[variable(Name)],!, {TrueArgs = [variable(Name)|TrueArgs1]}, ( [comma], !,  arguments(TrueArgs1,ValArgs); {TrueArgs1 = [], ValArgs = [] }).
arguments([],[]) --> [].



instrukcje([Inst|Rest]) --> instrukcja(Inst),!, ([part],!,instrukcje(Rest); {Rest = []} ).
instrukcje([]) --> [].

instrukcja(Inst) -->
	[variable(Left)], !, [assign], arithmeticExpr(Right), {Inst = assign(variable(Left), Right)};
	[if],!, logicExpr(Expr), [then], instrukcje(Instr),([else],! , instrukcje(Else), [fi],{Inst = if(Expr, Instr, Else )}; [fi], {Inst = if(Expr, Instr, [] )}  );
	[while], !, logicExpr(Expr), [do], instrukcje(Instr), [done], {Inst = while(Expr, Instr)};
	[call], !, procedureCall(Inst);
	[return], !, arithmeticExpr(Expr), {Inst = return( Expr)};
	[read], !, [variable(Name)], {Inst = read(variable(Name))};
	[write], !, arithmeticExpr(Right), {Inst = write(Right)}.


procedureCall(Proc) --> [variable(Name)], [lp], argumentsAplication(TrueArgs, ValArgs), [rp], {Proc = call(variable(Name), TrueArgs, ValArgs)}.


argumentsAplication( TrueArgs, ValArgs ) -->
	[value],!, arithmeticExpr(Expr), {ValArgs = [Expr|ValArgs1]}, ( [comma], !, argumentsAplication(TrueArgs, ValArgs1); { TrueArgs = [], ValArgs1 = [] });
	arithmeticExpr(Expr),!, {TrueArgs = [Expr|TrueArgs1]}, ( [comma], !,  argumentsAplication(TrueArgs1,ValArgs); {TrueArgs1 = [], ValArgs = [] }).
argumentsAplication([],[]) --> [].


arithmeticExpr(Expr) --> summand(Expr1), !,arithmeticExpr(Expr1, Expr).
arithmeticExpr(Acc, Expr) --> [plus], !, summand(Expr1), {Acc1 = plus(Acc,Expr1)}, arithmeticExpr(Acc1, Expr).
arithmeticExpr(Acc, Expr) --> [minus], !, summand(Expr1), {Acc1 = minus(Acc,Expr1)}, arithmeticExpr(Acc1, Expr).
arithmeticExpr(Acc, Acc) --> [].

summand(Expr) --> factor(Expr1), !, summand( Expr1, Expr).
summand(Acc, Expr) --> [mult], !, factor(Expr1), {Acc1 = mult(Acc, Expr1)}, summand(Acc1, Expr).
summand(Acc, Expr) --> [mod], !, factor(Expr1), {Acc1 = mod(Acc, Expr1)}, summand(Acc1, Expr).
summand(Acc, Expr) --> [div], !, factor(Expr1), {Acc1 = div(Acc, Expr1)}, summand(Acc1, Expr).
summand(Acc, Acc) --> [].

factor( Expr ) --> ([minus],!, {Expr = inv(Expr1)}; {Expr = Expr1}), simple(Expr1).
simple( Expr ) -->  [lp], !, arithmeticExpr(Expr), [rp] ; atomic(Expr).

atomic( Expr) --> [num(Number)],!, {Expr = num(Number)};procedureCall(Expr),!;[variable(Name)],!,{Expr = variable(Name)}.
 
logicExpr(Expr) --> con(Expr1), !, logicExpr(Expr1, Expr).
logicExpr(Acc, Expr) --> [or],!, con(Expr1), {Acc1 = or(Acc, Expr1)}, arithmeticExpr(Acc1, Expr).
logicExpr(Acc,Acc) --> [].

con(Expr) --> war(Expr1), !, con(Expr1,Expr).
con(Acc, Expr) --> [and], !, war(Expr1), {Acc1 = and(Acc, Expr1)}, con(Acc1, Expr).
con(Acc, Acc) --> [].

war(Expr) --> ([not], !, {Expr = not(Expr1)}; {Expr = Expr1}), rel(Expr1).

rel(Expr) --> arithmeticExpr(Left),!, relOp(Op), arithmeticExpr(Right),{Expr =..[Op, Left, Right]}.
rel(Expr) --> [lp], !, logicExpr(Expr), [rp].

relOp(eq) --> [eq],!.  
relOp(diff) --> [diff], !.
relOp(less) --> [less], !.
relOp(sless) --> [sless], !.
relOp(more) --> [more], !.
relOp(smore) --> [smore], !.



%Change names of Variables to distinct ones




%For most
%       In  Out     In        In               Out         Out        In             In                       Out        In 
%unfold(AST,NewAST, Position, FirstFreeNumber, LastNumber, Variables, LastVariables, LastCallByNameVariables, Functions, LastFunctions)

%For instructions
%       in         out     in        in         in                   in  
%unfold(Instrukcje,NewAST, Position, Variables, CallByNameVariables, Functions).

unfold(program(_, Deklaracje, instrukcje(Instrukcje)),NewAST, Position, FirstFreeNumber, LastNumber, Variables, LastVariables, LastCallByNameVariables, Functions, LastFunctions) :-
	!,
	unfold(Deklaracje,_     , Position, FirstFreeNumber, LastNumber, Variables, LastVariables, LastCallByNameVariables, Functions, LastFunctions ),
	unfold(Instrukcje,NewAST, Position, Variables, LastCallByNameVariables, Functions).



unfold(deklaracje(Vars, Proc),_, Position, FirstFreeNumber, LastNumber, Variables, LastVariables, LastCallByNameVariables, Functions, LastFunctions) :-
	!,
	addVariables(Vars,Position, FirstFreeNumber, LastNumberAfterDeclaration, MidVariables, LastVariables),
	addFunctions(Proc,Position, LastNumberAfterDeclaration, LastNumber, Variables, MidVariables,  LastCallByNameVariables, Functions, LastFunctions ).


unfold([],[],_,_,_,_) :- !.
unfold([Instrukcja|Rest],[Modified|NewAST], Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Instrukcja,Modified, Position, Variables, CallByNameVariables, Functions),
	unfold(Rest, NewAST, Position, Variables, CallByNameVariables, Functions).


unfold(assign(Left, Right),assign(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(if(Expr, Instr, Else),if(NExpr,NInstr, NElse), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Expr,NExpr, Position, Variables, CallByNameVariables, Functions),
	unfold(Instr,NInstr, Position, Variables, CallByNameVariables, Functions),
	unfold(Else,NElse, Position, Variables, CallByNameVariables, Functions).

unfold(while(Expr, Instr), while(NExpr, NInstr), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Expr,NExpr, Position, Variables, CallByNameVariables, Functions),
	unfold(Instr,NInstr, Position, Variables, CallByNameVariables, Functions).


unfold(call(variable(Name), TrueArgs, ValArgs), call(variable(Number), UnfoldedTrueArgs, UnfoldedValArgs), Position, Variables, CallByNameVariables ,Functions) :-
	!,
	findFunction(variable(Name), Position, Functions, variable(Number)),
	unfold(TrueArgs, UnfoldedTrueArgs,  Position, Variables, CallByNameVariables, Functions),
	unfold(ValArgs, UnfoldedValArgs,  Position, Variables, CallByNameVariables, Functions).

unfold(return(Expr), return(NExpr), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Expr,NExpr, Position, Variables, CallByNameVariables, Functions).

unfold(read(variable(Name)), read(variable(Number)), Position, Variables, CallByNameVariables, _) :-
	!,
	findVariable(variable(Name), Position, Variables, CallByNameVariables, variable(Number)).

unfold(write(Expr), write(NExpr), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Expr,NExpr, Position, Variables, CallByNameVariables, Functions).

unfold(variable(Name), variable(Number), Position, Variables, CallByNameVariables, _) :-
	!,
	findVariable(variable(Name), Position, Variables, CallByNameVariables, variable(Number)).

unfold(plus(Left, Right),plus(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(minus(Left, Right),minus(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(mult(Left, Right),mult(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(mod(Left, Right),mod(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(div(Left, Right),div(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(or(Left, Right),or(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(and(Left, Right),and(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).


unfold(eq(Left, Right),eq(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(diff(Left, Right),diff(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).


unfold(less(Left, Right),sless(minus(NLeft,num(1)),NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(sless(Left, Right),sless(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(more(Left, Right),smore(NLeft,minus(NRight,num(1))), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(smore(Left, Right),smore(NLeft,NRight), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Left,NLeft, Position, Variables, CallByNameVariables, Functions),
	unfold(Right,NRight, Position, Variables, CallByNameVariables, Functions).

unfold(inv(Expr), inv(NExpr), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Expr,NExpr, Position, Variables, CallByNameVariables, Functions).

unfold(not(Expr), not(NExpr), Position, Variables, CallByNameVariables, Functions) :-
	!,
	unfold(Expr,NExpr, Position, Variables, CallByNameVariables, Functions).

unfold(num(Number), num(Number), _, _ , _, _).


addVariables([],_,Number,Number,Variables,Variables) :- !.
addVariables([variable(Name)|Rest], Position, FirstFreeNumber, LastNumber, [New|Variables], LastVariables ) :-
	New = variable(FirstFreeNumber,Position, variable(Name) ),
	NewNumber is FirstFreeNumber + 1,
	addVariables(Rest, Position, NewNumber, LastNumber, Variables, LastVariables).

addFunctions([],_, Number, Number, Variables, Variables, _, Functions, Functions) :- !.
addFunctions( [ fun(variable(Name), TrueArgs, ValArgs,Deklaracje, Instrukcje)|Rest], Position, FirstFreeNumber, LastNumber, Variables, LastVariables, LastCallByNameVariables, [New|Functions], LastFunctions) :-
	!,
	New = fun(FirstFreeNumber, ProcessedTrueArgs, ProcessedValArgs, AST, variable(Name), Position),
	NewNumber is FirstFreeNumber + 1,
	changeTrue(TrueArgs,ProcessedTrueArgs, [FirstFreeNumber|Position]),
	changeValue(NewNumber, NumberAfterArgs, ValArgs, ProcessedValArgs,[FirstFreeNumber|Position]),
	append(ProcessedValArgs, LastVariables,NewVariables),
	append(ProcessedTrueArgs, LastCallByNameVariables, NewCallBN),
	unfold(program(variable(Name),Deklaracje,Instrukcje), AST, [FirstFreeNumber|Position],  NumberAfterArgs,MidNumber, MidVariables, NewVariables, NewCallBN, MidFunctions, LastFunctions ),
	addFunctions(Rest, Position, MidNumber, LastNumber, Variables, MidVariables, LastCallByNameVariables, Functions, MidFunctions ).	

changeTrue([], [], _) :- !.
changeTrue([variable(Name)|Rest], [ variable(_, Position, variable(Name) )|ProccessedRest ], Position ) :-
	changeTrue(Rest, ProccessedRest, Position).

changeValue(Number, Number, [], [], _  ) :- !.
changeValue(FirstFreeNumber, LastNumber, [variable(Name)|Rest], [New|ProccessedRest], Position) :-
	New = variable(FirstFreeNumber, Position, variable(Name)),
	NewNumber is FirstFreeNumber + 1,
	changeValue(NewNumber, LastNumber, Rest, ProccessedRest, Position).

findVariable(variable(Name), Position, Variables, CallByNameVariables, variable(Number)) :-
	(member( variable(Number, Position, variable(Name)), CallByNameVariables) ;member( variable(Number, Position, variable(Name)), Variables) ),!.
findVariable(variable(Name), [_|Position], Variables, CallByNameVariables, variable(Number)) :-
	findVariable(variable(Name), Position, Variables, CallByNameVariables, variable(Number)). 

findFunction(variable(Name), Position, Functions, variable(Number)) :-
	member( fun(Number, _, _, _, variable(Name), Position), Functions ),!.
findFunction(variable(Name), [_|Position], Functions, variable(Number)) :-
	findFunction(variable(Name), Position, Functions, variable(Number)).

%Clean - tworzy liste funkcji bez zbedynych informacji

clean([],[]) :- !.
clean([ fun(Number, ProcessedTrueArgs, ProcessedValArgs, AST, _, _)  |Rest], [ fun(Number, ProcessedTrueArgs, ProcessedValArgs, AST) |ProccessedRest]) :-
	clean(Rest, ProccessedRest).
	



/*

	Expand Function in place of calling

*/

insertAll([],Functions, Functions) :- !.
insertAll([ H|Rest], ListOfAllFunctions, NewListOfFunctions ) :-
	!,
	insertOne(H, ListOfAllFunctions, ListOfAllFunctionsWithUnfoldedH ),
	insertAll(Rest,ListOfAllFunctionsWithUnfoldedH,NewListOfFunctions).


insertOne(_, [], []) :- !.
insertOne(Function, [fun( Number, ProcessedTrueArgs, ProcessedValArgs, AST)|ListOfAllFunctions], [New|NewListOfFunctions]) :-
	!,
	findAndInsert(AST, NewAST, Function),
	New = fun(Number, ProcessedTrueArgs, ProcessedValArgs, NewAST),
	insertOne(Function, ListOfAllFunctions,NewListOfFunctions).

insertToBody([], AST, AST).
insertToBody([Function|Rest], AST, LastAST) :-
	findAndInsert(AST, NewAST, Function),
	insertToBody(Rest, NewAST, LastAST).


%findAndInsert(AST, NewAST, Function)



findAndInsert([],[],_) :- !.

findAndInsert([Instrukcja|Rest],[Modified|NewAST], Function) :-
	!,
	findAndInsert(Instrukcja,Modified, Function),
	findAndInsert(Rest, NewAST, Function).


findAndInsert(assign(Left, Right),assign(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(if(Expr, Instr, Else),if(NExpr,NInstr, NElse), Function) :-
	!,
	findAndInsert(Expr,NExpr, Function),
	findAndInsert(Instr,NInstr, Function),
	findAndInsert(Else,NElse, Function).

findAndInsert(while(Expr, Instr), while(NExpr, NInstr), Function) :-
	!,
	findAndInsert(Expr,NExpr, Function),
	findAndInsert(Instr,NInstr, Function).

%Insert
findAndInsert(call(variable(Name), TrueArgsAplication, ValArgsAplication), call(Name, AST),fun(Name, TrueArgs, ValArgs, FunAST)) :-
	!, % w tym miejscu tworzymy historie
	copy_term(fun(Name, TrueArgs, ValArgs, FunAST), fun(_, TrueArgsCopy, ValArgsCopy, FunASTCopy)),
	unifyTrueArgs( TrueArgsAplication, TrueArgsCopy),
	addValueAssign(ValArgsAplication, ValArgsCopy, AssignList),
	append(AssignList, FunASTCopy, AST).

%Call of another function
findAndInsert(call(variable(Name), TrueArgs, ValArgs), call(variable(Name), TrueArgsWithInsertedFunction, ValArgsWithInsertedFunction), Function) :-
	!,
	findAndInsert(TrueArgs,TrueArgsWithInsertedFunction, Function),
	findAndInsert(ValArgs, ValArgsWithInsertedFunction, Function).

%Call of expanded function
findAndInsert(call(Name, AST), call(Name, NewAST), Function) :-
	!,
	findAndInsert(AST, NewAST, Function).


findAndInsert(return(Expr), return(NExpr), Function) :-
	!,
	findAndInsert(Expr,NExpr, Function).

findAndInsert(read(variable(Number)), read(variable(Number)), _) :-
	!.

findAndInsert(write(Expr), write(NExpr), Function) :-
	!,
	findAndInsert(Expr,NExpr, Function).

findAndInsert(variable(Number), variable(Number), _) :-
	!.

%Same as always
findAndInsert(plus(Left, Right),plus(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(minus(Left, Right),minus(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(mult(Left, Right),mult(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(mod(Left, Right),mod(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(div(Left, Right),div(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(or(Left, Right),or(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(and(Left, Right),and(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).


findAndInsert(eq(Left, Right),eq(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(diff(Left, Right),diff(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(less(Left, Right),less(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(sless(Left, Right),sless(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(more(Left, Right),more(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(smore(Left, Right),smore(NLeft,NRight), Function) :-
	!,
	findAndInsert(Left,NLeft, Function),
	findAndInsert(Right,NRight, Function).

findAndInsert(inv(Expr), inv(NExpr), Function) :-
	!,
	findAndInsert(Expr,NExpr, Function).

findAndInsert(not(Expr), not(NExpr), Function) :-
	!,
	findAndInsert(Expr,NExpr, Function).

findAndInsert(num(Number), num(Number), _).


unifyTrueArgs([],[]) :- !.
unifyTrueArgs([Right|TrueArgsAplication], [variable(X, _,_)|TrueArgs]) :-
	!,
	X = Right,
	unifyTrueArgs(TrueArgsAplication,TrueArgs).

addValueAssign([],[],[]) :- !.
addValueAssign([Right|ValArgsAplication], [variable(Number, _, _)|ValArgs], [New|AssignList]) :-
	!,
	New = assign(variable(Number), Right),
	addValueAssign(ValArgsAplication,ValArgs,AssignList) .


%Changes AST to instructions for processor

numToHex(Adress, HEX) :-
	N1 is Adress mod 16,
	N2 is (Adress div 16) mod 16,
	N3 is (Adress div 256) mod 16,
	N4 is Adress div 4096,
	hex(N1, H1),
	hex(N2, H2),
	hex(N3, H3),
	hex(N4, H4),
	HEX = [H4,H3,H2,H1].

hex(0,0).
hex(1,1).
hex(2,2).
hex(3,3).
hex(4,4).
hex(5,5).
hex(6,6).
hex(7,7).
hex(8,8).
hex(9,9).
hex(10,a).
hex(11,b).
hex(12,c).
hex(13,d).
hex(14,e).
hex(15,f).

getAdress(X, Y) :-
	number(X),!, Y=X.
getAdress(variable(X),Y) :-
	getAdress(X,Y).



%     in   in               out         in            out       out
%comp(AST, FirstFreeNumber, LastNumber, ReturnAdress, Compiled, TailCompiled)

comp([],Number,Number, _,_,Tail,Tail) :-
	!.

comp([Instr|Rest], FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Instr, FirstFreeNumber, NumberAfterFirstInstr,StackNumber, ReturnAdress, Compiled, TailOfPrev),
	comp(Rest, NumberAfterFirstInstr, LastNumber,StackNumber, ReturnAdress, TailOfPrev, TailCompiled).

comp(assign(VAR,Right), FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Right, FirstFreeNumber, NumberAfterRight,StackNumber, ReturnAdress, Compiled, TailOfRight),
	%now i have value of Right in Acc
	getAdress(VAR, Adress),
	numToHex(Adress, Hex),
	%After SWAPA Right will be in AR
	%After Const in Acc I will have address of variable
	%After SWAPA i have value in ACC Right in AR have addres
	%Store saves right value in HEX
	%swapA const swapA store HEX 
	LastNumber is NumberAfterRight + 2,
	TailOfRight = [[4,9,4,3],Hex|TailCompiled].
 



comp(if(Expr, Instr, Else),FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Expr, FirstFreeNumber, NumberAfterExpr,StackNumber, ReturnAdress, Compiled, TailOfExpr),
	%if zero jump to else
	TailOfExpr = [ [4,9,4,6], HexElseBegin|CompiledInstr],
	NewFirstNumber is NumberAfterExpr + 2,
	comp(Instr, NewFirstNumber, NumberAfterFirstInstr,StackNumber, ReturnAdress, CompiledInstr, TailOfInstr),
	%jump after else
	TailOfInstr = [ [9,8,0,0], HexEnd|CompiledElse ],
	ElseBegin is NumberAfterFirstInstr + 2,
	comp(Else, ElseBegin, LastNumber,StackNumber, ReturnAdress,CompiledElse, TailCompiled),
	numToHex(ElseBegin, HexElseBegin),
	numToHex(LastNumber,HexEnd).


comp(while(Expr, Instr), FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Expr, FirstFreeNumber, NumberAfterExpr, StackNumber, ReturnAdress, Compiled, TailOfExpr),
	%if zero jump after end
	TailOfExpr = [ [4,9,4,6], HexEnd|CompiledInstr],
	NewFirstNumber is NumberAfterExpr + 2,
	comp(Instr, NewFirstNumber, NumberAfterFirstInstr,StackNumber, ReturnAdress, CompiledInstr, TailOfInstr),
	%jump to begining and another computation of expression
	LastNumber is NumberAfterFirstInstr + 2,
	TailOfInstr = [[9,8,0,0],HexBegin|TailCompiled],
	numToHex(FirstFreeNumber,HexBegin),
	numToHex(LastNumber, HexEnd).


comp(call(Adress, AST), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(AST, FirstFreeNumber, NumberAfterCall, StackNumber, [ (Adress, ThisReturn)|ReturnAdress], Compiled, TailOfCall),
	%return makes jump with value in adres
	numToHex(NumberAfterCall, ThisReturn),
	numToHex(Adress, Hex),
	% const swapA load nop  Hex
	% After reading i have in Acc value returned by function
	LastNumber is NumberAfterCall + 2,
	TailOfCall = [[9,4,2,0],Hex|TailCompiled].


comp( return(Expr), FirstFreeNumber, LastNumber, StackNumber, [(Adress, MyReturn)|ReturnAdress], Compiled, TailCompiled  ) :-
	!,
	comp(Expr, FirstFreeNumber, NumberAfterExpr,StackNumber, [(Adress, MyReturn)|ReturnAdress], Compiled, TailOfExpr),
	numToHex(Adress, HexAdress),
	% i have in acc value of Expr
	% swapA const swapA store HexAdress
	% value Expr is written in HexAdress
	% const jump nop nop MyReturn 
	% reading jump address and jump
	LastNumber is NumberAfterExpr + 4,
	TailOfExpr = [ [4,9,4,3], HexAdress, [9,8,0,0], MyReturn|TailCompiled  ].


comp(read(variable(Adress)) ,FirstFreeNumber, LastNumber,_, _, Compiled, TailCompiled  )  :-
	!,
	numToHex(Adress, Hex),
	% 	read and store in Hex
	% const swapA const syscall Hex 0001
	%  store
	LastNumber is FirstFreeNumber + 4,
	Compiled = [ [9,4,9,1], Hex, [0,0,0,1], [3,0,0,0]|TailCompiled ].


comp(write(Expr),FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled  ) :-
	!,
	comp(Expr, FirstFreeNumber, NumberAfterExpr,StackNumber, ReturnAdress, Compiled, TailOfExpr),
	%mam expr w Acc teraz musze je wypisac
	% swapD const syscall nop 0002
	LastNumber is NumberAfterExpr + 2,
	TailOfExpr = [ [5,9,1,0], [0,0,0,2]|TailCompiled].


comp(variable(Adress), FirstFreeNumber, LastNumber,_, _, Compiled, TailCompiled   )  :-
	number(Adress), %Nie jest to zmienna przekazana przez nazwe
	!,
	%Laduje wartosc zmiennej do Acc
	numToHex(Adress, Hex),
	%const swapA load nop Hex
	LastNumber is FirstFreeNumber + 2,
	Compiled = [[9,4,2,0], Hex|TailCompiled].

comp(variable(Expr), FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled   )  :-
	!,
	comp(Expr, FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled   ).


comp(num(Number), FirstFreeNumber, LastNumber, _, _, Compiled, TailCompiled   )  :-
	!,
	%Laduje wartosc liczby do Acc
	numToHex(Number, Hex),
	%const nop nop nop Hex
	LastNumber is FirstFreeNumber + 2,
	Compiled = [[9,0,0,0], Hex|TailCompiled].


comp(plus(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Right jest w Acc
	%daj right do DR nastepnie wczytaj left z HexTemp i dodaj je do siebie
	%swapD const swapA load HexTemp add nop nop nop
	LastNumber is NumberAfterRight + 3,
	TailOfRight = [ [5,9,4,2], HexTemp, [a,0,0,0]|TailCompiled ].

comp(minus(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Right jest w Acc
	%daj right do DR nastepnie wczytaj left z HexTemp i dodaj je do siebie
	%swapD const swapA load HexTemp sub nop nop nop
	LastNumber is NumberAfterRight + 3,
	TailOfRight = [ [5,9,4,2], HexTemp, [b,0,0,0]|TailCompiled ].

comp(mult(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Right jest w Acc
	%daj right do DR nastepnie wczytaj left z HexTemp i dodaj je do siebie
	%swapD const swapA load HexTemp mul nop nop nop
	LastNumber is NumberAfterRight + 3,
	TailOfRight = [ [5,9,4,2], HexTemp, [c,0,0,0]|TailCompiled ].

comp(div(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Right jest w Acc
	%daj right do DR nastepnie wczytaj left z HexTemp i dodaj je do siebie
	%swapD const swapA load HexTemp div nop nop nop
	LastNumber is NumberAfterRight + 3,
	TailOfRight = [ [5,9,4,2], HexTemp, [d,0,0,0]|TailCompiled ].



comp(mod(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Right jest w Acc
	%daj right do DR nastepnie wczytaj left z HexTemp i dodaj je do siebie
	%po podzieleniu uzywam komendy e (tak jest uzyskany mod w przykladzie z tresci zadania)
	%swapD const swapA load HexTemp div const shift nop
	LastNumber is NumberAfterRight + 5,
	TailOfRight = [ [5,9,4,2], HexTemp, [d,5,9,5],[f,f,f,0], [e,0,0,0]|TailCompiled ].


comp(inv(Expr), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Expr, FirstFreeNumber, NumberAfterExpr,StackNumber, ReturnAdress, Compiled, TailOfExpr),
	%Mam w Acc Wartosc Expr teraz musze ja pomnozyc przez -1
	%swapD const mul nop -1 - mnozenie jest przemienne
	LastNumber is NumberAfterExpr + 2,
	TailOfExpr = [[5,9,c,0],[f,f,f,f]|TailCompiled].


comp(eq(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Right jest w Acc
	%daj right do DR nastepnie wczytaj left z HexTemp i odejmij
	%jezeli 0 to skocz do miejsca gdzie
	%swapD const swapA load HexTemp sub swapA const swapA adresJezeliZero branchZ nop nop nop
	%jezeli rozne to zaladuje 0 do data register i skocz do konca
	% const swapD const jump 0000 adreskonca
	% const swapD nop nop 0001
	% swapD nop nop nop
	IfAddr is NumberAfterRight + 8,
	End is NumberAfterRight + 10,
	numToHex(IfAddr,HexIfAddr),
	numToHex(End,HexEnd),
	LastNumber is NumberAfterRight + 11,
	TailOfRight = [ [5,9,4,2], HexTemp, [b,4,9,4],HexIfAddr, [6,0,0,0], [9,5,9,8], [0,0,0,0], HexEnd, [9,5,0,0], [0,0,0,1], [5,0,0,0]|TailCompiled ].


%To samo co wyzej tylko ze 1 gdy nieprawda
comp(diff(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	IfAddr is NumberAfterRight + 8,
	End is NumberAfterRight + 10,
	numToHex(IfAddr,HexIfAddr),
	numToHex(End,HexEnd),
	LastNumber is NumberAfterRight + 11,
	TailOfRight = [ [5,9,4,2], HexTemp, [b,4,9,4],HexIfAddr, [6,0,0,0], [9,5,9,8], [0,0,0,1], HexEnd, [9,5,0,0], [0,0,0,0], [5,0,0,0]|TailCompiled ].
%To samo co pierwsze tylko zamiast branchZ jest branchN
comp(sless(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	IfAddr is NumberAfterRight + 8,
	End is NumberAfterRight + 10,
	numToHex(IfAddr,HexIfAddr),
	numToHex(End,HexEnd),
	LastNumber is NumberAfterRight + 11,
	TailOfRight = [ [5,9,4,2], HexTemp, [b,4,9,4],HexIfAddr, [7,0,0,0], [9,5,9,8], [0,0,0,0], HexEnd, [9,5,0,0], [0,0,0,1], [5,0,0,0]|TailCompiled ].

%To samo co wyzej tylko left jest zmienione z right
comp(smore(Right,Left), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	IfAddr is NumberAfterRight + 8,
	End is NumberAfterRight + 10,
	numToHex(IfAddr,HexIfAddr),
	numToHex(End,HexEnd),
	LastNumber is NumberAfterRight + 11,
	TailOfRight = [ [5,9,4,2], HexTemp, [b,4,9,4],HexIfAddr, [7,0,0,0], [9,5,9,8], [0,0,0,0], HexEnd, [9,5,0,0], [0,0,0,1], [5,0,0,0]|TailCompiled ].


comp(and(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	%Jezeli Right jest zerem to skocz do wypisania adresJezeliZero
	%jezeli nie to zaladuj left i sprawdz czy jest zerem jezeli tak to skocz do adresJezeliZero
	%jezeli nie to wczytaj stala 1 i daj do rejestru danych
	% swapA const swapA branchZ adresJezeliZero
	% const swapA load swapA HexTemp const swapA branchZ nop adresJezeliZero
	% const swapD const jump 0001 adreskonca
	% const swapD nop nop 0000
	% swapD nop nop nop 
	IfAddr is NumberAfterRight + 9,
	End is NumberAfterRight + 11,
	LastNumber is NumberAfterRight + 12,
	numToHex(IfAddr, HexIfAddr),
	numToHex(End,HexEnd),
	TailOfRight = [ [4,9,4,6], HexIfAddr, [9,4,2,4], HexTemp, [9,4,6,0], HexIfAddr, [9,5,9,8], [0,0,0,1], HexEnd, [9,5,0,0],[0,0,0,0],[5,0,0,0]|TailCompiled].


%As earlier
comp(or(Left,Right), FirstFreeNumber, LastNumber, StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Left, FirstFreeNumber, NumberAfterLeft, StackNumber, ReturnAdress, Compiled, TailOfLeft),
	%Left jest w Acc
	%Zapisz wartosc left w pierwszej wolnej komorce pamieci na stercie
	numToHex(StackNumber, HexTemp),
	NewStackNumber is StackNumber - 1,
	%SWAPA const swapA Store HexTemp
	NewFreeNumber is NumberAfterLeft + 2,
	TailOfLeft = [[4,9,4,3], HexTemp|CompiledRight],
	comp(Right, NewFreeNumber, NumberAfterRight, NewStackNumber, ReturnAdress, CompiledRight, TailOfRight),
	IfAddr is NumberAfterRight + 9 +2,
	End is NumberAfterRight + 11 + 2,
	LastNumber is NumberAfterRight + 12 + 2,
	numToHex(IfAddr, HexIfAddr),
	numToHex(End,HexEnd),
	%dodatkowo z przodu
	%swapD const swapD sub 0001 (odjecie jedynki od Acc)
	TailOfRight = [ [5,9,5,b], [0,0,0,1], [4,9,4,6], HexIfAddr, [9,4,2,4], HexTemp, [9,4,6,0], HexIfAddr, [9,5,9,8], [0,0,0,0], HexEnd, [9,5,0,0],[0,0,0,1],[5,0,0,0]|TailCompiled].


comp(not(Expr),FirstFreeNumber, LastNumber,StackNumber, ReturnAdress, Compiled, TailCompiled) :-
	!,
	comp(Expr, FirstFreeNumber, NumberAfterExpr,StackNumber, ReturnAdress, Compiled, TailOfExpr),
	% swapA const swapA branchZ IfAddr 
	% const swapD const jump 0 End
	% const swapD nop nop 1
	% swapD nop nop nop
	IfAddr is NumberAfterExpr + 5,
	End is NumberAfterExpr + 7,
	LastNumber is NumberAfterExpr + 8,
	numToHex(IfAddr,HexIfAddr),
	numToHex(End,HexEnd),
	TailOfExpr = [ [4,9,4,6], HexIfAddr, [9,5,9,8], [0,0,0,0], HexEnd, [9,5,0,0], [0,0,0,1], [5,0,0,0]|TailCompiled]. 
	



%Po napisaniu comp

allocateMem(0, List, List) :- !.
allocateMem(N, List, [[0,0,0,0]|ResList]) :-
	NN is N - 1,
	allocateMem(NN, List, ResList).

