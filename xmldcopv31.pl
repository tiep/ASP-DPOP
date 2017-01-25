:- use_module(library(lists)).
:- use_module(library(process)).
:- use_module(library(xml)).
:- use_module(library(file_systems)).

:- dynamic variable/2, constraint/3, agent/1, utility/3, owner/2, default/3, minmax/0.
:- set_prolog_flag(redefine_warnings, off).

prepare :-
	retractall(variable(_,_)),
	retractall(constraint(_,_,_)),
	retractall(agent(_)),
	retractall(utility(_,_,_)),
	retractall(default(_,_,_)),
	retractall(owner(_,_)),
	retractall(minmax),
	[asp_v3].


xml2asp(In, Out) :-
	prepare,
	load_structure(In,[element(_, _, X)],[]),
	processing(X, Out),
	%tiep(Out),
	halt.

processing(X, Out):-
	member(element(presentation,Pres,_),X),
	member(element(relations,_,Relations),X),
	member(element(agents,_,Agents),X),
	member(element(constraints,_,Constraints),X),
	member(element(domains,_,Domains),X),
	member(element(variables,_,Variables),X),
	process_presentation(Pres),
	process_agents(Agents, ListA),
	process_variables(Variables, ListV),
	process_domains(Domains, ListD),
	process_relations(Relations, ListR),
	process_constraints(Constraints, ListC),
        define_agents(ListA),
	define_variables(ListV, ListD),
	define_constraints(ListC),
	print('relation-----'),
	define_relations(ListR),
	print_problem(Out),
	print_list_agent.

print_list_agent:-
	open('list_agent.pl',write,S),
	findall(A, agent(A), LA),
	print_list_agent(LA,S),
	close(S).

print_list_agent([],_).
print_list_agent([H|T],S):-
	format(S,'agent(\'~w\').\n',[H]),
	print_list_agent(T,S).
print_problem(Out):-
	findall(A, agent(A), LA),
	print_problem_agents(Out, LA).

print_problem_agents(_, []).

print_problem_agents(Out, [Agent|LA]):-
	format('\nAgent a~w\n',[Agent]),
	atom_concat(Agent, '.pl', Suffix),
	atom_concat(Out, Suffix, FileName),
	atom_concat(Agent, '.asp', Suffix1),
	atom_concat(Out, Suffix1, FileName1),
	atom_concat(Out, Agent, FileName2),
	atomic_list_concat(XFile, '/', FileName2),
	last(XFile, FileName3),
	tell(FileName),
	(minmax -> format('minmax(true).\n',[]); format('minmax(false).\n',[])),
	format('agent(a~w).\n', [Agent]),
	format('filename(~w).\n', [FileName3]),
	findall(B, neighbor(Agent, B), LNeighbors1),
	list_to_set(LNeighbors1, LNeighbors),
	print_neighbor(LNeighbors),
	append(LNeighbors,[Agent],LNeighbors2),
	print_ownership(LNeighbors2),
	findall((Var,Range), (variable(Var,Range), owner(Agent, Var)), LVars),
	print_variables(LVars),
        findall((N,C,S), (constraint(N,C,S), appear(LVars,S)), CDesc),
        print_related_constraints(CDesc),
        format('owner(A,X):- table_info(_,A,X,_,_).\n',[]),
        format('begin(X,BV) :- table_info(_,_,X,BV,_).\n',[]),
        format('end(X,EV) :- table_info(_,_,X,_,EV).\n',[]),
        format('variable_symbol(X):- table_info(_,_,X,_,_).\n',[]),
	told,
	tell(FileName1),
	findall((N,Scope,U,Values), (constraint(N,Ref, Scope), utility(Ref, U, Values),
				        appear(LVars, Scope)), LCons1),
	findall((N,Scope,'-infinity',Values), (constraint(N,Ref,Scope),
					       appear(LVars, Scope),
					       utility(Ref, '-infinity', Values)), LCons2),
	subtract(LCons1,LCons2,LCons),
	print_constraints(LCons),
	print_bad_constraints(LCons2),
	

	%%%%%findall((N,Scope,U,Values), (constraint(N,Ref, Scope), utility(Ref, U, Values),
	%%			        appear(LVars, Scope)), LCons1),



	findall((Ref, NVar, Scope), (default(Name, NVar, _), constraint(Ref, Name,Scope),
					appear(LVars, Scope)), LDefaults),
	print_defaults(LDefaults),
	format('variable(X, Begin..End):- variable_symbol(X), begin(X, Begin), end(X, End).\n',[]),
	format('owner(X,Y):- table_info(_,X,Y,_,_).\n',[]),
	format('begin(X,Y):- table_info(_,_,X,Y,_).\n',[]),
	format('end(X,Y):- table_info(_,_,X,_,Y).\n',[]),
	format('variable_symbol(X):- table_info(_,_,X,_,_).\n',[]),
	format('#show table_info/5.\n',[]),
	%format('#hide.\n',[]),
	told,
	%%preprocess the default values
	atom_concat(FileName, '  ', FileName_t),
	atom_concat(FileName_t, FileName1, FileNameString),
	atom_concat(Out,Agent,Temp),
	solve_asp_models_given_stringfiles(FileNameString, Temp),
	Temp:model(Model),
	asp:list_predicate(Model,Set_Value),
	%atom_concat(FileName1,'.a',FileNamee),
	tell(FileName1),
	print_new_asp(Set_Value),
	format('variable(X, Begin..End):- variable_symbol(X), begin(X, Begin), end(X, End).\n',[]),
	format('owner(X,Y):- table_info(_,X,Y,_,_).\n',[]),
	format('begin(X,Y):- table_info(_,_,X,Y,_).\n',[]),
	format('end(X,Y):- table_info(_,_,X,_,Y).\n',[]),
	format('variable_symbol(X):- table_info(_,_,X,_,_).\n',[]),
	format('#show table_info/5.\n',[]),
	told,
	print_problem_agents(Out, LA).

print_new_asp([]).	
print_new_asp([H|T]):-
	format('~w.\n',[H]),
	print_new_asp(T).

appear([], _):- false.
appear([(H,_)|T], Scope) :-
	member(H, Scope) -> true; appear(T, Scope).

print_defaults([]).
print_defaults([(N, V, S)|LDefaults]):-
	 print_default_rule(N, S, V),
         print_defaults(LDefaults).

print_related_constraint(_, []).
print_related_constraint(C, [E|LMems]):-	
        format('constraint_member(c~w,v~w).\n',[C,E]),
	owner(Agent,E),	
	format('constraint_agent(c~w,a~w).\n',[C,Agent]),		
        print_related_constraint(C, LMems).

print_related_constraints([]).
print_related_constraints([(N,_,S)|CDesc]):-
        format('constraint(c~w).\n',[N]),
        print_related_constraint(N, S),
	%%check constraint for either min value or max value
	(length(S,1) -> 
		find_min_max(N,S);
		true		
	),
        print_related_constraints(CDesc).


find_min_max(N1,S):-
	findall((Values), (constraint(N,Ref, Scope), utility(Ref, U, Values), appear(LVars, Scope), N==N1, \+ Values == ['-infinity'], \+ Values == ['infinity']), LCons1),
	%length(LCons1,Length),
	%Length >= 1,
	max_member(Max,LCons1),
	Max = [Ma],
	min_member(Min,LCons1),
	Min = [Mi],
	S = [Var],
	format('max_value(v~w,~w).\n',[Var,Ma]),
	format('min_value(v~w,~w).\n',[Var,Mi]).

print_neighbor([]).
print_neighbor([N|LNeighbors]):-
	format('neighbor(a~w).\n',[N]),
	print_neighbor(LNeighbors).

print_ownership([]).
print_ownership([Ag|LNeighbors]):-
	findall(Var, owner(Ag, Var), LVars),
	print_ownerships(Ag, LVars),
	findall((Var1,Range), (variable(Var1,Range), owner(Ag, Var1)), LVars1),
	print_variables(LVars1),
	print_ownership(LNeighbors).

print_ownerships(_, []).
print_ownerships(Ag, [Var|LVars]):-
	format('owner(a~w,v~w).\n', [Ag,Var]),
	print_ownerships(Ag, LVars).

print_variables([]).
print_variables([(Var,Range)|LVars]):-
	format('variable_symbol(v~w).\n',[Var]),
	atomic_list_concat([Begin,End], '..', Range),
	format('begin(v~w,~w).\n',[Var,Begin]),
	format('end(v~w,~w).\n',[Var,End]),
	print_variables(LVars).

print_constraints([]).
print_constraints([(N,Scope, Util, Values)|LCons]):-
        (Util == '-infinity' ->
	     format('c~w(#inf, ',[N]);
	     (Util == infinity ->
	         format('c~w(#sup, ',[N]);
	         format('c~w(~w, ',[N, Util])
	      )
	),
	print_value_pairs(Scope, Values),
	format(').\n',[]),
	%%length(Scope,Length),
	%%check constraint for either min value or max value	
	%%(Length == 1 -> 
	%%	;
	%%)	
	print_constraints(LCons).

print_bad_constraints([]).
print_bad_constraints([(N,Scope, _, Values)|LCons]):-
	format('c~w(#inf,',[N]),
	print_value_pairs(Scope, Values),
	format(').\n',[]),
	print_bad_constraints(LCons).

print_value_pairs([], _).
print_value_pairs([_|T], [Value|Tail]):-
	format('~w',[Value]),
	length(T, Next),
	(Next > 0 -> print(',');true),
	print_value_pairs(T, Tail).


print_default_rule(N, Scope, VX):-
	% defined_xxx(V1,...,Vn):- xxx(U,V1,...,Vn), U != #inf, U != #sup.
	format('defined_c~w(',[N]),
	print_list_vars(Scope),
	format('):- c~w(U,',[N]),
	print_list_vars(Scope),
	format('), U != #inf, U != #sup.\n',[]),
	%format(').\n',[]),

	% value_cxxx(X,V1,...,Vn) :- default_xxx(X),not defined(V1,...,Vn),variable(v1,V1),...,variable(vn,Vn).
	format('value_c~w(X,',[N]),
	print_list_vars(Scope),
	%format('):- default_~w(X), not defined_~w(',[N,N]),
	format('):- default_c~w(X), not defined_c~w(',[N,N]),
	print_list_vars(Scope),
	format('), X != #inf, X != #sup,\n',[]),
	print_def_vars(Scope),
	% value_cxxx(X,V1,....,Vn) :- cxxx(X,V1,...,Vn).
        format('value_c~w(X,',[N]),
	print_list_vars(Scope),
	format('):- c~w(X,',[N]),
	print_list_vars(Scope),
	%format(').\n',[]),
	format('), X != #inf, X != #sup.\n',[]),	
	%%#show value_c.../
	length(Scope,Leng),
	NewLeng is Leng + 1,
	format('#show value_c~w/~w.\n',[N,NewLeng]),

	(   VX == '-infinity' ->
	    format('default_c~w(#inf).\n',[N]);
	    (
	        VX == infinity ->
	        format('default_c~w(#sup).\n',[N]);
	        format('default_c~w(~w).\n',[N,VX])
	    )
	).

print_list_vars([]).
print_list_vars([V|Scope]):-
	format('V~w', [V]),
	length(Scope, LS),
	(   LS > 0 -> format(',',[]); true),
	print_list_vars(Scope).

print_def_vars([]).
print_def_vars([V|Scope]):-
	format('variable(v~w, V~w)', [V,V]),
	length(Scope, LS),
	(   LS > 0 -> format(',',[]); format('.\n',[])),
	print_def_vars(Scope).

add_value(_, [], _).
add_value(R, [Entry|Table], Def):-
	%format(' *** Entry ~q \n', [Entry]),
	atomic_list_concat(VX, ':', Entry),
	%format(' *** VX ~q \n', [VX]),
	length(VX, NVX),
	(NVX > 1 ->
	  (
	     nth0(0, VX, Value),
	     nth0(1, VX, Scope),
	     atomic_list_concat(LLVars, ' ', Scope),
             subtract(LLVars, [''], LVars),
             assert(utility(R, Value, LVars)),
             add_value(R, Table, Value)
	  );
	  (
             nth0(0, VX, Scope),
             atomic_list_concat(LLVars, ' ', Scope),
             subtract(LLVars, [''], LVars),
             assert(utility(R, Def, LVars)),
             add_value(R, Table, Def)
	  )
	).

define_relations([]).
define_relations([(R, [pcdata(Values)], Default, Arity)|LR]):-
        %%% format('\nRelations ****** next ~q \n ~q\n',[Values, LR]),
        atom_codes(RR, R),
	%trace,
        (atom(Values) ->
	    define_relation(RR, Values);
	    (
             atom_codes(RValues, Values),
	    define_relation(RR, RValues)
	    )
	),
	%print('\n\n finish hhhhhhhhhaaaaaallllllffffffffff doing ----------------: \n'),
	atom_codes(RArity, Arity),
	(atom(Default) ->
             assert(default(RR, Default, RArity));
             (
	     atom_codes(RDefault, Default),
	     assert(default(RR, RDefault, RArity))
	     )
	),
	%print('\n\n finish doing ----------------: \n'),
	%notrace,
	define_relations(LR).

define_relation(R, Values):-
        %    format('\nNow  ****** Values ~q\n',[Values]),
	%print('\n\n before\n\n'),
	%trace,
	%atomic_list_concat([Entry|Table], '|', Values),
	testing(R,Values),
	%atom_chars(Values,ListValues),
	%append(C1,['|'|C2],ListValues),
	%print(C1),
	%print('\n\n after-----------------\n\n'),
        %    format('Entry ******  ~q    Table --- ~q\n',[Entry,Table]),
	%notrace,
	%
    %
    %trace,
    print('DONEDONE\n').
	%atomic_list_concat(VX, ':', Entry),
        %    format('VX ******  ~q\n',[VX]),
	%print('\n\n start doing : \n'),
	%print(Values),
	%print('\n\n'),
	%length(VX, NVX),
	%(NVX > 1 ->
	%     ( %% print('here -----------\n'),
	%       nth0(0, VX, VValue),
	%       nth0(1, VX, Scope),
	%       atomic_list_concat(LLVars, ' ', Scope),
    %           subtract(LLVars, [''], LVars),
    %           assert(utility(R, VValue, LVars)),
    %           add_value(R, Table, VValue)
    %         );
	%     (
    %           print('Syntax error\n'),
    %           fail
    %         )
	%).

testing(R,Values):-
	atom_chars(Values,ListValues),
	process_one_by_one(R,ListValues),
	print('DDDDDDDDDDDD\n').

process_one_by_one(R,LV):-
	member('|',LV),
	append(C1,['|'|C2],LV),
	\+ member('|',C1),
	append(CVValues,[':'|CScope],C1),
	atom_chars(VValues,CVValues),
	atom_chars(Scope,CScope),
	atomic_list_concat(LLVars, ' ', Scope),
	subtract(LLVars, [''], LVars),
        assert(utility(R, VValues, LVars)),

	%print('\nSSSTART\n'),	
	%print('utility('), print(R), print(','), print(VValues), print(','), print(LVars), print(').\n'),	
	%nl,nl,nl,
    %trace,
	process_one_by_one(R,C2,VValues).

process_one_by_one(R,LV):-
	\+ member('|',LV), %%there is will be only one element
	%append(C1,['|'|C2],LV),
	%\+ member('|',C1),
	append(CVValues,[':'|CScope],LV),
	atom_chars(VValues,CVValues),
	atom_chars(Scope,CScope),
	atomic_list_concat(LLVars, ' ', Scope),
	subtract(LLVars, [''], LVars),
        assert(utility(R, VValues, LVars)),

	%print('\nSSSTART\n'),	
	%print('utility('), print(R), print(','), print(VValues), print(','), print(LVars), print(').\n'),	
	nl,nl,nl.
    %trace,
	%process_one_by_one(R,C2,VValues).

process_one_by_one(R,LV,Value):-
	member('|',LV),	
	append(C1,['|'|C2],LV),
	\+ member('|',C1), %to be sure append clause retrieves the first element
    %trace,
	(append(CVValues,[':'|CScope],C1) ->
		atom_chars(VValues,CVValues),
		atom_chars(Scope,CScope),
		atomic_list_concat(LLVars, ' ', Scope),
		subtract(LLVars, [''], LVars),
        	assert(utility(R, VValues, LVars)) ;
		
		VValues = Value,	
		atom_chars(Scope,C1),	
             	atomic_list_concat(LLVars, ' ', Scope),
             	subtract(LLVars, [''], LVars),
            	assert(utility(R, VValues, LVars))
    ),     	

	%print('\nSSSTART\n'),	
	%print('utility('), print(R), print(','), print(VValues), print(','), print(LVars), print(').\n'),	
	%nl,nl,nl,
	process_one_by_one(R,C2,VValues).
	
	

process_one_by_one(R,C2,Value):-
	\+member('|',C2),	
	(append(CVValues,[':'|CScope],C2) ->
		atom_chars(VValues,CVValues),
		atom_chars(Scope,CScope),
		atomic_list_concat(LLVars, ' ', Scope),
		subtract(LLVars, [''], LVars),
        	assert(utility(R, VValues, LVars)) ;
		
		VValues = Value,	
		atom_chars(Scope,C2),	
             	atomic_list_concat(LLVars, ' ', Scope),
             	subtract(LLVars, [''], LVars),
            	assert(utility(R, VValues, LVars))
        ), 
	%print('\nSSSTART\n'),	
	%print('utility('), print(R), print(','), print(VValues), print(','), print(LVars), print(').\n'),
	nl,nl,nl.

	
define_agents([]).
define_agents([A|ListA]):-
         atom_codes(VX, A),
         assert(agent(VX)),
         define_agents(ListA).

define_constraints([]).
define_constraints([(Name, Scope, C, Arity)|ListC]):-
        atom_codes(VScope, Scope),
	atomic_list_concat(S, ' ', VScope),
        atom_codes(VC, C),
        atom_codes(VN, Name),
        assert(constraint(VN, VC, S)),
	define_constraints(ListC).

define_variables([],_).
define_variables([(Var,Dom,Agent)|ListV],ListD):-
        member((Dom,[pcdata(Range)]),ListD),
        atom_codes(VVar, Var),
        atom_codes(VRange, Range),
        assert(variable(VVar,VRange)),
	atom_codes(VAgent, Agent),
        assert(owner(VAgent,VVar)),
        define_variables(ListV,ListD).

process_agents(Agents, ListA):-
	findall(A, member(element(agent, [name=A], _), Agents), ListA).

process_variables(Variables, ListV):-
	findall((V,D,A),
               (
		  member(element(variable, VDA, _),
			 Variables),
                  member(name=V, VDA),
                  member(domain=D, VDA),
                  member(agent=A, VDA)
               ), ListV).

process_domains(Domains, ListD):-
	findall((D,R),
		   member(element(domain, [name=D,nbValues=_], R),
			  Domains), ListD).

process_relations(Relations, ListR):-
	findall((N,T,D,A),
                (member(element(relation, NDTA, T), Relations),
                 member(name=N, NDTA),
                 member(defaultCost=D, NDTA),
                 member(arity=A, NDTA)
                ), ListRD),
	findall((N,T,'#infimum',A), %% need to check here again. This is only for #infinum
                (member(element(relation, NDTA, T), Relations),
                 member(name=N, NDTA),
                 \+ member(defaultCost=D, NDTA),
                 member(arity=A, NDTA)
                ), ListRND),
	%length(ListRD,L1),
	%length(ListRND,L2),
	%print('-------------------.\n'),
	%print(L1),nl,print(L2),nl,
        append(ListRD, ListRND, ListR).

process_constraints(Constraints, ListC):-
	findall((N,S,R,A),
           (
		   member(element(constraint, SRA, _), Constraints),
                   member(name=N, SRA),
                   member(scope=S, SRA),
                   member(reference=R, SRA),
                   member(arity=A, SRA)
           ),
           ListC).

process_presentation(Pres):-
        %% format('Presentation ~q', [Pres]),
        member(maximize="true", Pres) -> assert(minmax); true.

neighbor(A, B):-
	agent(A), agent(B), \+ (A == B),
	owner(A, V1), owner(B, V2),
	constraint(_, _, Scope),
	member(V1, Scope),
	member(V2, Scope).

%%%%%%%%% swi to sicstus prolog predicates %%%%%%%%%%%%%


list_to_set(ListIn, ListOut):-
	remove_dups(ListIn, ListOut).

subtract(ListIn,LDel,LRest):-
	delete(ListIn,LDel,LRest).

atomic_list_concat(Out, Sep, Str):-
        atomic_list_concat_all(X, Sep, Str),
        findall(Y, (member(Y,X), atom_length(Y,L), L>0), Out).

atomic_list_concat_all([Str], Sep, Str):-
	\+ sub_atom(Str, _, _, _, Sep).

atomic_list_concat_all([First|Next], Sep, Str):-
	sub_atom(Str, B, _, A, Sep),
	atom_length(Sep, LSep),
	A1 is A + LSep, B1 is B+LSep,
	sub_atom(Str, 0, B, A1, First),
	sub_atom(Str, B1, A, 0, SStr),
	atomic_list_concat_all(Next, Sep, SStr).

load_structure(In, [element(_, _, X)], Opts):-
        see(In), capture(LIn), seen,
        xml_parse(LIn, xml(_,[element(_,_,X)]), [extended_characters(true)]).

capture(Rest) :-
	get_code(C),
	process(C,Rest).
process(-1,[]) :- !.
process(C, [C|R]) :-
	capture(R).

tiep(Out):-
	[list_agent],
	absolute_file_name('$SHELL', Shell),
	print('start_server.\n'),
	process_create(Shell, ['-c', ['timeout 10m sicstus -l server.pl --goal start_server. &']], [process(P1)]),
	process_wait(P1,exit(0)),
	print('finish_start_server.\n'),
	findall(A,agent(A),LA),
	start_client(Out,LA),
	start_master.

start_client(_,[]).
start_client(Out,[H|T]):-
	atom_concat(Out,H,Out1),
	print('start_client '), print(Out1), nl,
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['timeout 10m sicstus -l client3.pl --goal "consult([gen,' ,Out1,',asp_v3]),start_client." &']], [process(P1)]),
	process_wait(P1,exit(0)),
	print('finish_start_client '), print(Out1), nl,
	start_client(Out,T).

start_master :-
	print('start_master.\n'),
	agent(A),
	atom_concat(a,A,A1),
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['timeout 10m sicstus -l client.pl --goal "start_client,run."']], [process(P1)]),
	process_wait(P1,exit(0)),
	print('finish_start_master ').









