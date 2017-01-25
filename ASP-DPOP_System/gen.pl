/*

Input:
  * set of decendants
  * set of ancestors
  * parent
  * children

Sicstus Version

*/

:- use_module(library(lists)).

:- dynamic parent/1,ancestor/1,decendant/1, owner/2, solution/3,min_value/2,max_value/2.
:- dynamic table_info/5, minmax/1.

:- multifile begin/2, end/2, owner/2, constraint/1, constraint_member/2, variable_symbol/1, parent/1, ancestor/1, decendant/1, solution/3,  table_info/5, minmax/1, min_value/2, max_value/2.

:- discontiguous begin/2, end/2, owner/2, constraint/1, constraint_member/2, variable_symbol/1, parent/1, ancestor/1, decendant/1, solution/3,  table_info/5, minmax/1, min_value/2, max_value/2.

:- set_prolog_flag(redefine_warnings, off).

%% Sicstus-Prolog specific code remove_duplicates

% list_to_set(L1, L2):- remove_dups(L1, L2).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% preparation
%%%%%%%%%%%%%%%%%%%%%%%%%%

minmax_string('max') :- minmax(true).                % maximization(true)
default_value('#infimum') :- minmax(true).

minmax_string('min') :- minmax(false).                % maximization(false)
default_value('#supremum') :- minmax(false).

/*
generate([In|Others]):-
	load_files(In,[]),
        load_files(Others, []),
	atomic_list_concat(X, '/', In),
	last(X, Last),
	append(Prefix, [Last], X),
	atomic_list_concat(Prefix, '/', Path),
	(parent(_) -> generate_non_root(Path); generate_root(Path)).
*/

generate :-
	(parent(_) -> generate_non_root(Path); generate_root(Path)).

generate_root(Path):-
	agent(Ag),
	findall(P, parent(P), []),
	findall(D, decendant(D), Decs),
	findall(V, (constraint_member(_,V),  owner(Ag, V)), ListVarSelf1),
	list_to_set(ListVarSelf1, ListVarSelf),
	%sort(ListVarSelfNS, ListVarSelf),
	%findall(C, constraint(C), Constrs),
	findall_constraint_ancestor_parent(Constrs),
	%format('List of decendants ~q\n', [Decs]),
	filename(File),
	create_filename(File, Path, FileName1),
	open(FileName1, write, Stream),
	set_output(Stream),
%	format('#hide.\n',[]),
	print_rules(Ag, ListVarSelf, [], Constrs, Decs),
	print_max(Ag, ListVarSelf, [], Constrs, Decs),
        print_out_table(Ag, ListVarSelf, [], Constrs, Decs),
	print_select(Ag, ListVarSelf, [], Constrs, Decs),
	format('#show solution/3.\n',[]),
	told.

create_filename(File, Path, FileName):-
/*
	atom_length(Path, LN),
	(   LN > 0 ->
	    (atom_concat(Path, '/', Path1), atom_concat(Path1, File, File1));
	     atom_concat(File, '', File1)
	),
*/
	atom_concat(File, '.add', FileName).


	
generate_non_root(Path):-
	agent(Ag),
	findall(A, ancestor(A), Anc),
	parent(Pa),
	findall(D, decendant(D), Decs1),
	findall(V, (constraint_member(_,V), (owner(Pa, V);
		         (owner(PB, V), member(PB,Anc)))), ListVarOther2),
	upward_variables(Ag, LVarsUp),
	append(ListVarOther2, LVarsUp, ListVarOther1),
	findall(V, (constraint_member(_,V),  owner(Ag, V)), ListVarSelf1),
	%findall(C, upward_constraint(C, Ag, Pa, Anc), Constrs1),
	findall_constraint_ancestor_parent(Constrs1),
	list_to_set(ListVarSelf1, ListVarSelf),
	%sort(ListVarSelfNS, ListVarSelf),
	list_to_set(ListVarOther1, ListVarOther),
	%sort(ListVarOtherNS, ListVarOther),
	list_to_set(Constrs1, Constrs),
	list_to_set(Decs1,Descs),
	%format('List of variables others ~q\n', [ListVarOther]),
	%format('List of variables self ~q\n', [ListVarSelf]),
	%format('List of constraints ~q\n', [Constrs]),
	%format('List of decendants ~q\n', [Descs]),
	filename(File),
	create_filename(File, Path, FileName1),
	open(FileName1, write, Stream),
	set_output(Stream),
%	format('#hide. \n',[]),
	length(ListVarSelf, NVarSelf),
	format('number_vars(~q).\n',[NVarSelf]),
	print_position(Ag, ListVarOther),
	print_rules(Ag, ListVarSelf, ListVarOther, Constrs, Descs), 
        print_max(Ag, ListVarSelf, ListVarOther, Constrs, Descs),
%	print_select(Ag, ListVarSelf, ListVarOther, Constrs, Descs),
	told,
	atom_concat(File, '.table', FileName2),
	open(FileName2, write, Stream2),
	set_output(Stream2),
%	format('#hide.\n',[]),
        print_out_table(Ag, ListVarSelf, ListVarOther, Constrs, Descs),
	print_select(Ag, ListVarSelf, ListVarOther, Constrs, Descs),
	format('#show solution/3.\n',[]),
	told.

findall_constraint_ancestor_parent(Constrs):-
	findall(X, (parent(X);ancestor(X)), L),
	findall(C,(constraint(C),constraint_agent(C,A), member(A,L)),LC),
	find_self_constraint(SelfConstraint),
	%print(LC),nl,
	%print(SelfConstraint),nl,
	append(SelfConstraint,LC,Constrs).

find_self_constraint(Self):-
	findall(C,constraint(C), LC),
	test_self_constraint(LC,Self).

test_self_constraint([],[]).
test_self_constraint([H|T],[H|T1]):-
	findall(A, constraint_agent(H,A), LA),
	list_to_set(LA,SetLA),
	agent(Agent),
	SetLA == [Agent],
	test_self_constraint(T, T1).

test_self_constraint([H|T],T1):-
	findall(A, constraint_agent(H,A), LA),
	list_to_set(LA,SetLA),
	agent(Agent),
	\+SetLA == [Agent],
	test_self_constraint(T, T1).
	

upward_constraint(C, Ag, P, Anc):-
	constraint(C),
	append([Ag,P],Anc,AllAgs),
	findall(V, (constraint_member(C,V), owner(O,V), \+ member(O, AllAgs)),LV),
	length(LV, 0).

upward_variables(Ag, LVarsUp):-
	findall(V, (table_info(A, _, V, _, _), decendant(A),
		    \+ owner(Ag, V)), LVarsUp).

print_position(_, []).
print_position(Ag, [V|ListVarOther]):-
	owner(Av, V),
	begin(V, BV),
	end(V, EV),
	format('table_info(~w,~w,~w,~w,~w).\n',[Ag,Av,V,BV,EV]),
	print_position(Ag,ListVarOther).

print_max(Ag, ListVarSelf, ListVarOther, Constrs, Descs):-
         %% table_min/max_agent(U, X1, ..., Xn) :- variable(x1, X1), ..., variable(xn,Xn),
         %%                  U = min/max {table_row(...)}
        minmax_string(Sminmax),
	format('table_~w_~w(U',[Sminmax,Ag]),
	length(ListVarOther, NOthers),
	(NOthers > 0 -> format(',',[]); true),
	print_vars(ListVarOther, 'VX'),
	format('):- \n',[]),
	%print_vars_value(ListVarOther),
	%%tiep modifies
	length(ListVarOther,LengListOther),
	(LengListOther =< 3 -> 
		print_vars_value(ListVarOther);	
		print_body_for_max(Ag, ListVarSelf, ListVarOther, Constrs, Descs,0)),
        format('\tU = #~w {\n',[Sminmax]),
	format('\t V: table_row_~w(V',[Ag]),
	%print_vars(ListVarSelf, 'VX'),
	(NOthers > 0 -> format(',',[]); true),
	print_vars(ListVarOther, 'VX'),
	format(')',[]),
	format('\n\t},U != #inf, U != #sup.\n',[]),
	NArgs is NOthers + 1,
        format('#show table_~w_~w/~w.\n',[Sminmax,Ag,NArgs]).

print_body_for_max(Ag, ListVarSelf, ListVarOther, Constrs, Descs,Mode):-
        length(Constrs, NCons),
	print_cell(Constrs, 0, 1),
	length(Descs, NDescs),
	(   NCons >0 -> (NDescs > 0 -> format(',\n',[]); true); true),
	print_cell_decendants(Descs),	
	format(',\n',[]).

print_out_table(Ag, ListVarSelf, ListVarOther, Constrs, Descs):-
	% out_table_row_aXXX(...) :-  table_row_aXXX(... ),
	%                table_min_XXX(U, VXvpt910).

        minmax_string(Sminmax),
	length(ListVarOther, NOthers),
	format('0 { out_table_row_~w(U, ',[Ag]),
	print_vars(ListVarSelf, 'VX'),
	format(')} :-\n ',[]),
	print_select_other(ListVarOther),

        format('\ttable_~w_~w(U ',[Sminmax,Ag]),
	(NOthers > 0 -> format(',',[]); true),
	print_vars(ListVarOther, 'VX'),
	format('), \n',[]),

        print_body(Ag, ListVarSelf, ListVarOther, Constrs, Descs,1),

	% #show out_table_row_aXXX/n

	length( ListVarSelf, NVars),
	New_NArgs1 is NVars + 1,
        format('#show out_table_row_~w/~w.\n',[Ag,New_NArgs1]), 

        % :- N = #count {out_table_row(...)}, N > 0. 
        % :- N = #count {out_table_row(...)}, N > 1. 

	format(':- 2 {out_table_row_~w(U, ',[Ag]),
	print_vars(ListVarSelf, 'VX'),
	format(')}.\n ',[]),
	format(':-  {out_table_row_~w(U, ',[Ag]),
	print_vars(ListVarSelf, 'VX'),
	format(')} 0.\n ',[]).



print_select(Ag, ListVarSelf, ListVarOther, Constrs, Descs):-
         minmax_string(Sminmax),
	length(ListVarSelf, NLSelf),
	print_select_one(Ag,ListVarSelf, ListVarSelf),
 
	% 1 { pick_table_row_aXXX(...) :  out_table_row_aXXX(... )} 1.

	format('pick_table_row_~w(U, ',[Ag]),
	print_vars(ListVarSelf, 'VX'),
	format(') :- \n ',[]),

        format('\tout_table_row_~w(U, ',[Ag]),
	print_vars(ListVarSelf, 'VX'),
	format('). \n',[]).

print_select_one(_, [], _).
print_select_one(Ag, [V|ListVarSelf], List):-
	format('\tsolution(~w,~w,X~w):- ',[Ag,V,V]),
	format('\tpick_table_row_~w(U,',[Ag]),
	print_vars(List, 'X'),
	format(').\n',[]),
	print_select_one(Ag, ListVarSelf, List).

print_select_other([]).
print_select_other([V|ListVarOther]):-
	owner(Ag, V),
	format('\tsolution(~w,~w,VX~w)',[Ag,V,V]),
	format(',\n',[]),
	print_select_other(ListVarOther).

print_rules(Ag, ListVarSelf, ListVarOther, Constrs, Descs):-
        print_head(Ag, ListVarOther), 
        print_body(Ag, ListVarSelf, ListVarOther, Constrs, Descs,0). 

print_head(Ag, ListVarOther):-
	format('table_row_~w(U',[Ag]), 
	length(ListVarOther, NOthers),
	(NOthers > 0 -> format(',',[]); true),
	print_vars(ListVarOther, 'VX'),
	format('):- \n',[]).
%%Mode 0 means we are writing for .add
%%Mode 1 means we are writing for .table
print_body(Ag, ListVarSelf, ListVarOther, Constrs, Descs,Mode):-
%	print_defined(Constrs),
%	length(Constrs, NCons),
%	(   NCons > 0 -> format(',\n',[]); true),
%	print_vars_value(ListVarOther),
%	format('\tU = #sum [\n',[]),
        length(Constrs, NCons),
	print_cell(Constrs, 0, 1),
	length(Descs, NDescs),
	(   NCons >0 -> (NDescs > 0 -> format(',\n',[]); true); true),
	print_cell_decendants(Descs),
	(Mode == 0 -> format(',\n\t U=',[]) ; format(',\n\t U==',[]) ),
        print_sum_constr(Constrs, 0), 
	(length(Constrs,0) -> format('0',[]); true),
        print_sum_decendants(Descs), 
	format(',\n',[]),
	print_different_constr(Constrs, 0),
	(length(Constrs,0) -> format('1==1',[]); true),
	print_different_decendants(Descs),
	format('.\n',[]).

print_defined([]).
print_defined([C|Constrs]):-
	findall(V, constraint_member(C, V), ListVars),
	%sort(ListVarsNS, ListVars),
	format('\tdefined_~w(',[C]),
	print_vars(ListVars, 'VX'),
	format(')',[]),
	length(Constrs, NC),
	(NC > 0 -> format(',\n', []); true),
		print_defined(Constrs).


print_vars([], _).
print_vars([V|ListVars], Pref):-
	format('~w~w',[Pref,V]),
	length(ListVars, N),
	(N > 0 -> format(',',[]); true),
	print_vars(ListVars, Pref).

print_comp_vars([], _, _).
print_comp_vars([V|ListVars], Pref1,Pref2):-
	format('~w~w != ~w~w',[Pref1,V,Pref2,V]),
	length(ListVars, N),
	(N > 0 -> format(', ', []); true),
	print_comp_vars(ListVars, Pref1,Pref2).


print_vars_value([]).
print_vars_value([V|ListVars]):-
	format('\tvariable(~w,VX~w),\n',[V,V]),
	print_vars_value(ListVars).


print_sum_constr([], _). 
print_sum_constr([R|Constrs], N):-
        format('V~q',[N]),
	length(Constrs, NC),
	(NC > 0 -> format('+',[]); true),
	Next is N + 1,
	print_sum_constr(Constrs, Next).
   
print_different_constr([], _).
print_different_constr([R|Constrs], N):-
	format('V~q != #inf, V~q != #sup',[N,N]),
	%format('1==1',[]),
	length(Constrs, NC),
	(NC > 0 -> format(',',[]); true),
	Next is N + 1,
	print_different_constr(Constrs, Next).


print_cell([], _, _).
print_cell([R|Constrs], N, Mode):-
        default_value(DString),
	(Mode == 1 -> format('\t~w(V~q,',[R,N]);
	   (Mode == 0 -> format('\t~w(~w,',[R,DString]); format('\tnot ~w(~w,',[R,DString]))),
	findall(M, constraint_member(R, M), ListVars),
	%sort(ListVarsNS, ListVars),
	print_vars(ListVars,'VX'),
	(Mode == 1 -> format(')',[]);
	   (Mode == 0 -> format(')',[]); format(')',[]))),
	%%print literals for min and max value
	check_min_max_vars(ListVars,'VX'),
	length(Constrs, NC),
	(NC > 0 -> format(',\n',[]); true),
	Next is N + 1,
	print_cell(Constrs, Next, Mode).

%% tiep wrote
check_min_max_vars([],_).
check_min_max_vars([H|T],Pre):-
	(min_value(H,Min) -> 
		format(', min_value(~w,Min~w), ~w~w >= Min~w',[H,H,Pre,H,H]);
		true	
	),
	(max_value(H,Max) -> 
		format(', max_value(~w,Max~w), ~w~w <= Max~w',[H,H,Pre,H,H]);
		true	
	),
	check_min_max_vars(T,Pre).

print_cell_ancestors([]).
print_cell_ancestors([Child|Descs]):-
	print_ancestor_value(Child),
	length(Descs, N),
	%(N > 0 -> format(',\n',[]); true),
	print_cell_ancestors(Descs).


print_ancestor_value(Child):-
        minmax_string(Sminmax),
	format('\ttable_~w_~w(VV~w,',[Sminmax,Child,Child]),
	findall(V, table_info(Child, _, V, _, _), LVars),
	%sort(LVarsNS, LVars),
        print_vars(LVars, 'VX'),
	format('),\n',[]).
%% done tiep wrote

print_sum_decendants([]).
print_sum_decendants([Child|Descs]):-         
	format('+VV~w',[Child]),
        print_sum_decendants(Descs).

print_different_decendants([]).
print_different_decendants([Child|Descs]):-
	format(',VV~w != #inf, VV~w != #sup',[Child,Child]),
	%format(',2==2',[]),
        print_different_decendants(Descs).


print_cell_decendants([]).
print_cell_decendants([Child|Descs]):-
	print_child_value(Child),
	length(Descs, N),
	(N > 0 -> format(',\n',[]); true),
	print_cell_decendants(Descs).


print_child_value(Child):-
         minmax_string(Sminmax),
	format('\ttable_~w_~w(VV~w,',[Sminmax,Child,Child]),
	findall(V, table_info(Child, _, V, _, _), LVars),
	%sort(LVarsNS, LVars),
        print_vars(LVars, 'VX'),
	format(')',[]),
	check_min_max_vars(LVars,'VX').


owner(A,X):- table_info(_,A,X,_,_).
begin(X,BV) :- table_info(_,_,X,BV,_).
end(X,EV) :- table_info(_,_,X,_,EV).
variable_symbol(X):- table_info(_,_,X,_,_).


%% Sicstus	%%

list_to_set(ListIn, ListOut):-
	remove_dups(ListIn, ListOut).

subtract(ListIn,LDel,LRest):-
	delete(ListIn,LDel,LRest).

atomic_list_concat(Out, Sep, Str):-
        (atom(Str) ->
            (
            atomic_list_concat_all(X, Sep, Str),
            findall(Y, (member(Y,X), atom_length(Y,L), L>0), Out)
            );
            (
              is_list(Out),
              inserting(Out, Sep, '', Str)
            )
         ).

inserting([], _, C, C).
inserting([H|T], Sep, C, Str):-
	atom_concat(C, H, CH),
	atom_concat(CH, Sep, CHS),
	inserting([H|T], Sep, CHS, Str).

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





















