%:- module(client, [start_client/0,getX/0]).

:- use_module(library('linda/client')).
:- use_module(library(sets)).
:- use_module(library(lists)).
:- use_module(library(process)).

%----they are to look for and to assert name of this node and its neighbors 
assign_agent:-
	agent(X),
	%print(X),
	assert(node(X)).
assign_adjacent:-
	findall(X, neighbor(X), LX),
	%print(LX),
	assert(adjacent(LX)).

declare_neigbor_server:-
	adjacent(LX),
	node(Name),	
	length(LX,Length),
	out(neighbor(Name,Length,LX)).

%----they are to assert ancestors and decendants for this agent.


%--definition of ancestor with respect to list X.
ancestor(P,X) :- node(C),member(parent(C,P),X).
ancestor(P,X) :- member(parent(C,P),X), ancestor(C,X).

%--definition of decendant with respect to list X.	
decendant(D,X) :- node(P), member(parent(D,P),X).
decendant(D,X) :- member(parent(D,P),X), decendant(P,X).

assign_decendant(L):-
	%adjacent(A),
	findall(C,directchild1(C),LC),
	findall(P, (decendant(P,L), member(P, LC)), LP), %X is a real ancestor of this agent N if X is ancestor of N and X is neighbor of N
	assign_decendant2(LP).

assign_decendant2([]).
assign_decendant2([H|T]):-
	assert(decendant(H)), %assert for generate
	atom_concat('decendant(',H,D1),
	atom_concat(D1,')',D2),
	assert(pl:ruleLP(D2)), %assert for pl module
	assign_decendant2(T).

assign_ancestor(L):-
	adjacent(A),
	(parent(_) -> 
		parent(Parent),
		findall(P, (ancestor(P,L), member(P, A), \+ P == Parent), LP), %X is a real ancestor of this agent N if X is ancestor of N and X is neighbor of N
		assign_ancestor2(LP) ;
		true).

assign_ancestor2([]).
assign_ancestor2([H|T]):-
	assert(ancestor(H)), %assert for generate
	atom_concat('ancestor(',H,A1),
	atom_concat(A1,')',A2),
	assert(pl:ruleLP(A2)), %assert for pl module
	assign_ancestor2(T).

%---------- implement logics of this agent.

start_client:-
	%[gen,F,asp_v3],  %load basic files
	assign_agent, %this is to assert name for this agent
	assign_adjacent, %this is to assert adjacent lists for this agent	
	filename(File),
	assert(runningtime_up(0)),
	assert(runningtime_down(0)),
	%assert(newX2([])),
	atom_concat(File,'.pl',File1),
	%atom_concat(File,'.asp',File2),
	atom_concat(File,'_temp.pl',File11),
	%atom_concat(File,'_temp.asp',File21),
	%print('second version-----------------------------\n'),
	%trace,
	%load_MCS([File1,File2],[pl,asp],[File11,File21]),
	load_MCS([File1],[pl],[File11]),
	see('tmpServer'),
	read(connectionInformation(Host,Port)),
	seen,
	%statistics(walltime,[T_elapsed1,_]),
	%assert(timing(T_elapsed1)),
	linda_client(Host:Port),
	declare_neigbor_server,
	getX.
	

%data structure:
% X =[X1,X2,X3]
% X1 = List nodes which are opened already.
% X2 = List predicate parent/2. parent(a,b). b is parent of a.
% X3 = List predicate parent/2. parent(a,b). b is parent of a.
% X4 = tree,upward,downward,
% X5 = rank
getX:-
	node(Name),
	in(to(Name,From,Data)),
	%print('hehe.\n'),
	%trace,	
	%print('sent3.\n'),
	process_cl(From,Data),
	getX.

process_cl(From,Data):-
	Data = [X1,X2,X3,tree,Rank],
	%node(Node),
	%X4 = tree,
	building_the_tree(From,[X1,X2,X3,Rank]).

process_cl(From,Data):-
	Data = [X1,X2,X3,upward,Rank],
	%node(Node),
	%X4 = upward,
	start_count,
	processing_upward(From,[X1,X2,X3]).


process_cl(From,Data):-
	Data = [X1,X2,X3,downward,Rank],
	%node(Node),
	%X4 = downward,
	start_count,
	processing_downward(From,[X1,X2,X3]).

building_the_tree(From,[X1,X2,_,Rank]):-	
	node(Name),
	%print(Name), print('is processing the tree------------\n'),
	(Rank == 0 -> true; assert(rank(Rank))),
	rank(R),
	NRank is R + 1,	
	(member(Name,X1) -> NewX1 = X1; append(X1,[Name],NewX1)),%append my name into open list 
	(member(parent(Name,_), X2) -> 
		NewX2 = X2 ; 
		select_parent(From,X2,SelectParent),
		append(X2, [parent(Name, SelectParent)], NewX2),
		(SelectParent == master -> true;assign_parent(SelectParent))),
	(find_next(NewX1,Next) -> 
		assert(directchild(Next)),
		assert(directchild1(Next)),
		out(to(Next,Name,[NewX1,NewX2,[],tree,NRank])); 
		first_receive(F),
		(F == master -> length(NewX1,LeNewX1),write_tree(NewX2), out(to(master,Name,done_tree,LeNewX1,NewX1,NewX2)); 
			out(to(F,Name,[NewX1,NewX2,[],tree,0]))),
		assign_decendant(NewX2), 
		assign_ancestor(NewX2),
		start_time,
		(member(parent(_,Name), X2) -> true;
				start_count,processing_upward(_,[[],NewX2,[]])	
		)	
	).


start_time:-
	rd(time_starts),
	%statistics(walltime,[T_elapsed1,_]),
	%assert(timing(T_elapsed1)),
	node(Name).
	%print(Name), print('start_count_time-------\n').

start_count:-
	statistics(walltime,[T_elapsed1,_]),
	assert(timing(T_elapsed1)).

update_count_down:-	
	statistics(walltime,[T_elapsed2,_]),
	timing(T_elapsed1),
	T is T_elapsed2 - T_elapsed1,
	retract(runningtime_down(X)),
	NewX is X + T,
	assert(runningtime_down(NewX)),
	retractall(timing(_)).

update_count_up:-	
	statistics(walltime,[T_elapsed2,_]),
	timing(T_elapsed1),
	T is T_elapsed2 - T_elapsed1,
	retract(runningtime_up(X)),
	NewX is X + T,
	assert(runningtime_up(NewX)),
	retractall(timing(_)).

processing_upward(_,[_,NewX2,[]]):-	
	solve_first(NewX3), 
	update_count_up, %%%%%
	assert_to_table(NewX3),
	start_count, %%%%%
	first_receive(F),
	node(Name),
	update_count_up,
	out(to(F,Name,[[],NewX2,NewX3,upward,0])).

processing_upward(From,[_,NewX2,X3]):-
	assert_fact_to_filePL(X3),
	update_count_up, %%%%%
	save_variable(From,X3),
	start_count, %%%%%
	retract(directchild(From)),
	node(Name),
	%newX2(L),
	%length(L,L1),
	%length(NewX2,L2),
	%(L1 < L2 -> retract(newX2(L)), assert(newX2(NewX2)) ; true),
	(directchild(_) -> update_count_up; 		
		%newX2(N)
		solve_first(NewX3), 
		update_count_up, %%%%%
		assert_to_table(NewX3),
		start_count, %%%%%
		first_receive(F),
		update_count_up,
		(F==master -> write_sol(NewX3),send_result([],NewX2,NewX3),
				%shutdown_server,
				finish ; 
			     out(to(F,Name,[[],NewX2,NewX3,upward,0]))			
		)		
		
	).	

assert_to_table(NewX3):-
	filename(File),
	atom_concat(File,'.table',File1),	
	open(File1,append,S),
	write_set(S,NewX3),
	close(S).

processing_downward(From,[_,X2,X3]):-
	update_count_down, %%%%%
	assert_to_table(X3),
	start_count, %%%%%
	solve_second(NewX3),
	update_count_down,
	write_sol(NewX3),	
	send_result([],X2,NewX3),	
	finish.
	
send_result(X1,X2,NewX3):-
	node(Name),
	findall(C,directchild1(C),LC),
	send_to_list(X1,X2,NewX3,LC).
	
send_to_list(_,_,_,[]).
send_to_list(X1,X2,NewX3,[H|T]):-
	%print('sent5.\n'),
	node(Name),
	preprocess_solution(H,NewX3,Out),
	out(to(H,Name,[X1,X2,Out,downward,0])),
	%print_message_t(H,Name,Out),
	send_to_list(X1,X2,NewX3,T).
	
save_variable(From,X3):-
	findall(X,(member(M,X3),M=table_info(_,_,X,_,_)),LX),
	assert(variable_tmp(From,LX)).
	
preprocess_solution(H,NewX3,Out):-
	variable_tmp(H,LX),
	findall(A,(member(A,NewX3),A=solution(_,B,_),member(B,LX)),Out).

select_parent(From,X2,SelectParent):-
	SelectParent = From,
	assert(first_receive(From)).

update_neighbor_map(X1):-
	adjacent(Adj),	
	update_neighbor_map(X1,Adj).

update_neighbor_map(X1,[]):-
	node(Name),
	in(neighbor(Name,_,List)),
	subtract(List,X1,NewList),
	length(NewList,NewLength),
	out(neighbor(Name,NewLength,NewList)).

update_neighbor_map(X1, [H|T]):-
	in(neighbor(H,_,List)),
	subtract(List,X1,NewList),
	length(NewList,NewLength),
	out(neighbor(H,NewLength,NewList)),
	(member(H,X1) -> true; assert(neighbor_num_constraint(H,NewLength))),
	update_neighbor_map(X1,T).

find_next(X1,Next):-
	retractall(neighbor_num_constraint(_,_)),
	update_neighbor_map(X1),!,
	findall((N-L), neighbor_num_constraint(N,L), List),
	(length(List,0) -> 
			false; 
			keys_and_values(List,Keys,Values),
			max_member(LMax,Values),
			nth1(N,Values,LMax),
			nth1(N,Keys,Next)).
		
		
assign_parent(SelectParent):-
	assert(parent(SelectParent)),
	atom_concat('parent(',SelectParent,P1),
	atom_concat(P1,')',P),
	assert(pl:ruleLP(P)).
	
assert_to_filePL([]).
assert_to_filePL([H|T]):-
	assert_to_module(pl,H),
	%assert_string_fact_to_module(user,H),
	assert_to_filePL(T).
	
assert_fact_to_filePL([]).
assert_fact_to_filePL([H|T]):-
	assert_fact_to_module(pl,H),
	assert(user:H),
	assert_fact_to_filePL(T).
	
solve_first(Out):-
	%trace,
	%print('before generate.\n'),
	generate,!,
	%print('after generate.\n'),
	solve_first_second(Out).

solve_first_second(Out):-
	filename(File),
	%atom_concat(File,'.add',File1),
	%load_MCS([File1],[add],[add_asp]),
	%print('before count_up.\n'),
	update_count_up,
	prepare_solve_asp([pl],File), %prepare to solve for asp <--special case for calculating running time
	start_count,
	%print('after count_up.\n'),
	solve_asp_models_in_fact_already_prepared([pl],File),	
	File:model(Model),
	asp:list_predicate(Model,Out).
	%print(' Out is '),
	%print(Out).
	
	
solve_second(Out):-
	filename(File),
	%atom_concat(File,'.table',File1),
	atom_concat(File,'_solution',NewModel),
	%load_MCS([File1],[add],[add_asp]),
	%print('before count_down.\n'),
	%update_count_down,
	%prepare_solve_asp([pl],File), %prepare to solve for asp <--special case for calculating running time
	%start_count,
	%print('after count_down.\n'),
	solve_asp_models_given_files([File],NewModel),
	%print('after solving.\n'),
	NewModel:model(Model),
	asp:list_predicate(Model,Out).
	%print(' Out is '),
	%print(Out).

write_sol(Answer):-
	filename(File),
	atom_concat(File,'_sol.txt',File1),
	open(File1,write,S),
    write_set(S,Answer),
    close(S).
	%sed_file(File1).
	
write_tree(Answer):-
	open('graph.txt',write,S),
    write_set(S,Answer),
    close(S).
	%sed_file('graph.txt').
	
print_message_t(F,Name,NewX3):-
	atom_concat(Name,'_to_',Name1),
	atom_concat(Name1,F,F1),
	open(F1,write,S),
	write_set(S,NewX3),
	close(S).
	%sed_file(F1).
	
finish:-	
	%timing(T_elapsed1),
	%statistics(walltime,[T_elapsed2,_]),
	%T is T_elapsed2 - T_elapsed1,
	%runningtime(T),	
	%print_statistics(T),
	node(Name),
	rank(R),	
	out(to(master,rank(Name,R))),
	runningtime_up(Up),
	runningtime_down(Down),
	%format('CCCC--------runningtime_up(~w,~w).\n',[Name,Up]),
	%format('CCCC--------runningtime_down(~w,~w).\n',[Name,Down]),
	out(to(master,runningtime_up(Name,Up))),
	first_receive(F),
	(F == master -> true; out(to(master,runningtime_down(Name,Down)))),
	close_client,
	halt.

write_set(_,[]).
write_set(S,[H|T]):-
	write(S,H),
	write(S,'.\n'),
	write_set(S,T).
	
	
sed_file(FN):-
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['sed -i \'s/),/).\\n/g\' ', FN]], [process(P1)]),
	process_wait(P1,exit(0)).

print_statistics(T_elapsed):-   
    nl, nl,
    node(X),
    atom_concat(X,'_runtime.txt',X1),
    open(X1,write,S),       
    write(S,'runtime_'),
    write(S,T_elapsed), write(S,'msec.'), nl,
    close(S).

prepare_solve_asp(ListOfASPModules,OutputModule):-
	open(OutputModule,write,Stream_temp),
	write_modules_to_stream(ListOfASPModules,Stream_temp),
	close(Stream_temp).

write_modules_to_stream([],_).
write_modules_to_stream([H|T],Stream):-
	write_module_to_stream(H,Stream),
	write_modules_to_stream(T,Stream).

write_module_to_stream(H,Stream):-
	findall(Rule,H:ruleLP(Rule),Rules),
	write_rules_to_stream(Rules,Stream).
	
write_rules_to_stream([],_).
write_rules_to_stream([H|T],Stream):-
	write(Stream,H), write(Stream,'.\n'),
	write_rules_to_stream(T,Stream).
