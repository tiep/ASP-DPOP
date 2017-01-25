:- module(master, [start_client/0,getX/0,run/1,run/0]).

:- use_module(library('linda/client')).
:- use_module(library(sets)).
:- use_module(library(lists)).
start_client:-
	see('tmpServer'),
	read(connectionInformation(Host,Port)),
	seen,
	linda_client(Host:Port).

run(Des) :- 	
	out(to(Des,master,[[],[],[],tree])),
	%shutdown_server,
	%getX.
	in(to(master,Name,done_tree)),
	out(time_starts),
	close_client,
	halt.

run:- 	
	%look_for_most_constraint(Des),	
	out(to(aA9,master,[[],[],[],tree,1])),
	%shutdown_server,
	%getX.
	in(to(master,Name,done_tree,NumAgent,NewX1,NewX2)),
	assert(list_agent(NewX1)),
	assert(topology(NewX2)),
	out(time_starts),
	assert(numberAgent(NumAgent)),
	%format('numberAgent(~w).\n',[NumAgent]),
	get_rank,	
	%format('---------------------------Client is  done here.\n',[]),
	get_up_down,
	shutdown_server,
	close_client,
	halt.

get_up_down:-
	get_up,
	%format('DONE GETUP\n',[]),
	get_down,
	%format('DONE GETDOWN\n',[]),
	process_up_down.

process_up_down:-	
	assert(start(1)),
	assert_num,
	assert(counting(1)),
	assert(total(0)),
	process_down_time,
	process_total_time,
	write_result.

write_result:-
	open('result.txt', write,S),
	topology(Topo),
	format(S,'Topo is ~w.\n',[Topo]),
	findall(delta_up(H,T), delta_up(H,T), ListUp),
	format(S,'Time up is ~w.\n',[ListUp]),
	findall(delta_down(H1,T1), delta_down(H1,T1), ListDown),
	format(S,'Time down is ~w.\n',[ListDown]),
	finalrunningtime(NewRunning),
	format(S,'Total running time is ~w.\n',[NewRunning]),
	findall(runn_up(H3,TimeH3), runningtime_up(H3,TimeH3), ListUp1),
	format(S,'running time up is ~w.\n',[ListUp1]),
	findall(runn_down(H4,TimeH4), runningtime_down(H4,TimeH4), ListDown1),
	format(S,'running time down is ~w.\n',[ListDown1]),
	close(S).


process_total_time:-
	topology(Topo),
	member(parent(Root,master), Topo),
	findall(T, X^delta_down(X,T), LT),
	max_member(Max, LT),
	delta_up(Root,TimeUp),
	NewRunning is TimeUp + Max,
	assert(finalrunningtime(NewRunning)).

process_down_time:-
	findall(R, rank(N,R), List),
	max_member(Max,List),
	calculate_time(Max).
	%total(Total),
	%format(S,'TOTAL RUNNING TIME IS:  ~w.\n',[Total]),	
	%close(S).

calculate_time(Max):-
	retract(counting(C)),
	numberAgent(NumAgent),
	%format('-----hehehe ~w , numagent ~w.\n',[C,NumAgent]),
	(C > Max -> true ; calculate_time1(C),NewC is C + 1, assert(counting(NewC)), calculate_time(Max)).

calculate_time1(C):-
	findall(A, rank(A,C), L),	
	(C==1 -> L=[Node], assert(delta_down(Node,0)) ; 
	delta_down(L)).

delta_down([]).
delta_down([H|T]):-
	topology(Topo),
	member(parent(H,P),Topo),
	delta_down(P,TimeP),
	runningtime_down(H,TimeH),
	NewTime is TimeP + TimeH,
	assert(delta_down(H,NewTime)),
	%format('delta_down(~w,~w).\n',[H,NewTime]),
	delta_down(T).

	
	
	

assert_num:-
	list_agent(NewX1),
	topology(NewX2),
	findall(A, (member(A,NewX1), \+ member(parent(_,A), NewX2)), LA),
	remove_dups(LA,LA1),
	assert(done(LA1)),
	assert_num(LA1),
	process_next.

process_next:-
	done(LC),
	topology(L),
	findall(A1, (member(B1,LC), member(parent(B1,A1), L)), LC1),
	remove_dups(LC1,LC2),
	%format('-------------->>>>>> ~w\n',[LC2]),	
	subtract(LC2,LC, Process),
	delete(Process,master,Process1),
	length(Process1,Length),
	%format('length is  ~w\n',[Length]),	
	(Length == 0 -> true ;	
		process_next(Process1),		
		process_next).
	
	

process_next([]).
process_next([H|T]):-
	topology(L),
	done(Done),
	findall(C,member(parent(C,H), L), LC),
	remove_dups(LC,LC1),
	%format('DONE IS ~w.\n',[Done]),
	(subset(LC1,Done) ->	
		append(Done,[H],NewLC),
		remove_dups(NewLC,NewLC1),
		retractall(done(_)),
		assert(done(NewLC1)),
		%format('------LC1 is ~w->>>>>>\n',[LC1]),
		findall(Ti, (member(A,LC1), delta_up(A,Ti)), LT),
		%format('------done is ~w->>>>>>\n',[LT]),
		max_member(Max,LT),
		runningtime_up(H,Time),
		NewTime is Time + Max,
		%format('delta_up(~w,~w).\n',[H,NewTime])
		assert(delta_up(H,NewTime)) ; true),
	process_next(T).
	

assert_num([]):-
	retract(start(X)),
	NewX is X + 1,
	assert(start(X)).
assert_num([H|T]):-
	start(X),
	assert(order(H,X)),
	runningtime_up(H,Time),
	assert(delta_up(H,Time)),
	%format('delta_up(~w,~w).\n',[H,Time]),
	assert_num(T).
	
	

get_up:-
	in(to(master,runningtime_up(Name,Up))),
	assert(runningtime_up(Name,Up)),
	%format('rank(~w,~w,~w).\n', [Name,Rank,Time]),
	findall((N-U), runningtime_up(N,U), L),
	length(L,Le),
	%format('numbernow(~w).\n',[Le]),
	%format('<<<<<<<<<<runningtime_up(~w,~w).\n',[Name,Up]),	
	numberAgent(NumAgent),
	(Le == NumAgent-> true ; get_up
	).

get_down:-
	in(to(master,runningtime_down(Name,Down))),
	assert(runningtime_down(Name,Down)),
	%format('rank(~w,~w,~w).\n', [Name,Rank,Time]),
	findall((N-D), runningtime_down(N,D), L),
	length(L,Le),
	%format('numbernow(~w).\n',[Le]),	
	%format('<<<<<<<<<<<runningtime_down(~w,~w).\n',[Name,Down]),
	numberAgent(NumAgent),
	Num is NumAgent - 1,
	(Le == Num-> true ; get_down
	).

get_rank:-
	in(to(master,rank(Name,Rank))),
	assert(rank(Name,Rank)),
	%format('rank(~w,~w).\n', [Name,Rank]),
	findall((N,R), rank(N,R), L),
	length(L,Le),
	%format('numbernow(~w).\n',[Le]),
	numberAgent(NumAgent),
	(Le == NumAgent-> true ; get_rank
	).

%write_rank(L):-
%	open('rank.txt',write,S),
%	format(S,'rank is ~w.\n',[L]),	
%	findall(R, rank(N,R,T), List),
%	max_member(Max,List),
%	%format('max rank is ~w.\n',[Max]),
%	assert(counting(1)),
%	assert(total(0)),
%	calculate_time(S,Max),
%	total(Total),
%	format(S,'TOTAL RUNNING TIME IS:  ~w.\n',[Total]),	
%	close(S).

%calculate_time(S,Max):-
%	retract(counting(C)),
%	numberAgent(NumAgent),
%	%format('-----hehehe ~w , numagent ~w.\n',[C,NumAgent]),
%	(C > Max -> true ; calculate_time(C,S),NewC is C + 1, assert(counting(NewC)), calculate_time(S,Max)).

%calculate_time(C,S):-
%	findall(T, N^rank(N,C,T), L),
%	max_member(MaxValue,L),
%	retract(total(T)),
%	NewT is T + MaxValue,
%	format(S,'max time at rank ~w is ~w.\n',[C,MaxValue]),
%	%format('max time at rank ~w is ~w.\n',[C,MaxValue]),
%	assert(total(NewT)).
	
	
	
	
getX:-
	statistics(walltime,[T_elapsed1,_]),
	in(to(master,Y,Z)), 
	%print('X= '),print(X),nl,
	print('Y= '),print(Y),nl,
	print('Z= '),print(Z),nl,
	print('----------------------------------------'),nl,
	statistics(walltime,[T_elapsed2,_]),
    	T is T_elapsed2 - T_elapsed1,
	print_statistics(T),
	getX.

print_statistics(T_elapsed):-   
    nl, nl,        
    write('runtime_'),
    write(T_elapsed), write('msec.'), nl.

look_for_most_constraint(Des):-
	bagof_rd_noblock((Name-Length), T^neighbor(Name,Length,T), LC),
	keys_and_values(LC,Keys,Values),
	max_member(LMax,Values),
	nth1(N,Values,LMax),
	nth1(N,Keys,Des).
	
	
