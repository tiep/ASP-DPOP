:- module(server, [start_server/0]).
:- use_module(library('linda/server')).


start_server:-
	linda([(H:P)-start(H,P)]),
	print('DONE-------------DONE----------------DONE'),
	halt.

start(H,P):-
	write('Host: '),write(H),nl,
	write('Port: '),write(P),nl,
	tell('tmpServer'),
	format("connectionInformation(\'~w\', \'~w\').~n",[H,P]),
	told.


