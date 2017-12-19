:- dynamic null/1, cons/3, membertest/2.

foil_predicates([ null/1, cons/3, membertest/2]).
foil_cwa(true).
foil_use_negations(true).       
foil_det_lit_bound(0).            

% Definitions of background predicates
null([]).

cons(a, [b, c],[a, b, c]).
cons(b, [c], [b,c]).
cons(c, [], [c]).

membertest(a,[a, b, c]).
membertest(b,[a, b, c]).
membertest(c,[a, b, c]).
membertest(b,[b, c]).
membertest(c,[b, c]).
membertest(c,[c]).

