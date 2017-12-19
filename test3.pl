:- dynamic null/1, components/3, membertest/2.


foil_predicates([ null/1, components/3, membertest/2]).
foil_cwa(true).
foil_use_negations(false).        
foil_det_lit_bound(0).            

% Definitions of background predicates
null([]).

components([[a]], [a], []).
components([b, [a], d], b, [[a], d]).
components([[a],d], [a], [d]).
components([d], d, []).
components([e|f], e, f).

membertest(a,[a, b, [c]]).
membertest(b,[a, b, [c]]).
membertest([c],[a, b, [c]]).
membertest(b,[b, [c]]).
membertest([c],[b, [c]]).
membertest([c],[[c]]).

