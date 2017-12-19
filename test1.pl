:- dynamic can_reach/2, linked_to/2.

foil_predicates([ can_reach/2, linked_to/2]).
foil_cwa(true).   		  
foil_use_negations(false).        
foil_det_lit_bound(0).            

% Definitions of background predicates

can_reach(0,1).
can_reach(0,2).
can_reach(0,3).
can_reach(0,4).
can_reach(0,5).
can_reach(0,6).
can_reach(0,8).
can_reach(1,2).
can_reach(3,2).
can_reach(3,4).
can_reach(3,5).
can_reach(3,6).
can_reach(3,8).
can_reach(4,5).
can_reach(4,6).
can_reach(4,8).
can_reach(6,8).
can_reach(7,6).
can_reach(7,8).

linked_to(0,1).
linked_to(0,3).
linked_to(1,2).
linked_to(3,2).
linked_to(3,4).
linked_to(4,5).
linked_to(4,6).
linked_to(6,8).
linked_to(7,6).
linked_to(7,8).


