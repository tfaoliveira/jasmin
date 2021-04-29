require import AddN_ct.

(* the intuition is that we are trying to prove an equivalence
   between two executions of the add function where, if they start
   with the same leakage, they end up with the same leakage; *)
equiv add_ct :
  M.add ~ M.add : ={M.leakages} ==> ={M.leakages}.
proof.
(*proc tatic inlines the procedures *)
proc.
(* use sim tatic *)
sim.
(* everything is done *)
qed.

