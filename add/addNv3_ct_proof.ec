require import AddNv3_ct.

(*
if we use the same tactic as in the previous file, add_ct_proof, we will end up trying to prove this: 'forall &1 &2, ={M.leakages} => ={b, a, M.leakages}'

What this means, in practice, is that both inputs need to be declared as 'public', or the same, at the 'beginning' of the two executions.

* as a note: ={M.leakages} is the same as M.leakages{1} = M.leakages{2}

if a and b are public values then the equivalence can be updated into:
*)
equiv add_ct :
  M.add ~ M.add : ={a,b,M.leakages} ==> ={M.leakages}.
proof. proc; sim.
qed.

