require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array1 Array2.
require import WArray8 WArray16.



module M = {
  var leakages : leakages_t
  
  proc add (a:W64.t Array1.t, b:W64.t Array1.t) : W64.t Array2.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array2.t;
    var i:int;
    var cf:bool;
    var  _0:bool;
    r <- witness;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 1) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_0;
    leakages <- LeakAddr([0; 0]) :: leakages;
    (aux_1, aux_0) <- addc_64 r.[0] b.[0] false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakFor(1,1) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 1) {
      leakages <- LeakAddr([i; i]) :: leakages;
      (aux_1, aux_0) <- addc_64 r.[i] b.[i] cf;
      cf <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([1]) :: leakages;
    (aux_1, aux_0) <- addc_64 r.[1] (W64.of_int 0) cf;
     _0 <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_0;
    return (r);
  }
}.

