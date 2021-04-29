require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array6 Array7.
require import WArray48 WArray56.



module M = {
  var leakages : leakages_t
  
  proc add (a:W64.t Array6.t, b:W64.t Array6.t) : W64.t Array7.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array7.t;
    var i:int;
    var cf:bool;
    r <- witness;
    leakages <- LeakFor(0,6) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 6) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([6]) :: leakages;
    r.[6] <- aux_0;
    leakages <- LeakAddr([0; 0]) :: leakages;
    (aux_1, aux_0) <- addc_64 r.[0] b.[0] false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakFor(1,6) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 6) {
      leakages <- LeakAddr([i; i]) :: leakages;
      (aux_1, aux_0) <- addc_64 r.[i] b.[i] cf;
      cf <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakCond(cf) :: LeakAddr([]) :: leakages;
    if (cf) {
      leakages <- LeakAddr([6]) :: leakages;
      aux_0 <- (r.[6] + (W64.of_int 1));
      leakages <- LeakAddr([6]) :: leakages;
      r.[6] <- aux_0;
    } else {
      
    }
    return (r);
  }
}.

