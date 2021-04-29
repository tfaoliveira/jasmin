require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array1 Array2.
require import WArray8 WArray16.



module M = {
  proc add (a:W64.t Array1.t, b:W64.t Array1.t) : W64.t Array2.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var r:W64.t Array2.t;
    var i:int;
    var cf:bool;
    var  _0:bool;
    r <- witness;
    i <- 0;
    while (i < 1) {
      r.[i] <- a.[i];
      i <- i + 1;
    }
    r.[1] <- (W64.of_int 0);
    (aux_0, aux_1) <- addc_64 r.[0] b.[0] false;
    cf <- aux_0;
    r.[0] <- aux_1;
    i <- 1;
    while (i < 1) {
      (aux_0, aux_1) <- addc_64 r.[i] b.[i] cf;
      cf <- aux_0;
      r.[i] <- aux_1;
      i <- i + 1;
    }
    (aux_0, aux_1) <- addc_64 r.[1] (W64.of_int 0) cf;
     _0 <- aux_0;
    r.[1] <- aux_1;
    return (r);
  }
}.

