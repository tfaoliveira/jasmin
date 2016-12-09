(* * Conversion to and from Coq language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open IL_Utils
open IL_Typing
open Arith
open Util

module F  = Format
module DE = Dmasm_expr
module DT = Dmasm_type
module DV = Dmasm_var
module Lex = ParserUtil.Lexing
module HT = Hashtbl

(* ** Conversions for strings, numbers, ...
 * ------------------------------------------------------------------------ *)

let rec pos_of_bi bi =
  let open Big_int_Infix in
  if bi <=! Big_int.unit_big_int then BinNums.Coq_xH
  else 
    let p = pos_of_bi (bi >>! 1) in
    if (bi %! (Big_int.big_int_of_int 2)) === Big_int.unit_big_int 
    then BinNums.Coq_xI p 
    else BinNums.Coq_xO p 

let rec bi_of_pos pos =
  let open Big_int_Infix in
  match pos with
  | BinNums.Coq_xH   -> Big_int.unit_big_int
  | BinNums.Coq_xO p -> (bi_of_pos p) <!< 1
  | BinNums.Coq_xI p -> ((bi_of_pos p) <!< 1) +! Big_int.unit_big_int

let int_of_pos pos = Big_int.int_of_big_int (bi_of_pos pos)

let pos_of_int pos = pos_of_bi (Big_int.big_int_of_int pos)

let coqZ_of_bi bi =
  let open Big_int_Infix in
  if bi === Big_int.zero_big_int then
    BinNums.Z0
  else if bi <! Big_int.zero_big_int then 
    BinNums.Zneg (pos_of_bi (Big_int.minus_big_int bi))
  else 
    BinNums.Zpos (pos_of_bi bi)
  
let bi_of_coqZ z =
  match z with
  | BinNums.Zneg p -> Big_int.minus_big_int (bi_of_pos p)
  | BinNums.Z0 -> Big_int.zero_big_int
  | BinNums.Zpos p -> bi_of_pos p

let ascii_of_char x = 
  let x = int_of_char x in
  let bit i = 
    if x lsr (7 - i) land 1 = 1 then Datatypes.Coq_true 
    else Datatypes.Coq_false in
  Ascii.Ascii(bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let char_of_ascii c = 
  let Ascii.Ascii(b7, b6, b5, b4, b3, b2, b1, b0) = c in
  let cv b i = if b = Datatypes.Coq_true  then 1 lsl i else 0 in
  let i =
    (cv b7 7) + (cv b6 6) + (cv b5 5) + (cv b4 4) + (cv b3 3) + (cv b2 2) + (cv b1 1) + (cv b0 0) 
  in
  char_of_int i

let string0_of_string s = 
  let s0 = ref String0.EmptyString in
  for i = String.length s - 1 downto 0 do
    s0 := String0.String (ascii_of_char s.[i], !s0) 
  done;
  !s0

let string_of_string0 s0 =
  let rec go acc s0 =
    match s0 with
    | String0.EmptyString   -> List.rev acc
    | String0.String (c,s0) ->
      go ((char_of_ascii c)::acc) s0
  in
  String.of_char_list (go [] s0)

let cbool_of_bool b =
  if b then Datatypes.Coq_true else Datatypes.Coq_false

let bool_of_cbool cb =
  match cb with
  | Datatypes.Coq_true  -> true
  | Datatypes.Coq_false -> false

let list_of_clist cl =
  let rec go acc cl =
    match cl with
    | Datatypes.Coq_nil -> List.rev acc
    | Datatypes.Coq_cons(c,cl) ->
      go (c::acc) cl
  in
  go [] cl

let clist_of_list l =
  let rec go acc l =
    match l with
    | [] -> acc
    | x::l ->
      go (Datatypes.Coq_cons(x,acc)) l
  in
  go Datatypes.Coq_nil (List.rev l)

let sword = DT.Coq_sword
let sbool = DT.Coq_sbool
let sint  = DT.Coq_sint

let sarr i = DT.Coq_sarr(pos_of_bi i)

(* ** Conversation info (required for lossless roundtrip)
 * ------------------------------------------------------------------------ *)

module CVI = struct
  
  type t = {
    ctr       : int ref;
    vargs     : (int,Vname.t * stor * Lex.loc * Lex.loc) HT.t;
    dargs     : (int,Lex.loc * bool) HT.t;
    iloc      : (int,Lex.loc) HT.t;
    ifcond    : (int,bool) HT.t; (* true if fcond *)
    fname     : (int,Fname.t) HT.t; (* function name for call *)
    fname_rev : (Fname.t,int) HT.t; (* function name for call *)
    ftable    : (Fname.t,unit fundef) HT.t;
  }

  let mk ftable =
    { ctr = ref 2;
      vargs     = Int.Table.create ();
      dargs     = Int.Table.create ();
      iloc      = Int.Table.create ();
      ifcond    = Int.Table.create ();
      fname     = Int.Table.create ();
      fname_rev = Fname.Table.create ();
      ftable    = ftable;
    }

  let new_ctr cvi =
    let k = !(cvi.ctr) in
    incr cvi.ctr;
    k

  let add_varg cvi v =
    let k = new_ctr cvi in
    HT.set cvi.vargs ~key:k ~data:(v.Var.name,v.Var.stor,v.Var.uloc,v.Var.dloc);
    k

  let get_varg cvi vinfo =
    let num = Big_int.int_of_big_int (bi_of_pos vinfo) in
    match HT.find cvi.vargs num with
    | Some(va) -> va
    | None     -> assert false

  let add_darg cvi d =
    let k = add_varg cvi d.d_var in
    let is_Ivar = match d.d_idx with Some(Ivar(_)) -> true | _ -> false in
    HT.set cvi.dargs ~key:k ~data:(d.d_loc,is_Ivar);
    k

  let get_darg cvi vinfo =
    let num = Big_int.int_of_big_int (bi_of_pos vinfo) in
    match HT.find cvi.vargs num, HT.find cvi.dargs num with
    | Some(va), Some(da) -> va,da
    | None,     _        -> assert false
    | _,        None     -> assert false

  let add_iloc cvi loc =
    let k = new_ctr cvi in
    HT.set cvi.iloc ~key:k ~data:loc;
    k

  let get_iloc cvi i =
    let num = Big_int.int_of_big_int (bi_of_pos i) in
    match HT.find cvi.iloc num with
    | Some(loc) -> loc
    | None      -> assert false

  let add_ifcond cvi k is_fcond =
    HT.set cvi.ifcond ~key:k ~data:is_fcond

  let get_ifcond cvi i =
    let num = Big_int.int_of_big_int (bi_of_pos i) in
    match HT.find cvi.ifcond num with
    | Some(loc) -> loc
    | None      -> assert false

  let get_fundef cvi fname =
    HT.find_exn cvi.ftable fname

  let add_fname cvi k fname =
    match HT.find cvi.fname_rev fname with
    | None ->
      HT.set cvi.fname ~key:k ~data:fname;
      HT.set cvi.fname_rev ~key:fname ~data:k;
      k
    | Some(k) -> k 

  let get_fname cvi k =
    let num = Big_int.int_of_big_int (bi_of_pos k) in
    HT.find_exn cvi.fname num

end

(* ** Types, pexpr, pcond, and fcond
 * ------------------------------------------------------------------------ *)

let cty_of_bty = function
  | Bool  -> sbool
  | U(64) -> sword
  | Int   -> sint
  | _     -> assert false

let cty_of_ty ty =
  match ty with
  | Bty(bt)               -> cty_of_bty bt
  | Arr(U(64),Pconst(bi)) -> sarr bi
  | _                     -> assert false

let ty_of_cty cty =
  match cty with
  | DT.Coq_sbool     -> tbool
  | DT.Coq_sword     -> tu64
  | DT.Coq_sint      -> tint
  | DT.Coq_sarr(pos) -> Arr(U(64), Pconst(bi_of_pos pos))

let sop2_of_pop_u64 po =
  match po with
  | Pplus  -> DE.Oadd
  | Pmult  -> DE.Omul
  | Pminus -> DE.Osub

let pop_u64_of_sop2 sop =
  match sop with
  | DE.Oadd -> Pplus
  | DE.Omul -> Pmult
  | DE.Osub -> Pminus
  | _       -> failwith "pop_u64_of_sop2: cannot map operation to pop_u64"
  
let cvar_of_var v =
  let vname = string0_of_string (string_of_int v.Var.num) in
  let vtype = cty_of_ty v.Var.ty in
  { DV.Var.vname = Obj.magic vname; DV.Var.vtype = vtype }

let var_of_cvar cvar (name,stor,uloc,dloc) =
  let num = int_of_string (string_of_string0 (Obj.magic cvar.DV.Var.vname)) in
  let ty = ty_of_cty cvar.DV.Var.vtype in
  { Var.name = name;
    Var.num  = num;
    Var.ty   = ty;
    Var.stor = stor;
    Var.uloc = uloc;
    Var.dloc = dloc;
  }

let rec cpexpr_of_pexpr cvi pe =
  let cpe = cpexpr_of_pexpr cvi in
  match pe with
  | Patom(Pvar(v))     ->
    let k = CVI.add_varg cvi v in
    DE.Pvar{DE.v_var=cvar_of_var v; DE.v_info=pos_of_int k}
  | Pbinop(po,pe1,pe2) ->
    DE.Papp2(sop2_of_pop_u64 po,cpe pe1,cpe pe2) 
  | Pconst bi ->
    DE.Pconst(coqZ_of_bi bi)
  | Patom(Pparam(_))   ->
    failwith "cpexpr_of_pexpr: parameters not supported"

let rec pexpr_of_cpexpr cvi pe =
  let pcp = pexpr_of_cpexpr cvi in
  match pe with
  | DE.Pvar(vi) ->
    let vargs = CVI.get_varg cvi vi.DE.v_info in
    Patom(Pvar(var_of_cvar vi.DE.v_var vargs))
  | DE.Papp2(sop,cpe1,cpe2) ->
    Pbinop(pop_u64_of_sop2 sop,pcp cpe1,pcp cpe2)
  | DE.Pconst(zi) ->
    Pconst(bi_of_coqZ zi)
  | DE.Pcast(_) -> failwith "pexpr_of_cpexpr: Pcast not supported"
  | DE.Pget(_)  -> failwith "pexpr_of_cpexpr: Pget not supported"
  | DE.Pload(_) -> failwith "pexpr_of_cpexpr: Pload not supported"
  | DE.Pnot(_)  -> failwith "pexpr_of_cpexpr: Pnot not supported"
  | DE.Pbool(_) -> failwith "pexpr_of_cpexpr: Pbool not supported"

let bop_to_csop2 = function
  | Pand -> DE.Oand
  | Por  -> DE.Oor

let sop2_to_bop = function
  | DE.Oand -> Pand
  | DE.Oor  -> Por
  | _       -> assert false

let mk_bop o cpc1 cpc2 =
 DE.Papp2(bop_to_csop2 o,cpc1,cpc2)
 
let mk_not cpc =
  DE.Pnot(cpc)

let mk_cmp cop cpe1 cpe2 =
  DE.Papp2(cop,cpe1,cpe2)

let mk_eq = mk_cmp DE.Oeq

let rec cpexpr_of_pcond cvi pc =
  let cpc = cpexpr_of_pcond cvi in
  let cpe = cpexpr_of_pexpr cvi in
  match pc with
  | Pbool(b)          -> DE.Pbool(cbool_of_bool b)
  | Pnot(pc)          -> mk_not(cpc pc)
  | Pbop(o,pc1,pc2)   -> mk_bop o (cpc pc1) (cpc pc2)
  | Pcmp(pop,pe1,pe2) ->
    let cpe1 = cpe pe1 in
    let cpe2 = cpe pe2 in
    begin match pop with
    | Peq  -> mk_cmp DE.Oeq   cpe1 cpe2
    | Plt  -> mk_cmp DE.Olt   cpe1 cpe2
    | Ple  -> mk_cmp DE.Ole   cpe1 cpe2
    | Pgt  -> mk_cmp DE.Ogt   cpe1 cpe2
    | Pge  -> mk_cmp DE.Oge   cpe1 cpe2
    | Pneq -> mk_cmp DE.Oneq  cpe1 cpe2
    end

let rec pcond_of_cpexpr vat pe =
  let pcp = pcond_of_cpexpr vat in
  let pep = pexpr_of_cpexpr vat in
  let open DE in
  match pe with
  | DE.Pbool(cb) -> IL_Lang.Pbool(bool_of_cbool cb)
  | DE.Pnot(cpc) ->
    IL_Lang.Pnot(pcp cpc)
  | Papp2((Oand|Oor) as o,cpc1,cpc2) ->
    Pbop(sop2_to_bop o,pcp cpc1, pcp cpc2)
  | DE.Papp2((Oeq|Oneq|Olt|Ole|Ogt|Oge) as cop,cpe1,cpe2) ->
    let pe1 = pep cpe1 in
    let pe2 = pep cpe2 in
    begin match cop with
    | Oeq  -> Pcmp(Peq,pe1,pe2)
    | Oneq -> Pcmp(Pneq,pe1,pe2)
    | Olt  -> Pcmp(Plt,pe1,pe2)
    | Ole  -> Pcmp(Ple,pe1,pe2)
    | Ogt  -> Pcmp(Pgt,pe1,pe2)
    | Oge  -> Pcmp(Pge,pe1,pe2)
    | Oand
    | Oor
    | Omul
    | Oadd
    | Osub -> failwith "impossible"
    end
  | Papp2((Oadd|Omul|Osub), _, _)
  |Pconst _
  |Pcast _
  |Pvar _
  |Pget(_, _)
  |Pload(_) -> failwith "pcond_pexpr: unsuppported operator"


let cpexpr_of_fcond cvi {fc_neg; fc_var} =
  let cpe_v = cpexpr_of_pexpr cvi (Patom(Pvar(fc_var))) in
  (if fc_neg then DE.Pnot(cpe_v) else cpe_v)

let fcond_of_cpexpr cvi cpe =
  let neg, cpe_v = 
    match cpe with
    | DE.Pnot(cpe_v) -> true, cpe_v
    | _              -> false, cpe
  in
  let v =
    match pexpr_of_cpexpr cvi cpe_v with
    | Patom(Pvar(v)) -> v
    | _              -> assert false
  in
  {fc_neg=neg; fc_var=v}

(* ** Sources and destinations
 * ------------------------------------------------------------------------ *)

let rval_of_sdest cvi sd =
  match sd.d_idx with
  | None ->
    let k = CVI.add_darg cvi sd in
    DE.Rvar({DE.v_info=pos_of_int k;DE.v_var=cvar_of_var sd.d_var})
  | Some(idx) ->
    let cpe =
      match idx with
      | Ipexpr(pe) -> cpexpr_of_pexpr cvi pe
      | Ivar(v)    -> cpexpr_of_pexpr cvi (Patom(Pvar(v)))
    in
    let k = CVI.add_darg cvi sd in
    DE.Raset({DE.v_info=pos_of_int k;DE.v_var=cvar_of_var sd.d_var}, cpe)

let rval_of_rdest cvi rd =
  match rd with
  | Sdest(sd)  -> rval_of_sdest cvi sd
  | Mem(sd,pe) ->
    if sd.d_idx<>None then (
      failwith "rval_of_rdest: memory base pointer cannot be array"
    ) else (
      let k = CVI.add_darg cvi sd in
      DE.Rmem(DE.{v_info=pos_of_int k; v_var=cvar_of_var sd.d_var}, cpexpr_of_pexpr cvi pe)
    )
let rval_of_dest cvi d =
  match d with
  | Rdest(rd) -> rval_of_rdest cvi rd
  | Ignore(l) ->
    let k = CVI.add_iloc cvi l in
    DE.Rnone(pos_of_int k)

let idx_of_cpexpr cvi is_Ivar idx =
  if is_Ivar then (
    let v =
      match idx with
      | DE.Pvar(v) ->
        let vargs = CVI.get_varg cvi v.DE.v_info in
        var_of_cvar v.DE.v_var vargs
      | _ ->
        assert false
    in
    Ivar(v)
  ) else (
    Ipexpr(pexpr_of_cpexpr cvi idx)
  )
      
let rdest_of_rval cvi rv =
  match rv with
  | DE.Rvar(cvar_i) ->
    let cvar = cvar_i.DE.v_var in
    let vi   = cvar_i.DE.v_info in
    let vargs,(dloc,_is_Ivar) = CVI.get_darg cvi vi in
    let d = { d_var=var_of_cvar cvar vargs; d_idx=None; d_loc=dloc } in
    Sdest(d)
  | DE.Raset(cvar_i,cpe) ->
    let cvar = cvar_i.DE.v_var in
    let vi = cvar_i.DE.v_info in
    let vargs,(dloc,is_Ivar) = CVI.get_darg cvi vi in
    let d = { d_var=var_of_cvar cvar vargs; d_idx=Some(idx_of_cpexpr cvi is_Ivar cpe); d_loc=dloc } in
    Sdest(d)
  | DE.Rmem(cvar_i,cpe) ->
    let cvar = cvar_i.DE.v_var in
    let vi = cvar_i.DE.v_info in
    let vargs,(dloc,_) = CVI.get_darg cvi vi in
    let sd = { d_var=var_of_cvar cvar vargs; d_idx=None; d_loc=dloc } in
    Mem(sd,pexpr_of_cpexpr cvi cpe)
  | DE.Rnone(_) ->
    failwith "sdest_of_rval: unexpected None"

let dest_of_rval cvi rv =
  match rv with
  | DE.Rnone(k) ->
    let l = CVI.get_iloc cvi k in
    Ignore(l)
  | _ -> Rdest(rdest_of_rval cvi rv)

let cpexpr_of_src cvi s =
  let cpe = cpexpr_of_pexpr cvi in
  match s with
  | Imm(_,pe) -> cpe pe
  | Src(Sdest(d)) ->
    let k = CVI.add_darg cvi d in
    let v = {DE.v_info=pos_of_int k; DE.v_var=cvar_of_var d.d_var} in
    begin match d.d_idx with
    | None -> DE.Pvar(v)
    | Some(idx) ->
      let cpe =
        match idx with
        | Ipexpr(pe) -> cpexpr_of_pexpr cvi pe
        | Ivar(v)    -> cpexpr_of_pexpr cvi (Patom(Pvar(v)))
      in
      DE.Pget(v,cpe)
    end
  | Src(_) -> assert false

let src_of_cpexpr cvi cpe =
  match cpe with
  | DE.Pvar(cvar_i) ->
    Src(rdest_of_rval cvi @@ DE.Rvar(cvar_i))

  | DE.Pget(cvar_i,cpe) ->
    let vargs,(darg,is_Ivar) = CVI.get_darg cvi cvar_i.DE.v_info in
    let sd =
      { d_var=var_of_cvar cvar_i.DE.v_var vargs;
        d_idx=Some(idx_of_cpexpr cvi is_Ivar cpe);
        d_loc=darg }
    in
    Src(Sdest(sd))

  | _ -> Imm(64,pexpr_of_cpexpr cvi cpe) (* FIXME: bitsize fixed *)

(* ** Operators
 * ------------------------------------------------------------------------ *)

let sopn_of_three_op top =
  match top with
  | O_Imul -> DE.Omuli
  | O_And  -> DE.Oland
  | O_Xor  -> DE.Oxor
  | O_Or   -> DE.Olor

let sopn_of_carry_op cop =
  match cop with
  | O_Add -> DE.Oaddcarry
  | O_Sub -> DE.Osubcarry

let sopn_of_op o =
  match o with
  | ThreeOp(top) -> sopn_of_three_op top
  | Umul         -> DE.Omulu
  | Carry(cop)   -> sopn_of_carry_op cop
  | Cmov(neg)    -> assert(not neg); DE.Oif
  | Shift(Left)  -> DE.Olsl
  | Shift(Right) -> DE.Olsr

let op_of_sopn top =
  match top with
  | DE.Oland     -> ThreeOp(O_And)
  | DE.Oxor      -> ThreeOp(O_Xor)
  | DE.Olnot     -> assert false
  | DE.Olor      -> ThreeOp(O_Or)
  | DE.Oaddcarry -> Carry(O_Add)
  | DE.Osubcarry -> Carry(O_Sub)
  | DE.Omulu     -> Umul
  | DE.Omuli     -> ThreeOp(O_Imul)
  | DE.Oif       -> Cmov(false)
  | DE.Olsl      -> Shift(Left)
  | DE.Olsr      -> Shift(Right)

(* ** Basic instructions, instructions, and statements
 * ------------------------------------------------------------------------ *)

let atag_of_assgn_type = function
  | Mv -> DE.AT_keep
  | Eq -> DE.AT_rename

let assgn_type_of_atag = function
  | DE.AT_keep   -> Mv
  | DE.AT_rename -> Eq
  | _            -> assert false

let rec cfundef_of_fundef _cvi _tin _tres _fd =
  undefined () 
  (*
  let dest_of_var v = {d_var=v;d_loc=Lex.dummy_loc;d_idx=None} in
  let src_of_var v = Src(dest_of_var v) in
  let rval_arg = rval_of_dests cvi (List.map ~f:dest_of_var fd.f_arg) in
  let cpe_res = cpexpr_of_srcs cvi (List.map ~f:src_of_var fd.f_arg) in
  let cmd = cmd_of_stmt cvi fd.f_body  in
  DE.FunDef(tin,tres,rval_arg,cmd,cpe_res)
  *)

and cinstr_of_base_instr cvi lbi =
  let k = CVI.add_iloc cvi lbi.L.l_loc in
  match lbi.L.l_val with
  | Assgn(d,s,aty) ->
    let atag = atag_of_assgn_type aty in
    let rd = rval_of_dest cvi d in
    let es = cpexpr_of_src cvi s in
    Some(k,DE.Cassgn(rd,atag,es))

  | Op(o,ds,ss) ->
    let ds = List.map ~f:(rval_of_dest cvi) ds in
    let ss  = List.map ~f:(cpexpr_of_src cvi) ss in
    let sopn = sopn_of_op o in
    Some(k, DE.Copn(clist_of_list ds, sopn, clist_of_list ss))
    
  | Comment(_s) ->
    None

  | Call(fname,ds,ss) ->
    let fun_id = pos_of_int @@ CVI.add_fname cvi k fname in
    let rvals = List.map ~f:(rval_of_dest cvi) ds in
    let args  = List.map ~f:(cpexpr_of_src cvi) ss in
    Some(k,DE.Ccall(DE.InlineFun,clist_of_list rvals,fun_id,clist_of_list args))

and cinstr_of_linstr cvi linstr =
  let loc = linstr.L.l_loc in
  let ci =
    match linstr.L.l_val with
    | Block(lbis,oinfo) ->
      assert(oinfo=None);
      let conv_bi lbi =
        match cinstr_of_base_instr cvi lbi with
        | None       -> []
        | Some(k,ci) -> [ DE.MkI (pos_of_int k,ci) ]
      in
      List.concat_map ~f:conv_bi lbis

    | If(cond,s1,s2,oinfo) ->
      let k = CVI.add_iloc cvi loc in
      assert(oinfo=None);
      let cmd1 = cmd_of_stmt cvi s1 in
      let cmd2 = cmd_of_stmt cvi s2 in
      let cpe = match cond with
        | Fcond(fc) ->
          CVI.add_ifcond cvi k true;
          cpexpr_of_fcond cvi fc
        | Pcond(pc) ->
          CVI.add_ifcond cvi k false;
          cpexpr_of_pcond cvi pc
      in
      [ DE.MkI (pos_of_int k, DE.Cif(cpe,cmd1,cmd2)) ]

    | For(sd,pe_lb,pe_ub,s,oinfo) ->
      assert(oinfo=None && sd.d_idx=None);
      let v = cvar_of_var sd.d_var in
      let ki = CVI.add_iloc cvi loc in
      let kv = CVI.add_darg cvi sd in
      let cmd = cmd_of_stmt cvi s in
      let cvar_i = DE.{v_info=pos_of_int kv; v_var=v} in
      (* FIXME: we do not distinguish DownTo/UpTo in Ocaml *)
      let rng =
        Datatypes.Coq_pair(
          Datatypes.Coq_pair(DE.UpTo,cpexpr_of_pexpr cvi pe_lb),
          cpexpr_of_pexpr cvi pe_ub)
      in
      [ DE.MkI (pos_of_int ki, DE.Cfor(cvar_i,rng,cmd)) ]

    | While(wt,fc,s,oinfo) ->
      assert(oinfo=None);
      if (wt=DoWhile) then failwith "conversion to coq does not support do-while";
      let k = CVI.add_iloc cvi loc in
      let cmd = cmd_of_stmt cvi s in
      let cpe = cpexpr_of_fcond cvi fc in
      [ DE.MkI (pos_of_int k, DE.Cwhile(cpe,cmd)) ]
  in
  ci

and cmd_of_stmt cvi s =
  clist_of_list @@ List.concat_map ~f:(cinstr_of_linstr cvi) s

let base_instr_of_cassgn cvi rval atag pe =
  match pe with
  | DE.Pvar(_)
  | DE.Pconst(_)
  | DE.Pget(_) ->
    let d = dest_of_rval cvi rval in
    let s = src_of_cpexpr cvi pe in
    let aty = assgn_type_of_atag atag in
    Assgn(d,s,aty)

  | DE.Pcast(_) -> assert false

  | DE.Pnot(_) -> assert false

  | DE.Papp2(_,_,_) -> assert false

  | DE.Pbool(_) -> assert false

  | DE.Pload(_) -> assert false

let rec instr_of_cinstr cvi lci =
  let k, ci = match lci with DE.MkI(k,ci) -> k,ci in
  let loc = CVI.get_iloc cvi k in
  let mk_block bi =
    Block([{ L.l_val = bi; L.l_loc = loc }], None)
  in
  let instr =
    match ci with
    | DE.Cassgn(rval,atag,pe) ->
      mk_block (base_instr_of_cassgn cvi rval atag pe)

    | DE.Copn(ds,co,ss) ->
      let ds = List.map ~f:(dest_of_rval cvi) @@ list_of_clist ds in
      let ss = List.map ~f:(src_of_cpexpr cvi) @@ list_of_clist ss in
      let o = op_of_sopn co in
      mk_block (Op(o,ds,ss))

    | DE.Cif(cpe,cmd1,cmd2) ->
      let is_fcond = CVI.get_ifcond cvi k in
      let s1 = stmt_of_cmd cvi cmd1 in
      let s2 = stmt_of_cmd cvi cmd2 in
      let cond =
        if is_fcond then (
          Fcond(fcond_of_cpexpr cvi cpe)
        ) else (
          Pcond(pcond_of_cpexpr cvi cpe)
        )
      in
      If(cond,s1,s2,None)

    | DE.Cfor(vi,rng,cmd) ->
      let vargs = CVI.get_varg cvi vi.DE.v_info in
      let v = var_of_cvar vi.DE.v_var vargs in
      let d = { d_var = v; d_idx=None; d_loc= v.Var.uloc } in
      let dir,cpe_lb,cpe_ub = match rng with
        | Datatypes.Coq_pair(Datatypes.Coq_pair(dir,cpe_lb),cpe_ub) -> dir,cpe_lb,cpe_ub
      in
      assert(dir=DE.UpTo);
      let s = stmt_of_cmd cvi cmd in
      For(d,pexpr_of_cpexpr cvi cpe_lb,pexpr_of_cpexpr cvi cpe_ub,s,None)

    | DE.Cwhile(cpe,cmd) ->
      let s = stmt_of_cmd cvi cmd in
      let fc = fcond_of_cpexpr cvi cpe in
      While(WhileDo,fc,s,None)

    | DE.Ccall(iinfo,rvals,fun_id,args) ->
      assert(iinfo=DE.InlineFun);
      let fname = CVI.get_fname cvi fun_id in
      let ds = List.map ~f:(dest_of_rval cvi)  @@ list_of_clist rvals in
      let ss = List.map ~f:(src_of_cpexpr cvi) @@ list_of_clist args in
      mk_block (Call(fname,ds,ss))
  in
  { L.l_loc = loc; L.l_val = instr }

and stmt_of_cmd cvi c =
   List.map ~f:(instr_of_cinstr cvi) (list_of_clist c)
