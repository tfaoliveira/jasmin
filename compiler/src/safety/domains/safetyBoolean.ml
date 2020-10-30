open Utils
open Apron
    
open SafetyUtils
open SafetyPreanalysis
open SafetyVar
open SafetyExpr 
open SafetyConstr
open SafetyInterfaces
open SafetyNum
open SafetyDisjunctive
open SafetyProduct
open SafetyCongr
open SafetyProf

(*****************************************)
(* Maps with Equivalence Classes of Keys *)
(*****************************************)

module type Ordered = sig
  type t
  val compare : t -> t -> int
end

module Mc = Map.Int

module Map2 (M : Map.S) = struct
  let map2 : ('a -> 'b -> 'c) -> 'a M.t -> 'b M.t -> 'c M.t =
    fun f map_a map_b ->
      M.mapi (fun k a ->
          let b = M.find k map_b in
          f a b)
        map_a

  let merge2 : (unit -> 'a) -> (unit -> 'b) -> 'a M.t -> 'b M.t -> ('a M.t * 'b M.t)=
    fun fa fb mapa mapb ->
      (M.merge (fun _ aopt _ -> match aopt with
           | None -> fa () |> some
           | Some a -> Some a)
          mapa mapb,
       M.merge (fun _ _ bopt -> match bopt with
           | None -> fb () |> some
           | Some b -> Some b)
         mapa mapb)
end

module type EqMap = sig
  type key
  type 'a t

  val empty : 'a t

  (* Number of equivalence classes. *)
  val csize : 'a t -> int

  (* Fold over equivalence classes *)
  val cfold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val mem: key -> 'a t -> bool

  val find: key -> 'a t -> 'a

  val adds: key list -> 'a -> 'a t -> 'a t

  val removes: key list -> 'a t -> 'a t

  val iter: (key -> 'a -> unit) -> 'a t -> unit
      
  val map: ('a -> 'b) -> 'a t -> 'b t

  val map2 : ('a -> 'a -> 'c) -> 'a t -> 'a t -> 'c t

  val kfilter : (key -> bool) -> 'a t -> 'a t

  val vmerge:
    ('a option -> 'a option -> 'b option) -> 'a t -> 'a t -> 'b t
end

module MakeEqMap (K : Ordered) : EqMap with type key = K.t = struct
  type key = K.t

  module Mk = Map.Make(K)

  type 'a t = { ktoc : int Mk.t;
                ctov : 'a Mc.t;
                _cpt : int }

  let empty = { ktoc = Mk.empty;
                ctov = Mc.empty;
                _cpt = 0 }

  let csize t = Mc.cardinal t.ctov

  let newc t = ({ t with _cpt = t._cpt + 1 }, t._cpt)

  let mem k t = try Mc.mem (Mk.find k t.ktoc) t.ctov with Not_found -> false

  let find k t = Mc.find (Mk.find k t.ktoc) t.ctov

  let adds ks a t =
    let t,i = newc t in
    let ktoc =
      List.fold_left (fun ktoc k -> Mk.add k i ktoc) t.ktoc ks in
    { t with ktoc = ktoc; ctov = Mc.add i a t.ctov }

  let iter f t = Mk.iter (fun k c -> f k (Mc.find c t.ctov)) t.ktoc
                
  let map f t = { t with ctov = Mc.map f t.ctov }

  (* Fold over classes. *)
  let cfold f t a = Mc.fold (fun _ x y -> f x y) t.ctov a

  (* This function unifies the equivalence classes of t and t' *)
  let unify_classes : 'a t -> 'b t -> int * int Mk.t * 'a Mc.t * 'b Mc.t =
    fun t t' ->
      let open Utils in
      let module Sk = Set.Make(K) in
      (* This function groupe keys in the same equivalence class *)
      let rec grp l = match l with
        | [] | _ :: [] -> l
        | (x1,l1) :: (x2,l2) :: l' ->
          if x1 = x2 then grp ((x1,Sk.union l1 l2) :: l')
          else (x1,l1) :: grp ((x2,l2) :: l') in

      let s_binds x =
        Mk.bindings x.ktoc
        |> List.stable_sort (fun (_,i) (_,i') -> Stdlib.compare i i')
        |> List.map (fun (x,y) -> (y,Sk.singleton x))
        |> grp in

      let lt,lt' = s_binds t,s_binds t' in
      let ltk = List.fold_left (fun sk (_,sk') ->
          Sk.union sk sk') Sk.empty lt in
      let ltk' = List.fold_left (fun sk (_,sk') ->
          Sk.union sk sk') Sk.empty lt' in

      (* Tedious *)
      let rec merge_ne f_next lt lt' cpt mk mc mc' t t' ltk ltk' = match lt with
        (* We inverse the arguments ! *)
        | [] -> f_next lt' lt cpt mk mc' mc t' t ltk' ltk

        | (i,l) :: r ->
          let k = Sk.any l in
          let oi' = try Some (Mk.find k t'.ktoc) with Not_found -> None in
          let l' = match obind (fun i' -> List.assoc_opt i' lt') oi' with
            | Some s -> s
            | None -> Sk.empty in
          let join =
            Sk.union
              (Sk.inter l l')
              (Sk.union
                 (Sk.diff l ltk')
                 (Sk.diff l' ltk)) in
          let mk = Sk.fold (fun k mk -> Mk.add k cpt mk) join mk in
          let mc = Mc.add cpt (Mc.find i t.ctov) mc in
          let mc' = match oi' with
            | None -> mc'
            | Some i' -> Mc.add cpt (Mc.find i' t'.ctov) mc' in

          let nl, nl' = Sk.diff l join, Sk.diff l' join in
          let nlt = if Sk.is_empty nl then r else (i,nl) :: r in
          let nlt' = match oi' with
            | None -> lt'
            | Some i' ->
              if Sk.is_empty nl' then List.remove_assoc i' lt'
              else assoc_up i' (fun _ -> nl') lt' in

          merge_ne f_next nlt nlt' (cpt + 1) mk mc mc' t t' ltk ltk' in

      merge_ne (merge_ne (fun _ _ cpt mk mc mc' _ _ _ _ -> (cpt,mk,mc,mc')))
        lt lt' 0 Mk.empty Mc.empty Mc.empty t t' ltk ltk'

  let map2 f t t' =
    let cpt,mk,mc,mc' = unify_classes t t' in
    let module M2 = Map2(Mc) in
    { ktoc = mk;
      ctov = M2.map2 f mc mc';
      _cpt = cpt }

  let kfilter (f : key -> bool) (t : 'a t) =
    let module Si = Set.Int in
    let ktoc = Mk.filter (fun k _ -> f k) t.ktoc in
    let si = Mk.fold (fun _ i sk -> Si.add i sk) ktoc Si.empty in
    let ctov = Mc.filter (fun i _ -> Si.mem i si) t.ctov in
    { t with ctov = ctov; ktoc = ktoc }

  let removes (ks : key list) (t : 'a t) =
    kfilter (fun k -> not (List.mem k ks)) t

  let vmerge f t t' =
    let cpt,mk,mc,mc' = unify_classes t t' in
    let mr = Mk.fold (fun _ i mr ->
        if Mc.mem i mr then mr
        else
          let ov = Mc.Exceptionless.find i mc
          and ov' = Mc.Exceptionless.find i mc' in
          match f ov ov' with
          | None -> mr
          | Some rv -> Mc.add i rv mr)
        mk Mc.empty in
    let mk = Mk.filter (fun _ i -> Mc.mem i mr) mk in
    { ktoc = mk; ctov = mr; _cpt = cpt }
end

module EMs = MakeEqMap(Scmp)



(*************************************************)
(* Numerical Domain with Two Levels of Precision *)
(*************************************************)

module AbsNumTMake (PW : ProgWrap) : AbsNumT = struct

  let vdw =
    if Config.sc_dynamic_packing ()
    then (module PIDynMake (PW) : VDomWrap)
    else (module PIMake (PW) : VDomWrap)

  module VDW = (val vdw)

  (* Numerical domain using boxes for non-relational variables, 
     and polyhedra for relational variables *)
  module RProd =
    AbsNumProd (VDW) (AbsNumI (BoxManager) (PW)) (AbsNumI (PplManager) (PW))

  (* Disjunctive domain built on top of the numerical domain. *)
  module RNum = AbsDisj (RProd)

  (* Product of the disjunctive domain and of a congruence domain. *)
  module RNumWithCongr = ReducedProd (struct
      module A = RNum
      module B = LiftToDisj (AbsNumCongr)

      let print ?full:(full=false) fmt (a,b) =
        Format.fprintf fmt "@[<v>%a* Congruences:@;%a@]"
          (A.print ~full) a
          (B.print ~full) b
        
      let reduce (a,b) = (a,b)
    end)
      
  module R = MakeAbsDisjProf (struct
      module Num = RNumWithCongr
      let prefix = "R."
    end)

  module NRNum = AbsNumI (BoxManager) (PW)

  module NR = MakeAbsNumProf (struct
      module Num = NRNum
      let prefix = "NR."
    end)

  let downgrade a = NR.of_box (R.to_box a)

  let upgrade a tshape = R.of_box (NR.to_box a) tshape
end


(************************************************)
(* Abstraction of numerical and boolean values. *)
(************************************************)

(* Add boolean variable abstractions and keep track of initialized variables 
   and points-to information.
   The boolean abstraction use a non-relational abstract domain. *)
module AbsBoolNoRel (AbsNum : AbsNumT) (Pt : PointsTo) (Sym : SymExpr)
  : AbsNumBoolType = struct

  (* <Ms.find s init> is an over-approximation of the program state where s
     is *not* initialized.
     Remark: we lazily populate init and bool*)
  type t = { bool : AbsNum.NR.t Mbv.t;
             init : AbsNum.NR.t EMs.t; 
             num : AbsNum.R.t;
             points_to : Pt.t;
             sym : Sym.t; }

  module Mbv2 = Map2(Mbv)

  let merge_bool_dom t t' =
    let eb,eb' = Mbv2.merge2
        (fun () -> AbsNum.downgrade t.num)
        (fun () -> AbsNum.downgrade t'.num)
        t.bool t'.bool in
    ({ t with bool = eb }, { t' with bool = eb' })

  let merge_init_dom t t' =
    let eb = EMs.vmerge (fun x _ -> match x with
        | None -> Some (AbsNum.downgrade t.num)
        | Some _ -> x) t.init t'.init
    and eb' = EMs.vmerge (fun x _ -> match x with
        | None -> Some (AbsNum.downgrade t'.num)
        | Some _ -> x) t'.init t.init in
    ({ t with init = eb }, { t' with init = eb' })

  let apply f df fpt fsym t = { bool = Mbv.map df t.bool;
                                init = EMs.map df t.init;
                                num = f t.num;
                                points_to = fpt t.points_to;
                                sym = fsym t.sym; }

  (* Since init and bool are lazily populated, we merge the domains before 
     applying f *)
  let apply2 f df fpt fsym t t' =
    let t, t' = merge_init_dom t t' in
    let t, t' = merge_bool_dom t t' in
    { bool = Mbv2.map2 df t.bool t'.bool;
      init = EMs.map2 df t.init t'.init;
      num = f t.num t'.num;
      points_to = fpt t.points_to t'.points_to;
      sym = fsym t.sym t'.sym; }

  (* [for_all2 f a b b_dfl]
     Iters over the first map *)
  let for_all2 : ('a -> 'b option -> 'c) -> 'a Mbv.t -> 'b Mbv.t -> bool =
    fun f map_a map_b ->
      Mbv.for_all (fun k a ->
          let b = try Some (Mbv.find k map_b) with Not_found -> None in
          f a b)
        map_a

  let rec bool_vars = function
    | [] -> []
    | h :: t ->
      if ty_mvar h = Bty Bool then
        (Bvar.make h true) :: (Bvar.make h false) :: bool_vars t
      else bool_vars t

  let rec init_vars = function
    | [] -> []
    | Mvalue at :: t -> string_of_mvar (Mvalue at) :: init_vars t
    | _ :: t -> init_vars t

  let make : mvar list -> mem_loc list -> t = fun l mls ->
    let b_vars = bool_vars l in
    let abs = AbsNum.R.make l in
    let dabs = AbsNum.downgrade abs in

    let bmap = List.fold_left (fun bmap bv ->
        Mbv.add bv dabs bmap) Mbv.empty b_vars in
    { bool = bmap;
      init = EMs.empty;
      num = abs;
      points_to = Pt.make mls;
      sym = Sym.make (); }

  let unify_map : AbsNum.NR.t Mbv.t -> AbsNum.NR.t Mbv.t -> AbsNum.NR.t Mbv.t =
    fun b b' ->
      let eb = Mbv.merge (fun _ x y -> match x with
          | None -> y
          | Some _ -> x) b b'
      and eb' = Mbv.merge (fun _ x y -> match x with
          | None -> y
          | Some _ -> x) b' b in
      Mbv2.map2 AbsNum.NR.unify eb eb'


  let eunify_map : AbsNum.NR.t EMs.t -> AbsNum.NR.t EMs.t -> AbsNum.NR.t EMs.t =
    fun b b' ->
      let eb = EMs.vmerge (fun x y -> match x with
          | None -> y
          | Some _ -> x) b b'
      and eb' = EMs.vmerge (fun x y -> match x with
          | None -> y
          | Some _ -> x) b' b in
      EMs.map2 AbsNum.NR.unify eb eb'

  let meet : t -> t -> t = fun t t' ->
    let t,t' = merge_bool_dom t t' in
    { bool = Mbv2.map2 AbsNum.NR.meet t.bool t'.bool;
      init = eunify_map t.init t'.init;
      num = AbsNum.R.meet t.num t'.num;
      points_to = Pt.meet t.points_to t'.points_to;
      sym = Sym.meet t.sym t'.sym; }

  let join t t' =
    if AbsNum.R.is_bottom t.num       then t'
    else if AbsNum.R.is_bottom t'.num then t
    else apply2 AbsNum.R.join AbsNum.NR.join Pt.join Sym.join t t'

  let widening : Mtcons.t option -> t -> t -> t = fun oc ->
    apply2 (AbsNum.R.widening oc) (AbsNum.NR.widening oc)
      Pt.widening Sym.widening

  let forget_list : t -> mvar list -> t = fun t l ->
    let f x = AbsNum.R.forget_list x l
    and df x = AbsNum.NR.forget_list x l
    and f_pts x = Pt.forget_list x l
    and fsym x = Sym.forget_list x l in
    apply f df f_pts fsym t

  let forget_bvar : t -> mvar -> t  = fun t bv ->
    let dnum = AbsNum.downgrade t.num in
    let t_bv, f_bv = Bvar.make bv true, Bvar.make bv false in
    let bool = Mbv.add t_bv dnum t.bool
               |> Mbv.add f_bv dnum in
    { t with bool = bool }

  (* No need to check anything on t.init and t'.init. *)
  let is_included : t -> t -> bool = fun t t' ->
    let check_b b b_opt' = 
      let b' = match b_opt' with
        | None -> AbsNum.downgrade t'.num
        | Some b' -> b' in
      AbsNum.NR.is_included b b' in

    (AbsNum.R.is_included t.num t'.num)
    && (for_all2 check_b t.bool t'.bool)
    && (Pt.is_included t.points_to t'.points_to)

  let is_bottom : t -> bool = fun t -> AbsNum.R.is_bottom t.num

  let bound_variable : t -> mvar -> Interval.t = fun t v ->
    AbsNum.R.bound_variable t.num v

  let bound_texpr : t -> Mtexpr.t -> Interval.t = fun t e ->
    AbsNum.R.bound_texpr t.num e

  (* abs_beval t bexpr : evaluate bexpr in t.
     We split disequalities in two cases to improve precision. *)
  let rec abs_eval_btcons : t -> btcons -> AbsNum.R.t = fun t bexpr ->
    match bexpr with
    | BLeaf c -> begin match Mtcons.get_typ c with
        | Tcons0.DISEQ ->
          let bexpr_pos = BLeaf (Mtcons.make (Mtcons.get_expr c) Tcons0.SUP) in

          let minus_expr = Mtexpr.unop Texpr0.Neg (Mtcons.get_expr c) in
          let bexpr_neg = BLeaf (Mtcons.make minus_expr Tcons0.SUP) in

          abs_eval_btcons t (BOr (bexpr_pos,bexpr_neg))
        | _ -> AbsNum.R.meet_constr t.num c end

    | BVar bv ->
      begin try
          let ab = Mbv.find bv t.bool in
          AbsNum.upgrade ab t.num with
      | Not_found -> t.num end

    | BOr (l_bexpr, r_bexpr) ->
      AbsNum.R.join
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

    | BAnd (l_bexpr, r_bexpr) ->
      AbsNum.R.meet
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

  let abs_eval_neg_btcons t bexpr = match flip_btcons bexpr with
    | None -> t.num
    | Some c -> abs_eval_btcons t c

  (* Assign an expression given by a list of constrained expressions.
     We do not touch init and points_to there, this has to be done by manualy
     by the caller.
     We unpopulate init to be faster. This is sound if the evaluation of an
     expression neither modifies init not depend on it. *)
  let assign_sexpr : ?force:bool -> t -> mvar -> minfo option -> s_expr -> t =
    fun ?force:(force=false) t v info s_expr ->
      let s_init = t.init in
      let points_to_init = t.points_to in
      let t = { t with init = EMs.empty } in
      
      let t = match info with
        | None -> t
        | Some info -> { t with num = AbsNum.R.dom_st_update t.num v info; } in
      
      let n_env = AbsNum.R.get_env t.num in
      let constr_expr_list =
        List.map (fun (bexpr_list, expr) ->
            match bexpr_list with
            | [] -> (None,expr)
            | _ ->
              let constr = List.map (abs_eval_btcons t) bexpr_list
                           |> AbsNum.R.meet_list  in
              (Some constr,expr))
          s_expr in

      let t_list =
        List.map (fun (constr,expr) -> match expr with
            | Some e ->
              let e = Mtexpr.extend_environment e n_env in
              let t' = match constr with
                | None -> t
                | Some c ->
                  let dc = AbsNum.downgrade c in
                  apply (AbsNum.R.meet c) (AbsNum.NR.meet dc)
                    ident ident t in
              apply
                (fun x -> AbsNum.R.assign_expr ~force:force x v e)
                (fun x -> AbsNum.NR.assign_expr ~force:force x v e)
                ident ident t'

            | None ->
              let t' = match constr with
                | None -> t
                | Some c ->
                  let dc = AbsNum.downgrade c in
                  apply (AbsNum.R.meet c) (AbsNum.NR.meet dc)
                    ident ident t in
              apply
                (fun x -> AbsNum.R.forget_list x [v])
                (fun x -> AbsNum.NR.forget_list x [v])
                ident ident t'              
          ) 
          constr_expr_list in

      (* We compute the join of all the assignments *)
      let join_map b_list = match b_list with
        | [] -> assert false
        | h :: l ->
          Mbv.mapi (fun key x ->
              let elems = x :: List.map (Mbv.find key) l in
              AbsNum.NR.join_list elems) h in

      let b_list,n_list = List.map (fun x -> x.bool) t_list,
                          List.map (fun x -> x.num) t_list in

      (* If we have only one assignment in [s_expr], we add the symbolic
         equality. *)
      let sym = match s_expr with
        | [_, Some e] -> Sym.assign_expr ~force:force t.sym v e
        | _ -> Sym.forget_list t.sym [v] in
      
      { bool = join_map b_list;
        init = s_init;
        num = AbsNum.R.join_list n_list;
        points_to = points_to_init;
        sym = sym; }

  (* Assign a boolean expression.
     As we did in assign_sexpr, we unpopulate init *)
  let assign_bexpr t vb bexpr =
    let bexpr = Sym.subst_btcons t.sym bexpr in    
    let s_init = t.init in
    let points_to_init = t.points_to in

    let t = { t with init = EMs.empty } in

    let t_vb, f_vb = Bvar.make vb true,
                     Bvar.make vb false in

    let new_b =
      Mbv.add t_vb (abs_eval_btcons t bexpr |> AbsNum.downgrade) t.bool
      |> Mbv.add f_vb (abs_eval_neg_btcons t bexpr |> AbsNum.downgrade) in

    let sym = Sym.assign_bexpr t.sym vb bexpr in

    { bool = new_b;
      init = s_init;
      num = t.num;
      points_to = points_to_init;
      sym = sym; }

  let var_points_to t v = Pt.var_points_to t.points_to v

  let assign_ptr_expr t v pt_e =
    { t with points_to = Pt.assign_ptr_expr t.points_to v pt_e }

  (* [subst_btcons t c] returns an constraint [c'] equivalent to
     [c] in any state satisfying [t]. *)
  let subst_btcons t c = Sym.subst_btcons t.sym c

  let meet_btcons : t -> btcons -> t = fun t c ->    
    let c = Sym.subst_btcons t.sym c in
    let cn = abs_eval_btcons t c in
    let dcn = AbsNum.downgrade cn in

    apply (AbsNum.R.meet cn) (AbsNum.NR.meet dcn) ident ident t

  let change_environment : t -> mvar list -> t = fun t l ->
    let l = u8_blast_vars ~blast_arrays:true l in
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables that are not in l *)
    let b = Mbv.filter (fun s _ -> List.mem s bvars) t.bool
    and init = EMs.kfilter (fun s -> List.mem s ivars) t.init in

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.R.change_environment x l
    and df x = AbsNum.NR.change_environment x l
    and fsym x = Sym.change_environment x l in
    apply f df ident fsym { t with bool = b; init = init }

  let remove_vars : t -> mvar list -> t = fun t l ->
    let l = u8_blast_vars ~blast_arrays:true l in
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables in l *)
    let b = Mbv.filter (fun s _ -> not (List.mem s bvars)) t.bool
    and init = EMs.kfilter (fun s -> not (List.mem s ivars)) t.init in

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.R.remove_vars x l
    and df x = AbsNum.NR.remove_vars x l
    and ptf x = Pt.forget_list x l
    and fsym x = Sym.forget_list x l in
    apply f df ptf fsym { t with bool = b; init = init }

  let top_ni : t -> t = fun t ->
    let top = AbsNum.R.top_no_disj t.num in
    let bmap = Mbv.map (fun v -> AbsNum.NR.top v) t.bool in
    { bool = bmap;
      init = EMs.empty;
      num = top;
      points_to = Pt.make [];
      sym = Sym.make (); }

  let to_shape t shp =
    { t with num = AbsNum.R.to_shape t.num shp.num }

  let remove_disj t =
    { t with num = AbsNum.R.remove_disj t.num }

  (* Initialize some variable. 
     Note that an array is always initialized, even if its elements are not
     initialized. *)
  let is_init t at =
    let vats = match at with
      | Aarray _ -> []
      | _ -> u8_blast_at ~blast_arrays:true at in
    let vats = List.map string_of_mvar vats in
    
    { t with
      init = EMs.adds vats (AbsNum.R.bottom t.num |> AbsNum.downgrade) t.init }
    
  (* Copy some variable initialization.
     We only need this for elementary array elements. *)
  let copy_init t l e = match l, e with
    | Mvalue (AarrayEl (_, U8, _)),
      Mvalue (AarrayEl (_, U8, _)) ->
      let l = string_of_mvar l
      and e = string_of_mvar e in
      begin match EMs.find e t.init with
        | x -> { t with init = EMs.adds [l] x t.init }
        | exception Not_found -> t end
    | _ -> assert false
  
  (* Check that a variable is initialized. 
     Note that in Jasmin, an array is always initialized, even if its elements 
     are not initialized. *)
  let check_init : t -> atype -> bool = fun t at ->
    let vats = match at with
      | Aarray _ -> []
      | _ -> u8_blast_at ~blast_arrays:false at |> List.map string_of_mvar in    
    let dnum = AbsNum.downgrade t.num in
    let check x =
      try AbsNum.NR.meet dnum (EMs.find x t.init) |> AbsNum.NR.is_bottom with
      | Not_found -> AbsNum.R.is_bottom t.num in

    List.for_all check vats

  let get_env : t -> Environment.t = fun t -> AbsNum.R.get_env t.num

  let print_init fmt t = match Config.sc_is_init_no_print () with
    | Config.IP_None -> Format.fprintf fmt ""
    | Config.IP_All | Config.IP_NoArray ->
      let keep s =
        match mvar_of_svar s with
        | Mvalue (AarrayEl _)
          when Config.sc_is_init_no_print () = Config.IP_NoArray -> false
        | _ -> true
      in
      
      let dnum = AbsNum.downgrade t.num in
      let check' a =
        try AbsNum.NR.meet dnum a |> AbsNum.NR.is_bottom with
        | Not_found -> AbsNum.R.is_bottom t.num in

      let m = EMs.map (fun a -> check' a) t.init in
      Format.fprintf fmt "@[<h 2>* Init:@;";
      EMs.iter (fun s b ->
          if b && keep s then Format.fprintf fmt "%s@ " s else ()) m;
      Format.fprintf fmt "@]@;"

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt t ->
    let print_init fmt = print_init fmt t in

    let print_bool fmt =
      if Config.sc_bool_no_print () then 
        Format.fprintf fmt ""
      else begin
        Format.fprintf fmt "@[<v 0>* Bool:@;";
        Mbv.iter (fun bv nrval ->
            Format.fprintf fmt "@[<v 2>%a@;%a@]@;" Bvar.print bv
              (AbsNum.NR.print ~full:true) nrval;
          ) t.bool;
        Format.fprintf fmt "@]@;>" 
      end in

    let bool_size = Mbv.cardinal t.bool
    and init_size = EMs.csize t.init in
    let bool_nr_vars =  
      Mbv.fold (fun _ nrd size -> 
          size + Environment.size (AbsNum.NR.get_env nrd))
        t.bool 0
      |> EMs.cfold (fun nrd size -> 
          size + Environment.size (AbsNum.NR.get_env nrd))
        t.init in
    let print_bool_nums fmt = 
      Format.fprintf fmt "* Bool (%d vars.) + Init (%d vars): \
                          total of %d num. vars."
        bool_size init_size bool_nr_vars in

    if !only_rel_print then
      Format.fprintf fmt "@[<v 0>%a@]"
        (AbsNum.R.print ~full:full) t.num
    else
      Format.fprintf fmt "@[<v 0>@[<v 0>%a@]%a@;%t@;%t%t@]@;"
        (AbsNum.R.print ~full:full) t.num
        Pt.print t.points_to
        print_bool_nums
        print_bool
        print_init

  let new_cnstr_blck t l = { t with num = AbsNum.R.new_cnstr_blck t.num l }

  let add_cnstr t ~meet c i =
    let tl, tr = AbsNum.R.add_cnstr t.num ~meet c i in
    ( { t with num = tl }, { t with num = tr } )

  let pop_cnstr_blck t l = { t with num = AbsNum.R.pop_cnstr_blck t.num l }

  let pop_all_blcks t = { t with num = AbsNum.R.pop_all_blcks t.num }
end
