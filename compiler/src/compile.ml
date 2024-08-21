open Utils
open Prog
open Glob_options

let preprocess reg_size asmOp p =
  let p =
    p |> Subst.remove_params |> Insert_copy_and_fix_length.doit reg_size
  in
  Typing.check_prog reg_size asmOp p;
  p

(* -------------------------------------------------------------------- *)

let parse_file arch_info fname =
  let env =
    List.fold_left Pretyping.Env.add_from Pretyping.Env.empty
      !Glob_options.idirs
  in
  Pretyping.tt_program arch_info env fname

(* -------------------------------------------------------------------- *)
let rec warn_extra_i pd asmOp i =
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) -> (
      match tag with
      | AT_rename ->
          warning ExtraAssignment i.i_loc
            "@[<v>extra assignment introduced:@;<0 2>%a@]"
            (Printer.pp_instr ~debug:false pd asmOp)
            i
      | AT_inline ->
          hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
            "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
            (Printer.pp_instr ~debug:false pd asmOp)
            i
      | _ -> ())
  | Cif (_, c1, c2) | Cwhile (_, c1, _, c2) ->
      List.iter (warn_extra_i pd asmOp) c1;
      List.iter (warn_extra_i pd asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ -> ()

let warn_extra_fd pd asmOp (_, fd) = List.iter (warn_extra_i pd asmOp) fd.f_body

(*--------------------------------------------------------------------- *)

let compile (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) visit_prog_after_pass prog cprog =
  let module Regalloc = Regalloc.Regalloc (Arch) in
  let module StackAlloc = StackAlloc.StackAlloc (Arch) in
  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef (fn, cfd) in
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef fd) in

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd
  in

  let translate_var = Conv.var_of_cvar in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug up
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map Conv.fdef_of_csfdef fds in

    CheckAnnot.check_stack_size fds;


    let get_internal_size _fd sfe =
      let stk_size =
        BinInt.Z.add sfe.Expr.sf_stk_sz sfe.Expr.sf_stk_extra_sz in
      Conv.z_of_cz (Memory_model.round_ws sfe.sf_align stk_size)
    in

    let fds =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        get_internal_size
        fds
    in
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map Conv.csfdef_of_fdef fds in
    fds
  in

  let pp_cuprog s cp =
    Conv.prog_of_cuprog cp |> visit_prog_after_pass ~debug:true s
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog cp in
    Printer.pp_sprog ~debug:true Arch.pointer_data Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.pointer_data Arch.asmOp fmt lp in

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd
  in

  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl fd in
    let cvar = Conv.cvar_of_var in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;

    let f_cc =
      match fd.f_cc with
      | Subroutine si ->
          (* Since some arguments/returns are expended we need to fix the info *)
          let tbl = Hashtbl.create 17 in
          let newpos = ref 0 in
          let mk_n x =
            match x.v_kind, x.v_ty with
            | Reg (_, Direct), Arr (_, n) -> n
            | _, _ -> 1
          in
          let doarg i x =
            Hashtbl.add tbl i !newpos;
            newpos := !newpos + mk_n x
          in
          List.iteri doarg fd.f_args;
          let doret o x =
            match o with
            | Some i -> [Some (Hashtbl.find tbl i)]
            | None -> List.init (mk_n (L.unloc x)) (fun _ -> None)
          in
          let returned_params =
            List.flatten (List.map2 doret si.returned_params fd.f_ret) in
          FInfo.Subroutine { returned_params }

      | _ -> fd.f_cc
    in
    let do_outannot x a =
      try
        let (_, va) = Hv.find harrs (L.unloc x) in
        List.init (Array.length va) (fun _ -> [])
      with Not_found -> [a] in
    let f_outannot = List.flatten (List.map2 do_outannot fd.f_ret fd.f_outannot) in
    let finfo = fd.f_loc, fd.f_annot, f_cc, f_outannot in
    { Array_expansion.vars; arrs = !arrs; finfo }
  in

  let refresh_instr_info fn f =
    (fn, f) |> Conv.fdef_of_cufdef |> refresh_i_loc_f |> Conv.cufdef_of_fdef |> snd
  in

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii
  in

  let fresh_id _gd x =
    let x = Conv.var_of_cvar x in
    Prog.V.clone x
  in

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
  let renaming_fd fd = Regalloc.renaming fd in
  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog sp in
    let tokeep = RemoveUnusedResults.analyse fds in
    tokeep
  in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog p in
      List.iter (warn_extra_fd Arch.pointer_data Arch.asmOp) fds
  in



  (* TODO: Share this with regalloc. *)
  let get_rak f =
    let open Return_address_kind in
    match f.f_cc with
    | Export _ -> RAKexport
    | Internal -> RAKexport
    | Subroutine _ ->
      let ral =
        match f.f_annot.retaddr_kind with
        | None -> Arch.callstyle
        | Some ral -> begin
          match ral with
          | RAKexport -> assert false
          | RAKstack -> StackDirect
          | RAKregister -> Arch.callstyle (* We cannot use ByReg on StackDirect Architectures *)
          | RAKextra_register -> ByExtraReg
         end
      in
      match ral with
      | StackDirect -> RAKstack
      | ByReg oreg -> RAKregister
      | ByExtraReg -> RAKextra_register
  in

  let slh_info up =
    let p = Conv.prog_of_cuprog up in
    let ty_tbl = Sct_checker_forward.compile_infer_msf p in
    let rak_tbl = Hf.create 17 in
    List.iter (fun f -> Hf.add rak_tbl f.f_name (get_rak f)) (snd p);
    fun fn ->
      let (tin, tout) = try Hf.find ty_tbl fn with Not_found -> assert false in
      let rak = try Hf.find rak_tbl fn with Not_found -> assert false in
      let open Slh_lowering in
      {
        slhfi_tin = tin;
        slhfi_tout = tout;
        slhfi_rak = rak;
      }
  in

  (* TODO_RSB: We should use the function name to check if the user provided the
     tree in an annotation. *)
  let pc_return_tree fn ris =
    (* Create a sorted binary tree with [n] internal nodes labeled
       [get_label pos, get_label pos+1, ..., get_label pos+n-1].
       When [n] is 2, [go_left] decides to which side the child node goes. *)
    let rec tree_structure pos go_left get_label n =
      let empty = Utils0.BTleaf in
      let node x t0 t1 = Utils0.BTnode(get_label x, t0, t1) in
      let single x = node x empty empty in
      match n with
      | 0 -> empty
      | 1 -> single pos
      | 2 ->
          if go_left
          then node (pos + 1) (single pos) empty
          else node pos empty (single (pos + 1))
      | _ ->
          let n0 = (n - 1) / 2 in (* Size of the left tree: at most half. *)
          let n1 = n - n0 - 1 in  (* Size of the right tree: the rest. *)
          let pos' = n0 + pos in
          let t0 = tree_structure pos true get_label n0 in
          let t1 = tree_structure (pos' + 1) false get_label n1 in
          node pos' t0 t1
    in

    (* BEGIN DEBUG *)
    let rec collect acc = function
      | Utils0.BTleaf -> acc
      | Utils0.BTnode((_, x), t0, t1) ->
          collect (collect (CoreConv.int_of_cz x :: acc) t0) t1
    in
    let rec is_sorted = function
      | Utils0.BTleaf -> true
      | Utils0.BTnode((_, x), t0, t1) ->
          let x = CoreConv.int_of_cz x in
          List.for_all (fun y -> y < x) (collect [] t0)
          && is_sorted t0
          && List.for_all (fun y -> y > x) (collect [] t1)
          && is_sorted t1
    in
    let all_tags t =
      let x = collect [] t in
      let tags = List.range 0 `To (List.length x - 1) in
      List.sort compare x = tags
    in
    let check n t =
      if not (all_tags t && is_sorted t)
      then failwith (Format.sprintf "Error in%s, size %d" fn.fn_name n)
    in
    (* END DEBUG *)

    let get_label (pos : int) : Protect_calls.cs_info =
      try List.find (fun (_, tag) -> Conv.cz_of_int pos = tag) ris
      with Not_found -> assert false
    in
    let t = tree_structure 0 true get_label (List.length ris) in
    check (List.length ris) t; (* DEBUG *)
    t
  in

  let tbl_annot =
    let tbl = Hf.create 17 in
    let add (fn, cfd) =
      let fd = fdef_of_cufdef fn cfd in
      Hf.add tbl fn fd.f_annot
    in
    List.iter add cprog.Expr.p_funcs;
    tbl
  in

  let get_annot fn =
    try Hf.find tbl_annot fn
    with Not_found ->
           hierror
             ~loc:Lnone
             ~funname:fn.fn_name
             ~kind:"compiler error"
             ~internal:true
             "invalid annotation table."
  in

  let szs_of_fn fn =
    match (get_annot fn).stack_zero_strategy with
    | Some (s, ows) -> Some (s, Option.map Pretyping.tt_ws ows)
    | None -> None
  in

  let tbl_annot =
    let tbl = Hf.create 17 in
    let add (fn, cfd) =
      let fd = fdef_of_cufdef fn cfd in
      Hf.add tbl fn fd.f_annot
    in
    List.iter add cprog.Expr.p_funcs;
    tbl
  in

  let get_annot fn =
    try Hf.find tbl_annot fn
    with Not_found ->
           hierror
             ~loc:Lnone
             ~funname:fn.fn_name
             ~kind:"compiler error"
             ~internal:true
             "invalid annotation table."
  in

  let szs_of_fn fn =
    match (get_annot fn).stack_zero_strategy with
    | Some (s, ows) -> Some (s, Option.map Pretyping.tt_ws ows)
    | None -> None
  in

  let cparams =
    {
      Compiler.rename_fd;
      Compiler.expand_fd;
      Compiler.split_live_ranges_fd =
        apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd =
        apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol =
        Var0.Var.vname (Conv.cvar_of_var Arch.rsp_var);
      Compiler.global_static_data_symbol =
        Var0.Var.vname (Conv.cvar_of_var Arch.rip);
      Compiler.stackalloc = memory_analysis;
      Compiler.removereturn;
      Compiler.regalloc = global_regalloc;
      Compiler.print_uprog =
        (fun s p ->
          pp_cuprog s p;
          p);
      Compiler.print_sprog =
        (fun s p ->
          warn_extra s p;
          eprint s pp_csprog p;
          p);
      Compiler.print_linear =
        (fun s p ->
          eprint s pp_linear p;
          p);
      Compiler.refresh_instr_info;
      Compiler.warning;
      Compiler.lowering_opt = Arch.lowering_opt;
      Compiler.fresh_id;
      Compiler.fresh_var_ident = Conv.fresh_var_ident;
      Compiler.slh_info;
      Compiler.protect_calls = !Glob_options.protect_calls;
      Compiler.pc_return_tree;
      Compiler.stack_zero_info = szs_of_fn;
    }
  in

  let export_functions =
    let conv fd = fd.f_name in
    List.fold_right
      (fun fd acc ->
        match fd.f_cc with
        | Export _ -> conv fd :: acc
        | Internal | Subroutine _ -> acc)
      (snd prog) []
  in

  Compiler.compile_prog_to_asm Arch.asm_e Arch.call_conv Arch.aparams cparams
    export_functions
    (Expr.to_uprog Arch.asmOp cprog)
