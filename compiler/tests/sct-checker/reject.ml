open Jasmin
open Common
open Sct_checker_forward

let path = "fail"

let load_and_check name =
  Jasmin.Utils.nowarning ();
  Format.printf "File %s:@." name;
  let ((_, fds) as p) = load_file (Filename.concat path name) in
  List.iter
    (fun fd ->
      if should_check fd then
        let f = fd.Prog.f_name.fn_name in
        match ty_prog Arch.is_ct_sopn p [ f ] with
        | exception Utils.HiError e ->
            let e = { e with err_loc = Lnone } in
            Format.printf "Failed as expected %s: %a@." f Utils.pp_hierror e
        | _ ->
            Format.eprintf "Did not fail: %s.@." f;
            assert false)
    fds

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.iter load_and_check cases
