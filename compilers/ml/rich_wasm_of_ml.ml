open! Core
open! Ml
open! Syntax

let suffix = ".ml"

let command =
  Command.basic
    ~summary:"ML to RichWasm compiler"
    ~readme:(fun () -> "This compiler takes \".ml\" files and produces \".rwasm\" files")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map output_dir =
       flag "output-dir" (required string) ~doc:"DIR in which to output rwasm files"
     and input_dir =
       flag
         "input-dir"
         (optional string)
         ~doc:
           "DIR in which to find ml files to compile. Either provide this flag or \
            provide filenames directly."
     and filenames = anon (sequence ("filenames" %: string)) in
     fun () ->
       let filenames =
         match input_dir, filenames with
         | None, [] ->
           raise_s
             [%message
               "You must either provide filenames to compile or a directory from which \
                to find ml files"]
         | Some _, _ :: _ ->
           raise_s
             [%message
               "You cannot provide both filenames directly and an input directory"]
         | None, _ -> filenames
         | Some dir, _ ->
           Sys_unix.ls_dir dir
           |> List.filter ~f:(String.is_suffix ~suffix)
           |> List.map ~f:(fun filename -> dir ^/ filename)
       in
       let () =
         match List.filter ~f:(Fn.non (String.is_suffix ~suffix)) filenames with
         | [] -> ()
         | non_ml_filenames ->
           raise_s
             [%message "Filenames must end with \".ml\"" (non_ml_filenames : string list)]
       in
       let files =
         List.map filenames ~f:(fun filename ->
           try filename |> Stdio.In_channel.read_all with
           | Sys_error e -> raise_s [%sexp (e : string)])
       in
       let compiled = List.map ~f:Ml.compile files in
       Sys_unix.chdir output_dir;
       List.map2 filenames compiled ~f:(fun filename m_and_printer ->
         let m, _ = Or_error.ok_exn m_and_printer in
         let filename =
           filename
           |> String.chop_suffix_exn ~suffix
           |> String.split ~on:'/'
           |> List.last_exn
         in
         Stdio.Out_channel.write_all
           (filename ^ ".rwasm")
           ~data:(Sexp.to_string [%sexp (m : Rich_wasm.Module.t)]))
       |> Fn.ignore)
;;

let () = Command_unix.run ~version:"alpha" ~build_info:"" command
