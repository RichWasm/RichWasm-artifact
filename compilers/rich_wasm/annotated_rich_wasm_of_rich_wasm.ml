open! Core
open! Rich_wasm_typechecker
open! Rich_wasm

let suffix = ".rwasm"

let command =
  Command.basic
    ~summary:"Rich Wasm annotator"
    ~readme:(fun () ->
      "This annotator takes \".rwasm\" files and produces \".rwasma\" files")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map output_dir =
       flag "output-dir" (required string) ~doc:"DIR in which to output rwasm files"
     and input_dir =
       flag
         "input-dir"
         (optional string)
         ~doc:
           "DIR in which to find rwasm files to annotate. Either provide this flag or \
            provide filenames directly."
     and filenames = anon (sequence ("filenames" %: string))
     and just_typecheck =
       flag "-just-typecheck" no_arg ~doc:"just typecheck; don't produce .rwasma files"
     and aggregate_into_single_file =
       flag
         "aggregate-into-single-file"
         (optional string)
         ~doc:
           "FILE into which to aggregate all modules. Otherwise, modules are written out \
            one per file."
     in
     fun () ->
       let filenames =
         match input_dir, filenames with
         | None, [] ->
           raise_s
             [%message
               "You must either provide filenames to compile or a directory from which \
                to find rwasm files"]
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
         | non_rwasm_filenames ->
           raise_s
             [%message
               "Filenames must end with \".rwasm\"" (non_rwasm_filenames : string list)]
       in
       let modules =
         List.map filenames ~f:(fun filename ->
           let contents =
             try filename |> Stdio.In_channel.read_all with
             | Sys_error e -> raise_s [%sexp (e : string)]
           in
           contents
           |> Sexp.of_string
           |> Rich_wasm.Module.t_of_sexp
           |> fun rwasm ->
           let filename =
             filename
             |> String.chop_suffix_exn ~suffix
             |> String.split ~on:'/'
             |> List.last_exn
           in
           filename, rwasm)
         |> String.Map.of_alist_exn
       in
       match just_typecheck with
       | true ->
         (match Rich_wasm_typechecker.typecheck modules with
          | Ok _ -> ()
          | Error error -> print_s [%message "Failed to typecheck" (error : Error.t)])
       | false ->
         (match Rich_wasm_typechecker.annotate modules with
          | Error error -> print_s [%message "Failed to typecheck" (error : Error.t)]
          | Ok annotated ->
            Sys_unix.chdir output_dir;
            (match aggregate_into_single_file with
             | None ->
               Map.iteri annotated ~f:(fun ~key:filename ~data:annotated ->
                 Stdio.Out_channel.write_all
                   (filename ^ ".rwasma")
                   ~data:
                     (Sexp.to_string
                        [%sexp (annotated : Rich_wasm_compiler_interface.Module.t)]))
             | Some filename ->
               Stdio.Out_channel.write_all
                 filename
                 ~data:
                   (Sexp.to_string
                      [%sexp
                        (annotated : Rich_wasm_compiler_interface.Module.t String.Map.t)])))
         |> Fn.ignore)
;;

let () = Command_unix.run ~version:"alpha" ~build_info:"" command
