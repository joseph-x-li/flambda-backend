let () =
  (match Sys.backend_type with
   | Native -> Memtrace.trace_if_requested ~context:"ocamlopt" ()
   | Bytecode | Other _ -> ());
  (* This is installed unconditionally for native and bytecode and
     all tools that consume OCAMLPARAM, to avoid warnings about flags
     that are only supported in flambda-backend,
     similarly to the treatment of native-only flags in
     [ocaml/driver/compenv.ml] *)
  Compenv.set_extra_params Flambda_backend_args.Extra_params.read_param;
  exit (Optmaindriver.main Sys.argv Format.err_formatter
    ~flambda2:Flambda2.lambda_to_cmm)
