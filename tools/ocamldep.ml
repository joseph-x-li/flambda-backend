let () =
  Compenv.set_extra_params Flambda_backend_args.Extra_params.read_param;
  Makedepend.main ()
