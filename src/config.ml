open Format

(****** Command line + Software configuration *****)
type config_t = {
  f_name:string;
  outputsmt_name:string;
  distinct_i:int;
  debug:bool;
  version:string;
  lists:bool;
}
exception Version
exception Usage of string
exception NotFound of string
			

let set_outputsmt config (s:string) = config := {!config with outputsmt_name=s}
let set_debug config () = config := {!config with debug=true}
let set_lists config () = config := {!config with lists=true}

let set_fname config (s:string) =  
  if Sys.file_exists s
  then config := {!config with f_name=s}
  else raise (NotFound s) 

let set_di config nb =
  if (nb < 1)
  then raise (Usage "nb distinguished should be >= 1")
  else config := {!config with distinct_i=nb}
					   
let make_default_config () = {
  f_name="";
  outputsmt_name="stdout";
  distinct_i = 1;
  debug=false;
  lists=false;
  version="1.2 Sept 2016";
}
			       
let string_config cf =
  Printf.sprintf "inputfile=%s,di=%d\n" cf.f_name cf.distinct_i
			       
let read_args () =
  let cf = ref (make_default_config()) in
  let speclist = 
    [
      ("--version",Arg.Unit (fun () -> fprintf std_formatter "vaphor Version %s@." !cf.version ; raise(Version)),": print version and exit");
      ("-debug", Arg.Unit (set_debug cf) ,": all debug info");
      ("-lists", Arg.Unit (set_lists cf) ,": treats arrays as lists with operations such as insert");
      ("-distinct", Arg.Int (set_di cf) ,": #distinguished elements in abstraction");
      ("-o", Arg.String (set_outputsmt cf) ,": outputfile, default is res.smt2");
    ] in
  let usage_msg = "Usage : ./vaphor [options] file.smt2" in
  try (Arg.parse speclist (set_fname cf) usage_msg; 
       if !cf.f_name = "" then begin Arg.usage speclist usage_msg ; raise (Usage usage_msg) end; 
       !cf 
  )
  with
  | Version -> exit(1)
  | Usage(_) -> exit(1)
