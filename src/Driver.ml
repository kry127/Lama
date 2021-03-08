open Ostap

let parse cmd =
  let s   = Util.read cmd#get_infile in
  let kws = [
    "skip";      
    "if"; "then"; "else"; "elif"; "fi";
    "while"; "do"; "od";
    "repeat"; "until";
    "for";
    "fun"; "local"; "public"; "external"; "return"; "import"; 
    "length";
    "string";
    "case"; "of"; "esac"; "when";
    "boxed"; "unboxed"; "string"; "sexp"; "array";
    "infix"; "infixl"; "infixr"; "at"; "before"; "after";
    "true"; "false"; "lazy"; "eta"; "syntax"]
  in
  Util.parse
    (object
       inherit Matcher.t s
       inherit Util.Lexers.decimal s
       inherit Util.Lexers.string s
       inherit Util.Lexers.char   s
       inherit Util.Lexers.infix  s
       inherit Util.Lexers.lident kws s
       inherit Util.Lexers.uident kws s
       inherit Util.Lexers.skip [
	 Matcher.Skip.whitespaces " \t\n\r";
	 Matcher.Skip.lineComment "--";
	 Matcher.Skip.nestedComment "(*" "*)"
       ] s
     end
    )
    (if cmd#is_workaround then ostap (p:!(Language.constparse cmd) -EOF) else ostap (p:!(Language.parse cmd) -EOF))

exception Commandline_error of string
  
class options args =
  let n = Array.length args in
  let dump_ast  = 1 in
  let dump_sm   = 2 in
  let help_string =
    "Lama compiler. (C) JetBrains Reserach, 2017-2020.\n" ^
    "Usage: lamac <options> <input file>\n\n" ^
    "When no options specified, builds the source file into executable.\n" ^
    "Options:\n" ^
    "  -c        --- compile into object file\n" ^
    "  -o <file> --- write executable into file <file>\n" ^    
    "  -I <path> --- add <path> into unit search path list\n" ^
    "  -i        --- interpret on a source-level interpreter\n" ^
    "  -s        --- compile into stack machine code and interpret on the stack machine initerpreter\n" ^
    "  -g        --- compile with debug information\n" ^
    "  -dp       --- dump AST (the output will be written into .ast file)\n" ^
    "  -ds       --- dump stack machine code (the output will be written into .sm file; has no\n" ^
    "                effect if -i option is specfied)\n" ^
    "  -tc       --- typecheck code and produce gradually typed code\n" ^
    "  -v        --- show version\n" ^
    "  -h        --- show this help\n"             
  in
  object (self)
    val version   = ref false
    val help      = ref false
    val typecheck = ref false
    val i         = ref 1
    val infile    = ref (None : string option)
    val outfile   = ref (None : string option)
    val paths     = ref [X86.get_std_path ()]
    val mode      = ref (`Default : [`Default | `Eval | `SM | `Compile ])
    val curdir    = Unix.getcwd ()
    val debug     = ref false
    (* Workaround until Ostap starts to memoize properly *)
    val const  = ref false
    (* end of the workaround *)
    val dump   = ref 0
    initializer
      let rec loop () =
        match self#peek with
        | Some opt ->
           (match opt with
            (* Workaround until Ostap starts to memoize properly *)
            | "-w"  -> self#set_workaround
            (* end of the workaround *)
            | "-c"  -> self#set_mode `Compile
            | "-o"  -> (match self#peek with None -> raise (Commandline_error "File name expected after '-o' specifier") | Some fname -> self#set_outfile fname)
            | "-I"  -> (match self#peek with None -> raise (Commandline_error "Path expected after '-I' specifier") | Some path -> self#add_include_path path)
            | "-s"  -> self#set_mode `SM
            | "-i"  -> self#set_mode `Eval
            | "-ds" -> self#set_dump dump_sm
            | "-dp" -> self#set_dump dump_ast
            | "-tc" -> self#set_typecheck
            | "-h"  -> self#set_help
            | "-v"  -> self#set_version
            | "-g"  -> self#set_debug
            | _ ->
               if opt.[0] = '-'
               then raise (Commandline_error (Printf.sprintf "Invalid command line specifier ('%s')" opt))
               else self#set_infile opt
           );
           loop ()
        | None -> ()
      in loop ()
    (* Workaround until Ostap starts to memoize properly *)
    method is_workaround = !const   
    method private set_workaround =
      const := true
    (* end of the workaround *)
    method private set_typecheck = typecheck := true
    method private set_help      = help := true
    method private set_version   = version := true
    method private set_dump mask =
      dump := !dump lor mask
    method private set_infile name =
      match !infile with
      | None       -> infile := Some name
      | Some name' -> raise (Commandline_error (Printf.sprintf "Input file ('%s') already specified" name'))
    method private set_outfile name =
      match !outfile with
      | None       -> outfile := Some name
      | Some name' -> raise (Commandline_error (Printf.sprintf "Output file ('%s') already specified" name'))
    method private add_include_path path =
      paths := path :: !paths
    method private set_mode s =
      match !mode with
      | `Default -> mode := s
      | _ -> raise (Commandline_error "Extra compilation mode specifier")
    method private peek =
      let j = !i in
      if j < n
      then (incr i; Some (args.(j)))
      else None
    method get_mode = !mode
    method get_output_option =
      match !outfile with
      | None      -> Printf.sprintf "-o %s" self#basename
      | Some name -> Printf.sprintf "-o %s" name
    method get_absolute_infile =
      let f = self#get_infile in
      if Filename.is_relative f then Filename.concat curdir f else f
    method get_infile =
      match !infile with
      | None      -> raise (Commandline_error "Input file not specified")
      | Some name -> name
    method get_typecheck = !typecheck
    method get_help = !help
    method get_include_paths = !paths
    method basename = Filename.chop_suffix (Filename.basename self#get_infile) ".expr"
    method topname =
      match !mode with
      | `Compile -> "init" ^ self#basename
      | _ -> "main"
    method dump_file ext contents =
      let name = self#basename in
      let outf = open_out (Printf.sprintf "%s.%s" name ext) in
      Printf.fprintf outf "%s" contents;
      close_out outf
    method dump_AST ast =
      if (!dump land dump_ast) > 0
      then (
        let buf = Buffer.create 1024 in
        Buffer.add_string buf "<html>";
        Buffer.add_string buf (Printf.sprintf "<title> %s </title>" self#get_infile);
        Buffer.add_string buf "<body><li>";
        GT.html(Language.Expr.t) ast buf;
        Buffer.add_string buf "</li></body>";
        Buffer.add_string buf "</html>";
        self#dump_file "html" (Buffer.contents buf)
      )
      else ()
    method dump_SM sm  =
      if (!dump land dump_sm) > 0
      then self#dump_file "sm" (SM.show_prg sm)
      else ()
    method greet =
      (match !outfile with
       | None   -> ()
       | Some _ -> (match !mode with `Default -> () | _ -> Printf.printf "Output file option ignored in this mode.\n")
      );           
      if !version then Printf.printf "%s\n" Version.version;
      if !help    then Printf.printf "%s" help_string
    method get_debug =
      if !debug then "" else "-g"
    method set_debug =
      debug := true     
  end

let checkLoggerIfError = fun () ->
    if Language.Logger.has_errors ()
    then (Printf.eprintf "Errors occured!\n%s\n" (Language.Logger.show ()); exit 255)
    
let outputWarnings = fun() ->
    if Language.Logger.has_warnings ()
    then Printf.eprintf "Warnings occured!\n%s\n" (Language.Logger.show ())

let outputInfos = fun() ->
    if Language.Logger.has_infos ()
    then Printf.eprintf "%s\n" (Language.Logger.show ())
  
let main =
  try 
    let cmd = new options Sys.argv in
    cmd#greet;
    Language.Logger.clear; (* Initialize logger for collecting messages *)
    let parseResult = try parse cmd with Language.Semantic_error msg -> `Fail msg in
    match parseResult with
    | `Ok untyped_prog ->
       checkLoggerIfError (); (* If errors occured, tear down *)
       let prog = if cmd#get_typecheck then Typecheck.typecheck untyped_prog else untyped_prog in
       checkLoggerIfError();
       cmd#dump_AST (snd prog);
       (match cmd#get_mode with
        | `Default | `Compile ->
            ignore @@ X86.build cmd prog;
            checkLoggerIfError();
        | _ -> 
  	   let rec read acc =
	     try
	       let r = read_int () in
	       Printf.printf "> ";
	       read (acc @ [r])
             with End_of_file -> acc
	   in 
	   let input = read [] in
	   let output =
	     if cmd#get_mode = `Eval
	     then Language.eval prog input
	     else SM.run (SM.compile cmd prog) input
	   in
       checkLoggerIfError();
	   List.iter (fun i -> Printf.printf "%d\n" i) output 
       );
       outputWarnings() (* At last, output warnings if any *)
    | `Fail er -> Printf.eprintf "Fatal error: %s\n" er; exit 255
  with
  | Language.Semantic_error msg -> Printf.printf "Error: %s\n" msg; exit 255 
  | Commandline_error msg -> Printf.printf "%s\n" msg; exit 255
