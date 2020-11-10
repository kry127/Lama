# GraduLama
Lama programming language with Gradual Typing feature

### Interface

For 12.10.2020, Lama's `lamac` has following CLI help output:
```
$ lamac -h
Lama compiler. (C) JetBrains Reserach, 2017-2020.
Usage: lamac <options> <input file>

When no options specified, builds the source file into executable.
Options:
  -c        --- compile into object file
  -o <file> --- write executable into file <file>
  -I <path> --- add <path> into unit search path list
  -i        --- interpret on a source-level interpreter
  -s        --- compile into stack machine code and interpret on the stack machine initerpreter
  -dp       --- dump AST (the output will be written into .ast file)
  -ds       --- dump stack machine code (the output will be written into .sm file; has no
                effect if -i option is specfied)
  -v        --- show version
  -h        --- show this help
```

The task is to make one of these:
 1. Either separate utility, like `gradulama` (CLI command)
 2. Or make an additional key for `lamac` like this:
```
  -tc       --- perform typechecking
```

This command will launch typechecking on the parsed sourcefiles. For instance, we may use `let parse cmd` from `Language.ml`.
