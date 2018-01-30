ocamlc -rectypes -o T -pp "camlp5o -I `ocamlfind -query ocanren.syntax` -I `ocamlfind -query GT.syntax.all` pa_minikanren.cmo pa_gt.cmo -L `ocamlfind -query GT.syntax.all`" -I `ocamlfind -query GT`  -I `ocamlfind -query ocanren` unix.cma GT.cma  MiniKanren.cma T.ml
 
