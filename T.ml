open GT

let concat = (@) 
let deref  = (!)

module S = Set.Make (String)
module E = Map.Make (String)
module M = Map.Make (struct type t = int let compare = (-) end)

module Term =
  struct

    @type term =
    | Var of string 
    | App of term   * term 
    | Lam of string * term with show, eq

    let (!)  x   = Var x
    let (@)  x y = App (x, y)
    let (=>) x y = Lam (x, y)

    module Stream =
      struct

	type 'a t = ('a * 'a t) Lazy.t
	  
	let cons a t = lazy (a, t)
	    
	let take = Lazy.force 
	let hd s = Lazy.force s |> fst
	let tl s = Lazy.force s |> snd
	  
	let rec map f s = lazy (f (hd s), map f (tl s))
	    
	let rec prepend l s =
	  match l with 
	  | []    -> s 
	  | h::tl -> cons h (prepend tl s)
		
	let rec bind_list f s = 
	  let h, t = take s in prepend (f h) (Lazy.from_fun (fun () -> Lazy.force (bind_list f t)))
	    
      end

    let rec is_nf = function
    | App (Lam _, _) -> false
    | App (a, b)     -> is_nf a && is_nf b
    | Var _          -> true
    | Lam (_, a)     -> is_nf a
	
    let rec fv = function
    | Var x -> S.singleton x
    | App (x, y) -> S.union (fv x) (fv y)
    | Lam (x, y) -> S.remove x @@ fv y

    let fresh_var = 
      let letters = 
	let rec loop acc i = 
	  if i > Char.code 'z' 
	  then List.rev acc
	  else loop (String.make 1 (Char.chr i) :: acc) (i+1) 
	in
	loop [] (Char.code 'a')
      in
      let rec idents () = 
	Lazy.force (Stream.bind_list (fun l -> List.map (fun x -> x ^ l) letters) (Stream.cons "" (Lazy.from_fun idents)))
      in
      let idents = Lazy.from_fun idents in
      fun s ->
	let rec iterate t =
	  let h, t = Stream.take t in
	  if S.mem h s then iterate t else h
	in
	iterate idents

    let rec subst a x b =
      let fvb = fv b in
      match a with
      | App (m, n) -> App (subst m x b, subst n x b)
      | Lam (y, m) when y <> x ->
	  if S.mem y fvb 
	  then 
	    let z = fresh_var (S.add y fvb) in
	    Lam (z, subst (subst m y (Var z)) x b)
	  else Lam (y, subst m x b)
      | Var y when y = x -> b
      | _ -> a

    let _ =
      Printf.printf "Substitution:\n%!";
      Printf.printf "=============\n%!";
      Printf.printf "%s\n%!" (show(term) @@ subst (!"x") "y" (!"z"));
      Printf.printf "%s\n%!" (show(term) @@ subst (!"x") "x" (!"z"));
      Printf.printf "%s\n%!" (show(term) @@ subst ("x" => !"x") "x" (!"z"));
      Printf.printf "%s\n%!" (show(term) @@ subst ("y" => !"x") "x" (!"z"));
      Printf.printf "%s\n%!" (show(term) @@ subst ("y" => !"x") "x" (!"y"));
      Printf.printf "\n%!"

    let id    = "x" => !"x"
    let app   = "f" => ("x" => !"f" @ !"x")
    let omega = ("x" => !"x" @ !"x") @ ("x" => !"x" @ !"x")
    let y     = "f" => (("x" => (!"f" @ !"x") @ !"x") @ ("x" => (!"f" @ !"x") @ !"x"))
    let z     = "f" => id
    let one   = app
    let two   = "f" => ("x" => !"f" @ !"f" @ !"x")
    let three = "f" => ("x" => !"f" @ !"f" @ !"f" @ !"x")
    let add   = "m" => ("n" => ("f" => ("x" => (!"m" @ !"f") @ ((!"n" @ !"f") @ !"x"))))
    let mul   = "m" => ("n" => ("f" => ("x" => (!"m" @ (!"n" @ !"f")) @ !"x")))

    let _ = 
      Printf.printf "Terms:\n%!";
      Printf.printf "======\n%!";
      Printf.printf "%s\n%!" (show(term) (!"x"));
      Printf.printf "%s\n%!" (show(term) (!"x" @ !"y"));
      Printf.printf "%s\n%!" (show(term) ("x" => ("y" => !"x" @ !"y")));
      Printf.printf "%s\n%!" (show(term) id);
      Printf.printf "%s\n%!" (show(term) app);
      Printf.printf "%s\n%!" (show(term) y);
      Printf.printf "%s\n%!" (show(term) z);
      Printf.printf "%s\n%!" (show(term) add);
      Printf.printf "%s\n%!" (show(term) mul);
      Printf.printf "\n%!"

  end

module DeBruijn =
  struct

    @type term = Free of string | Var of int | App of term * term | Lam of term with show, eq, foldl

    let of_term t =
      let rec inner ((e, d) as env) = function
      | Term.App (m, n) -> App (inner env m, inner env n)
      | Term.Var  x     -> (try Var (d - (E.find x e) - 1) with Not_found -> Free x)
      | Term.Lam (x, m) -> Lam (inner (E.add x d e, d+1) m)
      in
      inner (E.empty, 0) t

    let fv t = transform(term) (object inherit [S.t] @term[foldl]
				  method c_Free s _ n = S.add n s
                                end) S.empty t
     
    let to_term t = 
      let rec inner s e d = function
      | Free x     -> Term.Var x, s
      | Var i      -> Term.Var (M.find (d - i - 1) e), s
      | Lam n      -> let z = Term.fresh_var s in
	              let n', s = inner (S.add z s) (M.add d z e) (d+1) n in
		      Term.Lam (z, n'), s
      | App (n, m) -> let n', s = inner s e d n in
	              let m', s = inner s e d m in
		      Term.App (n', m'), s
      in
      inner (fv t) M.empty 0 t |> fst

    let _ = 
      Printf.printf "DeBruijn:\n%!";
      Printf.printf "=========\n%!";
      Printf.printf "%s\n%!" (show(term) @@ of_term Term.id);
      Printf.printf "%s\n%!" (show(term) @@ of_term Term.app);
      Printf.printf "%s\n%!" (show(term) @@ of_term Term.y);
      Printf.printf "%s\n%!" (show(term) @@ of_term Term.z);
      Printf.printf "%s\n%!" (show(term) @@ of_term Term.add);
      Printf.printf "%s\n%!" (show(term) @@ of_term Term.mul);
      Printf.printf "\n%!";
      Printf.printf "%s\n%!" (show(Term.term) (Term.id |> of_term |> to_term));
      Printf.printf "%s\n%!" (show(Term.term) (Term.app |> of_term |> to_term));
      Printf.printf "%s\n%!" (show(Term.term) (Term.y |> of_term |> to_term));
      Printf.printf "%s\n%!" (show(Term.term) (Term.z |> of_term |> to_term));
      Printf.printf "%s\n%!" (show(Term.term) (Term.add |> of_term |> to_term));
      Printf.printf "%s\n%!" (show(Term.term) (Term.mul |> of_term |> to_term));
      Printf.printf "\n%!"

  end

module Semantics1 =
  struct

    open Term

    module BigStep =
      struct

	let rec wnf = function
	  | App (m, n) ->
	      (match wnf m with
	      | Lam (x, m') -> wnf (subst m' x n)
	      | m'          -> App (m', n)
	      )
	  | t -> t
		
	let _ =
	  let doit t = 
	    Printf.printf "%s == wnf ==> %s\n%!" (show(term) t) (show(term) @@ wnf t)
	  in
	  Printf.printf "WNF:\n%!";
	  Printf.printf "====\n%!";
	  doit (id @ !"z");
	  doit ((app @ id) @ !"q");
	  doit y;
	  Printf.printf "\n%!"
	    
	let name = "BigStep"

	let rec eval = function
	| Lam (x, m) -> Lam (x, eval m)
	| App (m, n) ->
	    (match wnf m with
	     | Lam (x, m') -> eval (subst m' x n)
	     | m' -> App (eval m', eval n)
	    )
	| t -> t
		
      end

    module SmallStep =
      struct

	let rec step = 
	  function
	  | App (Lam (x, m), n) -> `Continue (subst m x n)
	  | App (m, n)          -> 
	      (match step m with
	       | `Continue m' -> `Continue (App (m', n))
	       | `NF _ -> 
		   (match step n with
		    | `NF _        -> `NF (App (m, n))
		    | `Continue n' -> `Continue (App (m, n'))
		   )
	      )

	  | Lam (x, m) as t -> 
	      (match step m with
	       | `NF       _ -> `NF t
	       | `Continue m' -> `Continue (Lam (x, m'))
	      )
	  | t -> `NF t

	let name = "SmallStep"

	let eval t =
	  let rec loop t =
	    match step t with
	    | `NF       t -> t
	    | `Continue t -> loop t
	  in
	  loop t

      end

  end

module Semantics2 =
  struct

    open Term

    @type flag = T | F with show
    type env  = (term * env) E.t

    let rec show_env e = 
      let es = E.bindings e in
      show(list) (show(pair) (show(string)) (show(pair) (show(term)) show_env)) es

    let rec fve e =
      E.fold (fun _ (t, e) s -> S.union s (S.union (fve e) (fv t))) e S.empty

    let lookup e x = 
      try `Bound (E.find x e) 
      with Not_found -> `Free

    let free e x = E.remove x e

    let empty = E.empty
    let extend e x v = E.add x v e

    let rename x m e =
      let fve = fve e in
      if S.mem x fve 
      then let z = fresh_var fve in z, subst m x (Var z) 
      else x, m

    let name = "With Environment"

    let rec refine t e = 
      E.fold (fun x (t, e) term -> subst term x (refine t e)) e	t
      
    let eval t =      
      let rec eval t f e = 
	match t with
	| Var x -> 
	    (match lookup e x with
	     | `Free           -> t, empty
	     | `Bound (t', e') -> eval t' f e'
	    )
	| Lam (x, m) when f = T -> let x, m = rename x m e in Lam (x, m), e
	| Lam (x, m) -> 
	    let x, m = rename x m e in
	    let m', e' = eval m f @@ free e x in
	    Lam (x, m'), e
	| App (m, n) -> 
	    let m', e' = eval m T e in 
	    (match m' with
             | Lam (x, m') -> eval m' f @@ extend e' x (n, e) 
	     | _ -> let n', _ = eval n F e in App (m', n'), e
	    )
      in
      let t, e = eval t F empty in
      refine t e

  end

module Semantics3 =
  struct

    open Term

    type flag = Semantics2.flag = T | F
    type env  = Semantics2.env

    let empty  = Semantics2.empty
    let extend = Semantics2.extend
    let free   = Semantics2.free
    let refine = Semantics2.refine 
    let lookup = Semantics2.lookup
    let rename = Semantics2.rename

    let id x = x

    let name = "Tail-Recursive"

    let eval t =      
      let rec eval t f e k = 
	match t with
	| Var x -> 
	    (match lookup e x with
	     | `Free           -> k (t, empty) 
	     | `Bound (t', e') -> eval t' f e' k
	    )
	| Lam (x, m) when f = T -> let x, m = rename x m e in k (Lam (x, m), e)
	| Lam (x, m) -> let x, m = rename x m e in eval m f (free e x) (fun (m', e') -> k (Lam (x, m'), e))
	| App (m, n) -> 
	    eval m T e 
	      (fun (m', e') -> 
		 match m' with
		 | Lam (x, m') -> eval m' f (extend e' x (n, e)) k
		 | _ -> eval n F e (fun (n', _) -> k (App (m', n'), e))
	      )
      in
      let t, e = eval t F empty id in
      refine t e

  end

module Semantics4 =
  struct

    open Term

    type flag = Semantics2.flag = T | F
    type env  = Semantics2.env

    let empty  = Semantics2.empty
    let extend = Semantics2.extend
    let free   = Semantics2.free
    let lookup = Semantics2.lookup
    let rename = Semantics2.rename

    let name = "History & Environment"

    let rec show_history h =
      show(list) 
	(fun ((t, f, e, ch), c) -> 
           Printf.sprintf "(%s, %s, %s, %s)" (show(term) t) (show(Semantics2.flag) f) (Semantics2.show_env e) (show(bool) (deref c))
	)
	h

    let reconstruct h =
      let rec reconstruct stack = function
      | [] -> List.hd stack
      | (it, c) :: hs ->
          if deref c 
	  then
	    match it with
	    | (Var _ as x, _, _, _) -> reconstruct (x::stack) hs
	    | (App _     , _, _, _) -> let l::r::stack' = stack in reconstruct (App (l, r) :: stack') hs
	    | (Lam (x, _), _, _, _) -> let m::stack'    = stack in reconstruct (Lam (x, m) :: stack') hs
	  else reconstruct stack hs
    in
    reconstruct [] h

    let eval t =
      let mark    c  = c := true in
      let default () = ref false in
      let rec eval ((it, c) :: hs) as h =
	match it with
	| (Var x as t, f, e, ch) ->
	    (match lookup e x with
	     | `Free -> 
                mark c; 
                apk t empty ch h
	     | `Bound (t', e') -> 
                eval (((t', f, e', ch), default ()) :: h)
	    )
        | (Lam (x, m), F, e, ch) -> 
            let x, m = rename x m e in 
            mark c; 
            eval (((m, F, free e x, ch), default ()) :: ((Lam (x, m), F, e, ch), c) :: hs)
	| (Lam (x, m) as t, f, e, ch) -> apk t e ch h 
	| (App (m, n), f, e, ch) -> eval (((m, T, e, h), default ()) :: h)
      and apk t e ch h =
        match ch with
	| [] -> reconstruct h
	| ((App (m, n), f, e', ch'), c') :: _ ->
	    let f = function
	    | Lam (x, m) -> ((m, f, extend e x (n, e'), ch'), default ())
	    | _  -> 
               mark c'; 
               ((n, F, e', ch'), default ())
	    in
	    eval (f t :: h)
      in
      eval [(t, F, empty, []), default ()]

  end

module Semantics5 =
  struct

    open DeBruijn

    type flag = Semantics2.flag = T | F

    let name = "UNP"

    let rec show_history h =
      show(list) 
	(fun ((t, f, bh, ch), c) -> 
           Printf.sprintf "(%s, %s, %s)" (show(term) t) (show(Semantics2.flag) f) (*Semantics2.show_env e*) (show(bool) (deref c))
	)
	h

    let reconstruct h =
      let rec reconstruct stack = function
      | [] -> List.hd stack
      | (it, c) :: hs ->
          if deref c 
	  then
	    match it with
	    | (Var  i as x, _, bh, _) -> 
		let rec recalculate_index bh = function
		| 0 -> 0
		| i -> let ((_, _, bh, _), c) :: _ = bh in
		       (if deref c then 1 else 0) + recalculate_index bh (i-1)
		in		
		reconstruct (Var (recalculate_index bh i)::stack) hs
	    | (Free _ as x, _, _, _) -> reconstruct (x::stack) hs
	    | (App _     , _, _, _) -> let l::r::stack' = stack in reconstruct (App (l, r) :: stack') hs
	    | (Lam _     , _, _, _) -> let m::stack'    = stack in reconstruct (Lam m :: stack') hs
	  else reconstruct stack hs
    in
    reconstruct [] h

    let eval t =
      let mark    c  = c := true  in
      let unmark  c  = c := false in
      let default () = ref false  in
      let marked  () = ref true   in
      let rec eval ((it, c) :: hs) as h =
	match it with
	| (Free _ as t, f, bh, ch) -> mark c; apk t ch h
	| (Var  i     , f, bh, ch) -> lookup c f bh ch h i
        | (Lam  m     , F, bh, ch) -> mark c; eval (((m, F, h, ch), default ()) :: h) 
	| (Lam  _ as t, f, bh, ch) -> apk t ch h
	| (App (m, n) , f, bh, ch) -> mark c; eval (((m, T, bh, h), default ()) :: h)
      and lookup c f bh ch h = function
      | 0 -> 
	  (match bh with 
           | ((_, T, _, ((t, _, bh, _), _) :: _), _) :: _ -> evoperand (t, f, bh, ch) h
	   | ((_, F, _, ch'), _) :: _ -> mark c; apk (Var 0) ch h
	  )  
      | i -> let ((_, _, bh, _), _) :: _ = bh in lookup c f bh ch h (i-1)
      and apk t ch h = 
	match ch with
	| [] -> reconstruct h
	| ((t', f, bh', ch'), c) :: _ ->
          (match t with
	   | Lam t'' -> unmark c; eval (((t'', f, h, ch'), default ()) :: h)
	   | _ -> evoperand (t', F, bh', ch') h
	  )
      and evoperand (App (m, n), f, bh, ch) h = eval (((n, f, bh, ch), default ()) :: h) in
      eval [(of_term t, F, [], []), default ()] |> to_term

  end

module FelleisenStyle =
  struct

    (* C = [] | \x.C | CE | vC *)
    @type c = H | Lam of string * c | Fun of c * Term.term | Arg of Term.term * c with show

    let rec split = function
    | Term.Var  _              as t -> (H, t)
    | Term.App (Term.Lam _, _) as t -> (H, t)
    | Term.Lam (x, t) -> let (c', t') = split t in (Lam (x, c'), t')
    | Term.App (f, a) -> 
	if Term.is_nf f 
	then let (c', a') = split a in (Arg (f, c'), a')
        else let (c', f') = split f in (Fun (c', a), f')

    let rec patch_hole (c, t) =
      match c with
      | H            -> t
      | Lam (x, c')  -> Term.Lam (x, patch_hole (c', t))
      | Fun (c', t') -> Term.App (patch_hole (c', t), t')
      | Arg (t', c') -> Term.App (t', patch_hole (c', t))

    let _ =
      Printf.printf "Splitting-patching:\n%!";
      Printf.printf "===================\n%!";
      List.iter 
	(fun t -> 
	   if not @@ eq(Term.term) t (split t |> patch_hole) 
	   then failwith (Printf.sprintf "Split/patch pair mismatch for %s\n%!" @@ show(Term.term) t)
	) 
	[Term.id; Term.app; Term.omega; Term.y; Term.z; Term.mul];
      Printf.printf "Ok.\n%!"

    module Simple =
      struct

	open Term

	let name = "Simple Felleisen-style"

	let eval t =
	  let reduce = function
	  | Term.App (Term.Lam (x, a), b) -> Term.subst a x b 
	  | t -> t
	  in
	  let rec eval s t =
	    if is_nf t 
	    then match s with
	         | []      -> t
		 | c :: s' -> eval s' (patch_hole (c, t)) 
	    else 
	      let (c', t') = reduce t |> split in
              eval (c'::s) t'
	  in
	  eval [] t
	 
      end

    module WithEnvironment =
      struct

	open Term

	let name = "Felleisen-style with environment"
(*
	let eval t =
	  let pop 
	  let rec eval s e = function
	  | Term.Var x -> (match lookup e x with `Free -> | `Bound t -> eval s e t)
	  | Term.App (Term.Lam (x, a), b) ->
	    
	  in
	  eval [] t
*)	 
      end

  end

module Tests =
  struct

    module Generator =
      struct

	open MiniKanren

	@type ('string, 'self) lterm = 
	| Var of 'string
	| App of 'self * 'self
	| Lam of 'string * 'self with show, gmap

        module T = Fmap2 (struct type ('a, 'b) t = ('a, 'b) lterm let fmap f g = gmap(lterm) f g end)
        
	let (!) x = inj @@ lift x
                                
        let var x   = inj @@ T.distrib (Var x)
        let app f x = inj @@ T.distrib (App (f, x))
        let lam x f = inj @@ T.distrib (Lam (x, f))          

	let rec substo l x a l' =
	  conde [
	    fresh (y) (l === var y)(y === x)(l' === a);
	    fresh (m n m' n')
	      (l  === app m n) 
	      (l' === app m n')
	      (substo m x a m')
	      (substo n x a n');     
	    fresh (v b)
	      (l === lam v b)
	      (conde [
                (x === v) &&& (l' === l);
                fresh (b') (l' === lam v b') (substo b x a b')
	      ])    
	  ]
	    
	let rec evalo m n =
	  conde [
	    fresh (x) 
	      (m === var x)
	      (n === m);    
	    fresh (x l)
	      (m === lam x l)
	      (n === m);    
	    fresh (f a f' a') 
	      (m === app f a)
	      (conde [
                 fresh (x l l')     
                 (f' === lam x l)
                 (substo l x a' l')
                 (evalo l' n);         
                 fresh (p q) (f' === app p q) (n === app f' a');
                 fresh (x)   (f' === var x  ) (n === app f' a')
	      ])
	      (evalo f f')
	      (evalo a a')
	]

	exception Free of int

	let generate n =
 	  run q (fun q  -> evalo q (lam !"x" (var !"x")))
	        (fun qs ->  
                   Stream.take ~n:n qs |> 
                   List.map 
		     (fun lt ->
                        let prj_string = function MiniKanren.Value s -> s | MiniKanren.Var (i, _) -> string_of_int i in
                        let rec prj_term = function
			| MiniKanren.Value (Var  x) -> Term.Var (prj_string x)
			| MiniKanren.Value (App (m, n)) -> Term.App (prj_term m, prj_term n)
                        | MiniKanren.Value (Lam (x, m)) -> Term.Lam (prj_string x, prj_term m)
                        | MiniKanren.Var (i, _) -> Term.Var (string_of_int i)
			in                        
		        prj_term (lt#reify (let rec reify_term t = T.reify reify reify_term t in reify_term))
		     ) 
		)

      end

    open Term

    let terms = concat
    [
      id;
      id @ !"z";
      !"a" @ ("x" => !"b");
      (app @ id) @ !"q";
      "g" => (("x" => (!"g" @ !"x") @ !"x") @ !"q"); 
      "g" => (!"g" @ !"q");
      ("x" => (!"q" @ !"x") @ !"x") @ !"d";
      y;
      (add @ z) @ one;
      (mul @ z) @ one;
      (mul @ two) @ two;
      (("z" => !"z") @ ("x" => (!"x" @ omega) @ !"x")) @ ("x" => ("y" => !"y"))
    ] (Generator.generate 1000) 

    module type R = 
      sig 
	val name : string
	val eval : term -> term 
      end

    let run es =      
      List.fold_left
	(fun m e ->
	  let module E = (val e : R) in
	  Printf.printf "%s:\n%!" E.name;
	  Printf.printf "%s\n%!" (String.make (Printf.sprintf "%s:\n%!" E.name |> String.length) '=');
	  let m = 
	    List.fold_left
	      (fun (i, m) e -> 
		 let result  = E.eval e                in
		 let result' = DeBruijn.of_term result in
		 Printf.printf "%s ===> %s, " (show(term) e) (show(term) @@ result);
		 try 
		   let orig = M.find i m in
		   if eq(DeBruijn.term) orig result' 
		   then Printf.printf "ok\n%!"
		   else Printf.printf "********** fail ************\n%!";
		   (i+1, m)
		 with Not_found ->
		   Printf.printf "ok\n%!";
		   (i+1, M.add i result' m)		   
	      ) 
	      (0, m)
	      terms |> snd
	  in
	  Printf.printf "\n%!";
	  m
	) 
	M.empty
	es |> ignore
    
  end
	
let _ =
  Printf.printf "Testing various semantics\n%!";
  Printf.printf "=========================\n\n%!";
  Tests.run [
    (module Semantics1.BigStep    : Tests.R);
    (module Semantics1.SmallStep  : Tests.R);
    (module Semantics2            : Tests.R);
    (module Semantics3            : Tests.R);
    (module Semantics4            : Tests.R);
    (module Semantics5            : Tests.R);
    (*module FelleisenStyle.Simple : Tests.R*)
  ]

