module FStar.Tactics.Typeclasses

(* TODO: This must be in the FStar.Tactics.* namespace or we fail to build
 * fstarlib. That seems silly, but I forget the details of the library split. *)

open FStar.Tactics
module T = FStar.Tactics

(* The attribute that marks instances *)
irreducible
let instance : unit = ()

let rec first (f : 'a -> Tac 'b) (l : list 'a) : Tac 'b =
    match l with
    | [] -> fail "no cands"
    | x::xs -> (fun () -> f x) `or_else` (fun () -> first f xs)

(* TODO: loop detection (and memoization?) *)
let rec tcresolve () : Tac unit =
    local `or_else` (fun () -> global `or_else` (fun () -> fail "Typeclass resolution failed"))
and local () : Tac unit =
    let bs = binders_of_env (cur_env ()) in
    first (fun b -> trywith (pack (Tv_Var (bv_of_binder b)))) bs
and global () : Tac unit =
    let cands = lookup_attr (`instance) (cur_env ()) in
    first (fun fv -> trywith (pack (Tv_FVar fv))) cands
and trywith t : Tac unit =
    debug ("Trying to apply hypothesis/instance: " ^ term_to_string t);
    (fun () -> apply t) `seq` tcresolve

(* Solve an explicit argument by typeclass resolution *)
unfold let solve (#a:Type) (#[tcresolve ()] ev : a) : Tot a = ev

(**** Generating methods from a class ****)

let rec drop (n:nat) l =
  if n = 0 then l
  else match l with
       | [] -> []
       | x::xs -> drop (n-1) xs

let remove s1 s2 =
  (* FIXME, should check that s1 is a prefix of s2 *)
  String.substring s2 (String.strlen s1) (String.strlen s2 - String.strlen s1)
let _ = assert_norm (remove "a" "abc" == "bc")

let rec mk_abs (bs : list binder) (body : term) : Tac term (decreases bs) =
    match bs with
    | [] -> body
    | b::bs -> pack (Tv_Abs b (mk_abs bs body))

let binder_to_term (b : binder) : Tac term =
  let bv, _ = inspect_binder b in
  pack (Tv_Var bv)

let rec last (l : list 'a) : Tac 'a =
  match l with
  | [] -> fail "last: empty list"
  | [x] -> x
  | _::xs -> last xs

let mk_class (nm:string) : Tac unit =
    (* sigh *)
    let ns = String.split ['.'] nm in
    let r = lookup_typ (cur_env ()) ns in
    guard (Some? r);
    let Some se = r in
    let sv = inspect_sigelt se in
    guard (Sg_Inductive? sv);
    let Sg_Inductive name us params ty ctors = sv in
    (* dump ("got it, name = " ^ String.concat "." name); *)
    (* dump ("got it, ty = " ^ term_to_string ty); *)
    let ctor_name = last name in
    // Must have a single constructor
    guard (List.length ctors = 1);
    let [ctor] = ctors in
    let r = lookup_typ (cur_env ()) ctor in
    guard (Some? r);
    let res = Some?.v r in
    let r = inspect_sigelt res in
    guard (Sg_Constructor? r);
    let Sg_Constructor _ ty = r in
    (* dump ("got ctor " ^ String.concat "." ctor ^ " of type " ^ term_to_string ty); *)
    let bs, cod = collect_arr_bs ty in
    let r = inspect_comp cod in
    guard (C_Total? r);
    let C_Total cod _ = r in (* must be total *)
    (* The constructor of course takes the parameters of the record
     * as arguments, but we should ignore them here *)
    let ps, bs = List.Tot.splitAt (List.length params) bs in

    (* print ("n_univs = " ^ string_of_int (List.length us)); *)

    let base : string = "__proj__Mk" ^ ctor_name ^ "__item__" in

    (* Make a sigelt for each method *)
    T.iter (fun b ->
                  (* dump ("b = " ^ term_to_string (type_of_binder b)); *)
                  let s = name_of_binder b in
                  let s = remove "__fname__" s in (* unmangle *)
                  (* dump ("b = " ^ s); *)
                  let ns = cur_module () in
                  let sfv = pack_fv (ns @ [s]) in
                  let dbv = fresh_bv_named "d" cod in
                  let tcr = (`tcresolve) in
                  let tcdict = pack_binder dbv (Q_Meta tcr) in
                  let bs = ps @ [tcdict] in
                  (* let ty = mk_tot_arr bs (type_of_binder b) in *)
                  let ty = pack Tv_Unknown in (* Just leave it to inference *)
                  let proj = pack (Tv_FVar (pack_fv (cur_module () @ [base ^ s]))) in
                  let def : term = mk_abs bs (mk_e_app proj [binder_to_term tcdict]) in
                  let ty : term = ty in
                  let def : term = def in
                  let sfv : fv = sfv in
                  let se = pack_sigelt (Sg_Let false sfv us ty def) in
                  //let se = set_sigelt_attrs [`tcnorm] se in
                  (* print ("trying to return : " ^ term_to_string (quote se)); *)
                  add_elem (fun () -> exact (quote se));
                  ()
    ) bs;
    apply (`Nil)
