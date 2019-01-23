type exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

type program = exp

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ " ^ ")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty ->
	match e with
	| CONST n -> [(ty, TyInt)]
	| VAR v -> [(ty, (TEnv.find tenv v))]
	| ADD (e1, e2) -> let l1 = (gen_equations tenv e1 TyInt) in
										let l2 = (gen_equations tenv e2 TyInt) in
										[(ty, TyInt)] @ l1 @ l2
	| SUB (e1, e2) -> let l1 = (gen_equations tenv e1 TyInt) in
                    let l2 = (gen_equations tenv e2 TyInt) in
                    [(ty, TyInt)] @ l1 @ l2
	| MUL (e1, e2) -> let l1 = (gen_equations tenv e1 TyInt) in
                    let l2 = (gen_equations tenv e2 TyInt) in
                    [(ty, TyInt)] @ l1 @ l2
	| DIV (e1, e2) -> let l1 = (gen_equations tenv e1 TyInt) in
                    let l2 = (gen_equations tenv e2 TyInt) in
                    [(ty, TyInt)] @ l1 @ l2
	| ISZERO e1 -> let l1 = (gen_equations tenv e1 TyInt) in
								 [(ty, TyBool)] @ l1
	| IF (e1, e2, e3) -> let l1 = (gen_equations tenv e1 TyBool) in
											 let l2 = (gen_equations tenv e2 ty) in
											 let l3 = (gen_equations tenv e3 ty) in
											 l1 @ l2 @ l3
	| LET (x1, e1, e2) -> let aa = fresh_tyvar () in
												let l1 = (gen_equations tenv e1 aa) in
												let l2 = (gen_equations (TEnv.extend (x1, aa) tenv) e2 ty) in
												l1 @ l2 
	| LETREC (f1, x1, e1, e2) -> let a1 = fresh_tyvar () in
															 let a2 = fresh_tyvar () in
															 let ttenv = (TEnv.extend (f1, TyFun (a2, a1)) tenv) in
															 let l1 = (gen_equations (TEnv.extend (x1, a2) ttenv) e1 a1) in
															 let l2 = (gen_equations (TEnv.extend (f1, TyFun (a2, a1)) tenv) e2 ty) in
															 l1 @ l2
  | PROC (x1, e1) -> let a1 = fresh_tyvar () in
										 let a2 = fresh_tyvar () in
										 let l1 = (gen_equations (TEnv.extend (x1, a1) tenv) e1 a2) in
										 [(ty, TyFun (a1, a2))] @ l1
	| CALL (e1, e2) -> let aa = fresh_tyvar () in
										 let l1 = (gen_equations tenv e1 (TyFun (aa, ty))) in
										 let l2 = (gen_equations tenv e2 aa) in
										 l1 @ l2

let solve : typ_eqn -> Subst.t
=fun eqns -> 
  let subst_initial = Subst.empty in
  let rec unify : (typ * typ * Subst.t) -> Subst.t
  =fun (t1, t2, subst1) ->
	let rec var_occur : (typ * typ) -> bool
	= fun (typ1, typ2) -> 
	match (typ1, typ2) with
	| (TyVar a1, TyInt) -> true
	| (TyVar a1, TyBool) -> true
	| (TyVar a1, TyVar b1) -> if (a1 = b1) then false else true
	| (TyVar a1, TyFun (TyVar va, TyVar vb)) -> if (a1 = va || a1 = vb) then false
																					 	  else true
	| (TyVar a1, TyFun (TyVar va, TyInt)) -> if (a1 = va) then false else true
  | (TyVar a1, TyFun (TyVar va, TyBool)) -> if (a1 = va) then false else true
	| (TyVar a1, TyFun (TyInt, TyVar vb)) -> if (a1 = vb) then false else true
	| (TyVar a1, TyFun (TyBool, TyVar vb)) -> if (a1 = vb) then false else true
	| (TyVar a1, TyFun (TyFun (f1, f2), TyInt)) -> (var_occur (TyVar a1, f1)) && (var_occur (TyVar a1, f2))
	| (TyVar a1, TyFun (TyFun (f1, f2), TyBool)) -> (var_occur (TyVar a1, f1)) && (var_occur (TyVar a1, f2))
	| (TyVar a1, TyFun (TyFun (f1, f2), TyVar va)) -> (var_occur (TyVar a1, f1)) && (var_occur (TyVar a1, f2)) && (a1 <> va)
	| (TyVar a1, TyFun (TyFun (fa1, fa2), TyFun (fb1, fb2))) -> (var_occur (TyVar a1, fa1)) && (var_occur (TyVar a1, fa2)) && (var_occur (TyVar a1, fb1)) && (var_occur (TyVar a1, fb2))
	| (TyVar a1, TyFun (typ1, TyFun (f1, f2))) -> (var_occur (TyVar a1, (TyFun (TyFun (f1, f2), typ1))))
	| _ -> true
	in
  begin
    match (t1, t2, subst1) with
    | (TyInt, TyInt, subst1) -> subst1
    | (TyBool, TyBool, subst1) -> subst1
		| (TyVar aa, TyInt, subst1) -> Subst.extend aa TyInt subst1
    | (TyVar aa, TyBool, subst1) -> Subst.extend aa TyBool subst1
		| (TyVar aa, TyVar tyvar1, subst1) -> Subst.extend aa (TyVar tyvar1) subst1
		| (TyVar aa, TyFun (typa, typb), subst1) -> if (var_occur (TyVar aa, TyFun (typa, typb)) = false) 
																								then (raise TypeError)
																								else 
																								Subst.extend aa (TyFun (typa, typb)) subst1
		| (t11, TyVar aa, subst1) -> unify (TyVar aa, t11, subst1)
    | (TyFun (tt1, tt2), TyFun (tt11, tt22), subst1) ->
      let subst11 = unify (tt1, tt11, subst1) in
      let tt3 = Subst.apply tt2 subst11 in 
      let tt4 = Subst.apply tt22 subst11 in
      unify (tt3, tt4, subst11)
    | (_, _, _) -> (raise TypeError)
  end in
  let rec unifyall : typ_eqn -> Subst.t -> Subst.t
  =fun typ_eq sub ->
	begin
		match typ_eq with
    | [] -> sub
    | (typ1, typ2) :: tl -> let sub1 = unify ((Subst.apply typ1 sub), (Subst.apply typ2 sub), sub) 
														in unifyall tl sub1
	end in
  unifyall eqns subst_initial 

let typeof : exp -> typ (* Do not modify this function *)
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns;
          print_endline "" in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
   print_endline "= Substitution = ";
    Subst.print subst;
    print_endline "";
    print_endline ("Type: " ^ string_of_type ty);
    print_endline "";
    ty
