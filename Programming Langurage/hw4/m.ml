exception UndefSemantics

type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
  | CALLREF of exp * var
  | SET of var * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
and env = var -> loc
and loc = int
and mem = loc -> value

(*********************************)
(* implementation of environment *)
(*********************************)
(* empty env *)
let empty_env = fun x -> raise (Failure "Environment is empty")
(* extend the environment e with the binding (x, l), where x is a varaible and l is a location *)
let extend_env (x,l) e = fun y -> if x = y then l else (e y)
(* look up the environment e for the variable x *)
let apply_env e x = e x

(*********************************)
(* implementation of memory      *)
(*********************************)
let empty_mem = fun _ -> raise (Failure "Memory is empty")
(* extend the memory m with the binding (l, v), where l is a location and v is a value *)
let extend_mem (l,v) m = fun y -> if l = y then v else (m y)
let apply_mem m l = m l

(* NOTE: you don't need to understand how env and mem work *)

let counter = ref 0

(* calling 'new_location' produces a fresh memory location *)
let new_location () = counter:=!counter+1;!counter

let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f


(* TODO: Implement this function *)
let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> 
  match exp with
  | CONST n -> (Int n, mem)
	| VAR v -> ((apply_mem mem (apply_env env v)), mem)  
  | ADD (e1, e2) -> let (v1, m1) = eval e1 env mem in
                    let (v2, m2) = eval e2 env m1 in
                    begin
                      match v1, v2 with
                      | Int n1, Int n2 -> (Int (n1 + n2), m2)
                      | _ -> raise (Failure "UndefSemantics")
                    end
  | SUB (e1, e2) -> let (v1, m1) = eval e1 env mem in
                    let (v2, m2) = eval e2 env m1 in
                    begin
                      match v1, v2 with
                      | Int n1, Int n2 -> (Int (n1 - n2), m2)
                      | _ -> raise (Failure "UndefSemantics")
                    end
  | MUL (e1, e2) -> let (v1, m1) = eval e1 env mem in
                    let (v2, m2) = eval e2 env m1 in
                    begin
                      match v1, v2 with
                      | Int n1, Int n2 -> (Int (n1 * n2), m2)
                      | _ -> raise (Failure "UndefSemantics")
                    end
  | DIV (e1, e2) -> let (v1, m1) = eval e1 env mem in
                    let (v2, m2) = eval e2 env m1 in
                    begin
                      match v1, v2 with
                      | Int n1, Int n2 -> (Int (n1 / n2), m2)
                      | _ -> raise (Failure "UndefSemantics")
                    end
  | ISZERO e1 -> let (v1, m1) = eval e1 env mem in
                 begin
                   match v1 with
                   | Int n1 -> begin
																 match n1 with
																 | 0 -> (Bool true, m1)
                                 | _ -> (Bool false, m1)
															 end
                   | _ -> raise (Failure "UndefSemantics")
                 end
  | READ -> (Int (read_int()), mem)
  | IF (e1, e2, e3) -> let (v1, m1) = eval e1 env mem in
                       begin
                         match v1 with
                         | Bool true -> let (v2, m2) = eval e2 env m1 in 
                                        (v2, m2)
                         | Bool false -> let (v2, m2) = eval e3 env m1 in
                                         (v2, m2)
                         | _ -> raise (Failure "UndefSemantics") 
                       end
	| LET (x1, e1, e2) -> let (v1, m1) = eval e1 env mem in
												let l1 = new_location () in
												let (v2, m2) = eval e2 (extend_env (x1, l1) env) (extend_mem (l1, v1) m1) in
												(v2, m2)
	| LETREC (f1, x1, e1, e2) -> let l1 = new_location () in
															 let (v1, m1)
                               = eval e2 (extend_env (f1, l1) env) (extend_mem (l1, RecClosure (f1, x1, e1, env)) mem) in
															 (v1, m1)
	| PROC (v1, e1) -> (Closure (v1, e1, env), mem)
	| CALL (e1, e2) -> let (v1, m1) = eval e1 env mem in
										 begin
											match v1 with
											| Int nn -> raise (Failure "UndefSemantics")
											| Bool bb -> raise (Failure "UndefSemantics")
											| Closure (x1, ee, p1) ->
											let (v2, m2) = eval e2 env m1 in
											let l1 = new_location () in
											let (v3, m3)
											= eval ee (extend_env (x1, l1) p1) (extend_mem (l1, v2) m2) in
											(v3, m3)
											| RecClosure (f1, x1, ee, p1) ->
											let (v2, m2) = eval e2 env m1 in
											let l1 = new_location () in
											let l2 = new_location () in
											let (v3, m3) 
											= eval ee (extend_env (x1, l1) (extend_env (f1, l2) p1)) (extend_mem (l1, v2) (extend_mem (l2, RecClosure (f1, x1, ee, p1)) m2)) in
											(v3, m3)
										 end
	| CALLREF (e1, y1) -> let (v1, m1) = eval e1 env mem in
												begin
												 match v1 with
												 | Int nn -> raise (Failure "UndefSemantics")
												 | Bool bb -> raise (Failure "UndefSemantics")
												 | Closure (x1, ee, p1) ->
												 let (v2, m2)
												 = eval ee (extend_env (x1, apply_env env y1) p1) m1 in
												 (v2, m2)
												 | RecClosure (f1, x1, ee, p1) ->
												 let l1 = new_location () in
												 let (v2, m2)
												 = eval ee (extend_env (x1, apply_env env y1) (extend_env (f1, l1) p1)) (extend_mem (l1, RecClosure (f1, x1, ee, p1)) m1) in
												 (v2, m2)
											  end
	| SET (x1, e1) -> let (v1, m1) = eval e1 env mem in
										(v1, extend_mem ((apply_env env x1), v1) m1)
	| SEQ (e1, e2) -> let (v1, m1) = eval e1 env mem in
										let (v2, m2) = eval e2 env m1 in
										(v2, m2)
	| BEGIN e1 -> eval e1 env mem

let run : program -> value
=fun pgm -> 
  let (v,m) = eval pgm empty_env empty_mem in
    v
