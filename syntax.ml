type id = VString of string

type binOp = OpAdd | OpSub | OpMul | OpDiv | OpEq | OpL

type value = VInt of int | VBool of bool | VId of id | VList of value * value | VNil | VPair of value list |VFun of id * envir * expr | VRecFun of id * id * envir * expr | VRecFunAnd of int * id * id * envir * expr | VRecFun2 of int * id * id * envir * expr | VRecFun3 of int * (id * id * expr) list * envir

and envir = (id * value) list

and command_result = (*value * envirのはずだった*)CValue of value | CLet of id | CLetRecAnd of id list

and pat = Pv of value | Pl of pat * pat | Pp of pat list

and expr = EValue of value
           |ECons of expr * expr (*リストの式*)
           |ENil
           |EPair of expr list (*組の形式*)
           |EBin of binOp * expr * expr
           |IfElse of expr * expr * expr
           |EId of id
           |LetIn of id * expr * expr
           |EFun of id * expr
           |EApp of expr * expr
           |ERecIn of (id * id * expr * expr)
           |EMatch of (expr * ((pat * expr) list))
           |ERecAndIn of ((id * id * expr) list) * expr
                       
type thunk = expr * nenvir

and name_value = NVInt of int | NVBool of bool | NVId of id | NVList of value * value | VNil | NVPair of value list |NVFun of id * envir * expr | NVRecFun of id * id * envir * expr | NVRecFunAnd of int * id * id * envir * expr | NVRecFun2 of int * id * id * envir * expr | NVRecFun3 of int * (id * id * expr) list * envir | NVThunk of thunk

and nenvir = (id * thunk) list

type command = CExp of expr | Let of id * expr |LetRec of id * id * expr |LetRecAnd of (id * id * expr) list

type ty = TInt | TBool | TFun of ty * ty | TVar of string |TPair of ty list | TList of ty

type ty_subst = (string * ty) list

type ty_constraints = (ty * ty) list

type ty_env = (id * ty) list

let raelength = ref 0
let recandenvs = ref []
let templength = ref 0
let temprae = ref []
let saving = ref []

let tv = ref 0

let print_bin:binOp -> unit  = function
   OpAdd -> print_string "OpAdd,"
  |OpSub -> print_string "OpSub,"
  |OpMul -> print_string "OpMul,"
  |OpDiv -> print_string "OpDiv,"
  |OpEq -> print_string "OpEq,"
  |OpL -> print_string "OpL,"

exception Eval_error
exception ID_error
exception Print_error
exception Match_error
exception ID_Match_error
exception SFunc_error
exception Func_error
exception Retf_error
exception Funenvs_error
exception Funev_error

exception Unify_error
exception Occur_error

exception Unbound_value

let rec idenvmatch: id -> envir -> value = fun i -> fun e -> match e with
 [] -> raise ID_Match_error
|(d, v) :: rest -> if i = d then v else idenvmatch i rest;;

let rec find_match (p:pat) (v:value) : envir option = match (p, v) with
 (Pp lp, VPair lv) -> (if List.length lp = List.length lv then (match (lp, lv) with
      ([], []) -> Some []
     |((px :: prest), (vx :: vrest)) -> (match (find_match px vx) with
             None -> None
             |Some l -> (match (find_match (Pp prest) (VPair vrest)) with
                 None -> None
                 |Some ll -> Some (l @ ll)))
     |_ -> None)
                      else None)
 |(Pv pv, v) -> (match (pv, v) with
   (VInt pi, VInt vi) -> if pi = vi then Some [] else None
  |(VBool pb, VBool vb) -> if pb = vb then Some [] else None
  |(VId pi, v) -> Some ((pi, v) :: [])
  |(VNil, VNil) -> Some []
  |(_, _) -> None)
 |(Pl (p1, p2), VList (v1, v2)) -> (match find_match p1 v1 with
   None -> None
  |Some l -> (match find_match p2 v2 with
    None -> None
   |Some ll -> Some (l @ ll)))
 |(_, _) -> None;;

let rec eval:expr -> envir -> value = fun e -> fun env ->
match e with
 EValue v -> v
|EBin (op, a, b) -> (match op with (*match (op, eval a env, eval b env) with~*)
  OpAdd -> (match (eval a env, eval b env) with
   (VInt ia, VInt ib) -> VInt (ia+ib)
  |(_, _) -> raise Eval_error)
 |OpSub -> (match (eval a env, eval b env) with
   (VInt ia, VInt ib) ->  VInt (ia-ib)
  |(_, _) -> raise Eval_error)
 |OpMul -> (match (eval a env, eval b env) with
   (VInt ia, VInt ib) ->  VInt (ia*ib)
  |(_, _) -> raise Eval_error)
 |OpDiv -> (match (eval a env, eval b env) with
   (VInt ia, VInt ib) ->  VInt (ia/ib)
  |(_, _) -> raise Eval_error)
 |OpEq -> (match (eval a env, eval b env) with
   (VInt ia, VInt ib) ->  VBool (ia=ib)
  |(_, _) -> raise Eval_error)
 |OpL -> (match (eval a env, eval b env) with
   (VInt ia, VInt ib) ->  VBool (ia<ib)
  |(_, _) -> raise Eval_error)
 )
|IfElse (b, t, f) -> (match (eval b env) with
  VBool bo -> if bo then (eval t env) else (eval f env)
 |_ -> raise Eval_error)
|EId i -> idenvmatch i env
|LetIn (i, v, x) ->
  eval x ((i, eval v env) :: env)
|EFun (a, b) -> VFun (a, env, b)
|EApp (a, b) -> (match eval a env with
  VFun (i, en, ex) -> eval ex ((i, (eval b env)) :: en)
 |VRecFun (f, x, en, ex) -> eval ex ((x, (eval b env)) ::
                                    (f, VRecFun (f, x, en, ex)) :: en)
                                    (*get_andlist !temprae !templength !templength) @ en*)
 |VRecFunAnd (n, f, x, en, ex) -> eval ex (((x, eval b env)) ::
                                          (f, VRecFunAnd (n, f, x, en, ex)) ::
                                          (get_andlist !recandenvs n !raelength) @ en)
 |VRecFun2 (n, f, x, en, ex) -> eval ex ((x, (eval b env)) ::
                                        (f, VRecFun2 (n, f, x, en, ex)) ::
                                        (get_andlist !temprae n !templength) @ en)
 |VRecFun3 (n, l, en) -> let (fid, xid, exp) = get_func n l in
                         saving := [];
                         eval exp ((xid, (eval b env)) ::
                                  ((e_recandnew l l en 0)) @ en)
 |_ -> raise Eval_error)
|ERecIn (f, x, e, ex) -> eval ex ((f, VRecFun (f, x, env, e)) :: env)
|EMatch (e1, l) -> (match l with
    [] -> raise Match_error
   |(p, ex) :: rest -> (match find_match p (eval e1 env) with
      None -> eval (EMatch (e1, rest)) env
     |Some en -> eval ex (en @ env)))
|ERecAndIn (l, e)-> saving := [];(*templength := !templength + 1;temprae := [] :: !temprae;
                                  eval e ((e_recand l env !templength) @ env)*)
                                  eval e ((e_recandnew l l env 0) @ env)
|ECons (e1, e2) -> VList (eval e1 env, eval e2 env)
|ENil -> VNil
|EPair l -> VPair (List.map (fun x -> eval x env) l)

and e_recand l env n = match l with
 [] -> []
 |en :: rest -> let {contents = rae} = temprae in match en with
   (f, x, e) -> temprae := renew_andlist rae ((f, VRecFun2 (n, f, x, ((get_andlist rae n n) @ (e_recand rest env n) @ env), e)) :: get_andlist rae n n) n n;
(f, VRecFun2 (n, f, x, (get_andlist rae n n) @ env @ (e_recand rest env n), e)) :: e_recand rest env n

and get_func n l = match l with
[] -> raise Match_error
|(f, x, e) :: rest -> if n = (List.length rest) then (f, x, e) else get_func n rest

and e_recandnew l oril env n = match l with
 [] -> []
 |(f, x, e) :: rest -> saving := ((f, VRecFun3 (n, oril, (!saving @ (e_recandnew rest oril env (n+1)) @ env))) :: env);
 (f, VRecFun3 (n, oril, (!saving @ e_recandnew rest oril env (n+1) @ env))) :: (e_recandnew rest oril env (n+1))

and get_andlist (l : ((id * value) list) list) (n : int) (cn : int) : (id * value) list = match l with(*n番目のlistを取り出す*)
 [] -> []
|x :: rest -> if n = cn then x else get_andlist rest n (cn - 1)

and renew_andlist l nl n cn = match l with(*list更新*)
 [] -> []
  |x :: rest -> if n = cn then nl :: rest else x :: renew_andlist rest nl n (cn - 1);;
(*NVThunk : expr * nenvir*)
let eval_name (t : thunk) : name_value = let (e, env) = t in match e with
     EValue v -> v
    |EBin (bop, a, b) -> match bop with
                          OpAdd -> (match (eval_name (a, env), eval_name (b, env)) with
                                      (NVInt aa, NVInt bb) -> NVInt (aa + bb)
                                     |(NVThunk th, NVInt _) -> NVThunk (EBin (bop, (eval_name th), b), env)
                                     |(NVInt _, NVThunk th) -> NVThunk
                                   )
                                    
let print_id:id -> unit = function
 VString s -> print_string s;;

let rec print_value:value -> unit = function
 | VInt i -> print_int i
 | VBool b -> if b then print_string "true" else print_string "false"
 | VFun (i, en, ex) -> print_string "fun ";print_id i
 | VRecFun (f, i, en, ex) -> print_id f;print_string " = fun ";print_id i
 | VRecFunAnd (n, f, i, en, ex) -> print_string "funs ";print_int n
 | VList (l1, l2) -> print_value l1; print_string " :: "; print_value l2
 | VNil -> print_string "[]"
 | VPair p -> (match p with
     [] -> print_string "()"
    |x :: rest -> print_string "(";print_value x;List.iter (fun x -> print_string ", ";print_value x) rest;print_string ")")
 | _ -> print_int 0;;

let rec print_funs = function
 [] -> ()
|x :: rest -> print_id x;print_string " ";print_funs rest

let print_command : command_result -> unit = function
 |CValue v -> print_value v
 |CLet i -> print_string "let ";print_id i
 |CLetRecAnd l -> print_string "functions ";print_funs l





let rec alist_to_envs l env n = match l with
 |[] -> []
 |en :: rest -> (let {contents = rae} = recandenvs in match en with
   (f, x, e) -> recandenvs := renew_andlist rae ((f, VRecFunAnd (n, f, x, (get_andlist rae n n @ (alist_to_envs rest env n) @ env), e)) :: get_andlist rae n n) n n;
(f, VRecFunAnd (n, f, x, get_andlist rae n n @ env @ (alist_to_envs rest env n), e)) :: alist_to_envs rest env n
 )

let rec pick_ids = function
 |[] -> []
 |x :: rest -> match x with (f, x, e) -> f :: (pick_ids rest)

let ev:envir ref -> command -> command_result = fun env -> fun com ->
templength := 0;
temprae := [];
match com with
 CExp c -> let {contents = benv} = env in CValue (eval c benv)
|Let (i, v) -> let {contents = benv} = env in env := ((i, eval v benv) :: benv);CLet i
|LetRec (f, x, e) -> let {contents = benv} = env in env := ((f, VRecFun (f, x, benv, e)) :: benv);CLet f
|LetRecAnd l -> let {contents = benv} = env
                and {contents = len} = raelength
                and {contents = ra} = recandenvs
                in raelength := len + 1;
                   recandenvs := [] :: ra;
                   env := (alist_to_envs l benv (len + 1)) @ benv;
                   CLetRecAnd (pick_ids l);;

(*環境リストの型(id, value)*)
(*let rec f x = e
and f2 x2 = e2
and f3 x3 = e3

VRecFunを大量生成？*)

let rec print_ty (t : ty) = match t with
 TInt -> print_string "Int "
|TBool -> print_string "Bool "
|TFun (t1, t2) -> print_string "(";print_ty t1;print_string "-> ";print_ty t2;print_string ")"
|TVar s -> print_string s;print_string " "
|TPair l -> (match l with
            [] -> ()
           |x :: [] -> print_ty x;print_string " "
           |x :: rest -> print_ty x;print_string "* ";print_ty (TPair rest))
|TList lty -> print_ty lty;print_string "list "

(*apply_ty_subst ("a", TInt) :: ("b", TFun (TInt, TInt)) TVar a→TInt*)

let rec apply_sub sub t =
 match t with
 TVar a -> (match List.assoc_opt a sub with
  None -> t
 |Some st -> st
)
 |TFun (x, y) -> TFun (apply_sub sub x, apply_sub sub y)
 |_ -> t

let rec apply_ty_subst (tsub : ty_subst) (t : ty) : ty = match t with
   TVar a -> (match List.assoc_opt a tsub with
       None -> t
      |Some st -> (apply_ty_subst tsub st) )
  |TFun (x, y) -> TFun ((apply_ty_subst tsub x), (apply_ty_subst tsub y))
  |TList l -> TList (apply_ty_subst tsub l)
  |TPair l -> TPair (List.map (apply_ty_subst tsub) l)
  |_ -> t;;

(*match tsub with
 [] -> t
|x :: rest -> (match (x, t) with
   ((v, vt), TVar s) -> if v = s then vt else apply_ty_subst rest t
  |_ -> t);;*)

(*("a", tint);("b", *)
(**)

let doublesubst fl a =
 match a with
 (s, t) -> (match List.assoc_opt s fl with
   None -> true
  |Some _ -> false)

(*ts2:a->b b->e ts1:b->c a->d compose->   a->c b->c
・ts2を適用したあとにts1を適用した場合、変化が2回起こるものをまとめる
・重複していたらts2が優先*)
let compose_ty_subst (t1 : ty_subst) (t2 : ty_subst) : ty_subst =
let rec cts ts1 ts2 = match ts2 with
 [] -> ts1
(*|(s, TVar v) :: rest -> (s, apply_sub ts1 (TVar v)) :: cts ts1 rest
|(s, TFun (a, b)) :: rest -> (s, TFun ((apply_sub ts1 a), (apply_sub ts1 b))) :: cts ts1 rest*)
|(s, v) :: rest -> (s, (apply_sub ts1 v)) :: (cts ts1 rest)
in cts (List.filter (doublesubst t2) t1) t2

let print_type_constraints (l : ty_constraints) = List.iter (fun (t1, t2) -> print_string "(";print_ty t1;print_string ",";print_ty t2;print_string ")";print_newline()) l

let rec occurs_check (t : ty) (s : string) : unit =
 match t with
  TVar v when v = s -> raise Occur_error
  |TFun (a, b) -> occurs_check a s;occurs_check b s
  |_ -> ()
(*
TFun (t2, TInt),TFun (t1, t3);(t2,Int);(Int,Int)
(t2, t1) :: (TInt, t3) :: (t2, Int)
compose [s2, t1] [] -> [s2, t1]
(TInt, t3) :: (t2, Int)
compose [s3, TInt] [s2, t1] ->(s3, TInt);(s2, t1)
(t2, Int)
compose [s2, Int] (s3, TInt);(s2, t1) -> (s2, Int) (s3 Int) (s1 t2)
*)
let ty_unify (tyc : ty_constraints) : ty_subst =
let rec tu (tc : ty_constraints) (atys : ty_subst) = match tc with
[] -> atys
 |(t1, t2) :: rest when t1 = t2 -> tu rest atys
 |(TVar s1, t2) :: rest -> occurs_check t2 s1;let (a, b) = List.split rest in let aa = List.map (apply_sub [(s1, t2)]) a and bb = List.map (apply_sub [(s1, t2)]) b in tu (List.combine aa bb) (compose_ty_subst atys [(s1, t2)])(*restのs1にt2を代入*)
 |(t1, TVar s2) :: rest -> occurs_check t1 s2;let (a, b) = List.split rest in let aa = List.map (apply_sub [(s2, t1)]) a and bb = List.map (apply_sub [(s2, t1)]) b in tu (List.combine aa bb) (compose_ty_subst atys [(s2, t1)])

(*tu rest (compose_ty_subst [(s2, t1)] atys)*)
 |(TFun (a, b), TFun (c, d)) :: rest -> tu ((a, c) :: (b, d) :: rest) atys
 |(TPair l1, TPair l2) :: rest -> tu ((List.combine l1 l2) @ rest) atys
 |(TList t1, TList t2) :: rest -> tu ((t1, t2) :: rest) atys
 |_ -> raise Unify_error
in tu tyc []

let new_ty_var () : ty = tv := !tv + 1;TVar ("t" ^ string_of_int !tv)

let rec val_to_ty (te : ty_env) (i : id) : ty =
 match te with
  [] -> raise Unbound_value
 |(v, t) :: rest -> if i = v then t else val_to_ty rest i

let rec doublecons tc tt = match tc with
 [] -> true
 |x :: rest -> if tt = x then false else doublecons rest tt

let rec doubleremove l = match l with
 [] -> []
|x :: rest -> if List.mem x rest then doubleremove rest else x :: doubleremove rest

let rec make_gamma l tye = match l with
                       [] -> tye
                      |(f, x, e1) :: rest -> (f, TFun (new_ty_var (), new_ty_var ())) :: make_gamma rest tye

let rec t_beta_list l tcl g = match l with
                        [] -> []
                       |(f, x, e1) :: rest -> (match List.assoc f g with
                                               TFun (alpha, beta) -> (match tcl with
                                                                      [] -> raise Func_error
                                                                     |(t1, c1) :: rest2 -> (t1, beta) :: (t_beta_list rest rest2 g)
                                                                     )
                                              |_-> raise Func_error
                                              )
let rec e1clist l = match l with
                        [] -> []
                       |(t1, c1) :: rest -> c1 @ e1clist rest

let rec list_comb l = match l with
        [] -> []
       |x :: rest -> x @ list_comb rest

let rec gather_ty_constraints (te : ty_env) (e : expr) : ty * ty_constraints =
match e with
 EValue (VInt _) -> (TInt, [])
|EValue (VBool _) -> (TBool, [])
|EId i -> (val_to_ty te i, [])
|EBin (bop, e1, e2) -> let (t1, c1) = gather_ty_constraints te e1
                       and (t2, c2) = gather_ty_constraints te e2
                       in if bop = OpEq || bop = OpL then (TBool, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
                          else (TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
|LetIn (x, e1, e2) -> let (t, tc) = gather_ty_constraints te e1
                      in let (t2, tc2) = gather_ty_constraints ((x, t) :: te) e2
                      in (t2, tc @ tc2)
|IfElse (e1, e2, e3) -> let (t1, c1) = gather_ty_constraints te e1
                        and (t2, c2) = gather_ty_constraints te e2
                        and (t3, c3) = gather_ty_constraints te e3
                        in (t2, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3)
|EFun (x, ex) -> let ntv = new_ty_var ()
                 in let (t, c) = gather_ty_constraints ((x, ntv) :: te) ex
                 in (TFun (ntv, t), c)
|EApp (e1, e2) -> let (t1, c1) = gather_ty_constraints te e1
                  and (t2, c2) = gather_ty_constraints te e2
                  in let ntv = new_ty_var ()
                     in (ntv, (t1, TFun (t2, ntv)) :: c1 @ c2)
|ERecIn (f, x, e1, e2) -> let alpha = new_ty_var ()
                          and beta = new_ty_var ()
                          in let gamma = (f, TFun (alpha, beta)) :: te
                             in let (t1, c1) = gather_ty_constraints ((x, alpha) :: gamma) e1
                                and (t2, c2) = gather_ty_constraints gamma e2
                                in (t2, (t1, beta) :: c1 @ c2)
|ERecAndIn (li, e2) ->  let gamma = make_gamma li te(*liの要素をERecIn扱い*)
                          in let (t2, c2) = gather_ty_constraints gamma e2
                             and e1s = decide_e1 li gamma
                             in let tb = t_beta_list li e1s gamma
                                in (t2, tb @ c2 @ (e1clist e1s))
|EMatch (ex, l) -> let ret = new_ty_var () in
                   let (tex, cex) = gather_ty_constraints te ex in
                   let tyc = ematch_cons ret tex l te in
                   (ret, tyc)
|ENil -> (new_ty_var (), [])
|ECons (f, s) -> let (fty, fcon) = gather_ty_constraints te f in
                 let (sty, scon) = gather_ty_constraints te s in
                 (match sty with
                 TList ssty -> (TList fty, (fty, ssty) :: fcon @ scon)
                |_ ->  (TList fty, (fty, sty) :: fcon @ scon))
|EPair l -> (match l with
            [] -> (new_ty_var (), [])
           |x :: rest -> let (t, c) = List.split (gather_ty_constraints_pair l te) in
                                      (TPair t, list_comb c))
|_ -> raise Func_error;

and gather_ty_constraints_pair (l : expr list) (te : ty_env)= match l with
 [] -> []
|x :: rest -> (gather_ty_constraints te x) :: gather_ty_constraints_pair rest te

and gather_ty_constraints_pair_pattern (l : pat list) = match l with
 [] -> []
|x :: rest -> let (t, e, c) = gather_ty_constraints_pattern x in
              (t, (e, c)) :: (gather_ty_constraints_pair_pattern rest)

(*ret->constraints*)
and ematch_cons (t : ty) (ti : ty) (l : (pat * expr) list) (te : ty_env) : ty_constraints =
 match l with
 [] -> []
|(p, e) :: rest -> let (tp, enp, cp) = gather_ty_constraints_pattern p
                   in let (texp, cexp) = gather_ty_constraints (enp @ te) e
                   in (t, texp) :: (ti, tp) :: cp @ cexp @ ematch_cons t ti rest te

and gather_ty_constraints_pattern (p : pat) : ty * ty_env * ty_constraints =
match p with
Pv v ->  (match v with VInt _ -> (TInt, [], [])
                     |VBool _ -> (TBool, [], [])
                     |VId i -> let itv = new_ty_var () in (itv, [(i, itv)], [])
                     |VNil -> (new_ty_var (), [], [])
                     |_ -> raise Match_error)
|Pl (f, s) -> let (fty, fenv, fcon) = gather_ty_constraints_pattern f in
              let (sty, senv, scon) = gather_ty_constraints_pattern s in
              
             (match sty with(*nasi*)
             TList ssty -> (TList fty, fenv @ senv, (fty, ssty) :: fcon @ scon)
            |_ ->  (TList fty, fenv @ senv, fcon @ scon))
|Pp l -> let (t, ec) = List.split (gather_ty_constraints_pair_pattern l) in
         let (e, c) = List.split ec in
         (TPair t, list_comb e, list_comb c)
         

and decide_e1 l tye : (ty * ty_constraints) list = match l with
                       [] -> []
                      |(f, x, e1) :: rest -> (match List.assoc f tye with
                                             TFun (alpha, beta) -> (gather_ty_constraints ((x, alpha) :: tye) e1) :: decide_e1 rest tye
                                            |_ -> raise Func_error)

let rec renew_ty_env (te : ty_env) (ts : ty_subst) = match te with
 [] -> []
|(s, v) :: rest -> (s, apply_ty_subst ts v) :: renew_ty_env rest ts

let infer_expr (te : ty_env) (e : expr) : ty * ty_env =
 let (t, c)  = gather_ty_constraints te e
 in (*print_ty t;print_string " ";print_type_constraints c;*)let tuc = ty_unify c in let retty = apply_ty_subst tuc t
    in (retty, renew_ty_env te tuc)

let rec recandcons (te : ty_env) (l : (id * id * expr) list) : ty_constraints =
 match l with
 [] -> []
|(f, x, e) :: rest -> (match List.assoc f te with
                         TFun (alpha, beta) -> let (bt, nte) = gather_ty_constraints ((x, alpha) :: te) e in (beta, bt) :: nte @ recandcons te rest
                        |_ -> raise Func_error
)



let rec lra_tenv (te : ty_env) (l : (id * id * expr) list) : ty_env =
let cl = recandcons te l in
let tuc = ty_unify cl in
renew_ty_env te tuc



(*match l with
 [] -> te
|(f, x, e) :: rest -> (match List.assoc f te with
                       TFun (alpha, beta) -> let (bt, nte) = infer_expr ((x, alpha) :: te) e
                                             in lra_tenv nte rest
                      |_ -> raise Func_error)*)



let rec print_tys (te : ty_env) = match te with
 [] -> ()
|(i, t) :: rest -> print_id i;print_string ":";print_ty t;print_string "\n";print_tys rest

let infer_cmd (te : ty_env) (com : command) : ty_env * ty_env =
 match com with
  CExp e -> let (t, nte) = infer_expr te e in print_ty t;([], nte)
 |Let (i, e) -> let (t, nte) = infer_expr te e
                in ([(i, t)], (i, t) :: nte)
 |LetRec (f, x, e) -> let alpha = new_ty_var ()
                      and beta = new_ty_var ()
                      in let (t, nte) = infer_expr ((x, alpha) :: (f, TFun (alpha, beta)) :: te) e
                         in ([(f, List.assoc f nte)], nte)
 |LetRecAnd li -> let gamma = make_gamma li te
                          in (lra_tenv gamma li, lra_tenv gamma li)
                          (*in let e1s = decide_e1 li gamma
                             in let tb = t_beta_list li e1s gamma
                                in let  drl = doubleremove (tb @ (e1clist e1s))
                                in let newte = flist li (ty_unify drl) gamma
                                in ( *)

(*
type ty = TInt | TBool | TFun of ty * ty | TVar of string

type ty_subst = (string * ty) list

type ty_constraints = (ty * ty) list
*)
