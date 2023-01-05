(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)


// TODO implement this
let rec apply_subst (t : ty) (s : subst) : ty =
    match t with
    | TyVar x ->
        match List.tryFind ((=) x << fst) s with
        | Some (_, t) -> t
        | None -> t
    | TyArrow(f, t) -> TyArrow(apply_subst f s, apply_subst t s)
    | TyTuple args -> TyTuple <| List.map (fun x -> apply_subst x s) args
    | _ -> t

// TODO implement this
let compose_subst (s2 : subst) (s1 : subst) : subst =
    let s1 = List.map (fun (id, t) -> (id, apply_subst t s2)) s1
    // FIXME: Are infinite substitutions happening?
    s1 @ s2

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst =   
    match t1, t2 with
    | t1, t2 when t1 = t2 -> [] 
    | TyName t1, TyName t2 when t1 = t2 -> []
    | TyTuple t1s, TyTuple t2s when t1s.Length = t2s.Length ->
        let apply subst (x, y) = compose_subst (unify (apply_subst x subst)
                                                      (apply_subst y subst))
                                                subst
        List.fold apply [] <| List.zip t1s t2s
    | TyArrow(ft1, tt1), TyArrow(ft2, tt2) ->
        let args = unify ft1 ft2
        compose_subst (unify (apply_subst tt1 args)
                             (apply_subst tt2 args))
                      args
    | TyVar x, y when Set.contains x <| freevars_ty y ->
        type_error "Unification error: unifying %d with %s requires infinite types"
            x (pretty_ty y)
    | TyVar x, y -> [(x, y)]
    | _, TyVar _ -> unify t2 t1
    | _, _ -> type_error "Unification error: types '%s' and '%s' are not unifiable"
                            (pretty_ty t1) (pretty_ty t2)

let apply_subst_in_scheme (Forall(tyvars, ty)) subst =
    Forall(tyvars, apply_subst ty subst)
    
let apply_subst_in_env env subst =
    List.map(fun (id, schema) -> (id, apply_subst_in_scheme schema subst)) env

// type inference
//

let gamma0 =
    let make_numeric_sop op = [
        (op, TyArrow (TyInt, TyInt))
        (op, TyArrow (TyFloat, TyFloat))
    ]
    let make_boolean_sop op = [
        (op, TyArrow (TyBool, TyBool))
    ]
    let make_integral_op op = [
        (op, TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ]
    let make_numeric_op op =
        make_integral_op op
        @ [
        (op, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))   
        (op, TyArrow (TyInt, TyArrow (TyFloat, TyFloat)))
        (op, TyArrow (TyFloat, TyArrow (TyInt, TyFloat)))
    ]
    let make_comparison_op op = [
        (op, TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ]
    let make_bool_op op = [
        (op, TyArrow (TyBool, TyArrow(TyBool, TyBool)))
    ]
    let numeric_sops = List.collect make_numeric_sop ["-"]
    let boolean_sops = List.collect make_boolean_sop ["not"]
    let numerical_ops = List.collect make_numeric_op ["+" ; "-"; "/"; "%"; "*"]
    let comparison_ops = List.collect make_comparison_op ["<"; "<="; ">"; ">="; "=" ; "<>"]
    let boolean_ops = List.collect make_bool_op ["and"; "or"]
    numeric_sops @ boolean_sops @ numerical_ops @ comparison_ops @ boolean_ops
    
let s_gamma0 = List.map (fun (x, y) -> (x, Forall([], y))) gamma0

let mutable private fresh_variable_store = 0
let fresh_var () =
    let v = fresh_variable_store
    fresh_variable_store <- fresh_variable_store + 1
    TyVar v
    
// Instantiate a schema
let instantiate (Forall(tyvars, ty)) =
    let free = freevars_ty ty
    let toRefresh = Set.intersect free (Set tyvars)
    let sub = List.map (fun v -> (v, fresh_var  ())) <| Set.toList toRefresh
    apply_subst ty sub

// Generalize a type
let generalize env ty =
    let diff = Set.difference (freevars_ty ty)
                              (List.fold Set.union Set.empty <| List.map (freevars_scheme << snd) env)
    Forall (Set.toList diff, ty)

let extend_env (name, ty) env=
    (name, Forall ([], ty)) :: env

// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    // Literals
    | Lit (LInt _) -> TyInt, []
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit (LBool _) -> TyBool, []
    | Lit LUnit -> TyUnit, []
    
    | Var x ->
        match List.tryFind ((=) x << fst) env with
        | Some (_, ty) -> instantiate ty, []
        | None         -> type_error "Reference to undefined variable '%s'" x
    
    | Lambda(arg_name, annotation, body) ->
        // Argument inference or use annotation
        let arg_ty = match annotation with
                     | Some annotation -> annotation
                     | None -> fresh_var ()
        let env = extend_env (arg_name, arg_ty) env
        
        //  Body inference
        let body_ty, body_subs = typeinfer_expr env body
        let arg_ty = apply_subst arg_ty body_subs
        
        // Apply the new infos
        let arg_ty = apply_subst arg_ty body_subs
        
        TyArrow (arg_ty, body_ty), body_subs
        
    | App(lhs, rhs) ->
        // Infer lhs
        let lhs_ty, lhs_subst = typeinfer_expr env lhs
        let env = apply_subst_in_env env lhs_subst
        
        // Infer rhs
        let rhs_ty, rhs_subst = typeinfer_expr env rhs
        
        // Updates
        let lhs_ty = apply_subst lhs_ty rhs_subst
        
        // Construct the arrow
        let ret_ty = fresh_var ()
        let app_ty = TyArrow (rhs_ty, ret_ty)
        // Expect that the lhs_ty is such arrow
        let arrow_subst = unify lhs_ty app_ty
        
        // Collect all the information
        let subst = compose_subst arrow_subst <| compose_subst rhs_subst lhs_subst
        apply_subst ret_ty subst, subst
    
    // FIXME: Should we generalize? fun x -> x + x;;
    | BinOp(lhs, operator, rhs) ->
        let get_op = function
            | name, ty when name = operator -> Some ty
            | _ -> None
            
        let binary = function
            |TyArrow(_, TyArrow(_, TyArrow _)) -> false
            | TyArrow(_, TyArrow _) -> true
            | _ -> false
        
        // Get all the overloads of the operator
        let definitions = List.filter binary <| List.choose get_op gamma0
        if definitions.Length = 0 then
            type_error "Unknown binary operator '%s'" operator
        
        // infer the lhs
        let lhs_ty, lhs_subst = typeinfer_expr env lhs
        let env = apply_subst_in_env env lhs_subst
        
        // infer the rhs
        let rhs_ty, rhs_subst = typeinfer_expr env rhs
        // Update
        let lhs_ty = apply_subst lhs_ty rhs_subst
        
        // Construct the arrow
        let ret_ty = fresh_var ()
        let op_ty = TyArrow (lhs_ty, TyArrow(rhs_ty, ret_ty))
        let try_unify acc ty =
            match acc with
            | Some acc -> Some acc
            | None     ->
                try
                    let subst = unify op_ty ty
                    let subst = compose_subst subst <| compose_subst rhs_subst lhs_subst
                    Some (apply_subst ret_ty subst, subst)
                with
                    | TypeError _ -> None
                
        match List.fold try_unify None definitions with
            | Some res -> res
            | None     -> type_error "Cannot find a possible instantiation for operator '%s' with arguments %s %s %s"
                                        operator (pretty_ty lhs_ty) operator (pretty_ty rhs_ty)
    
    | UnOp(operator, arg) ->
        let get_op = function
            | name, ty when name = operator -> Some ty
            | _                             -> None
        
        let unary = function
            | TyArrow(_, TyArrow _) -> false
            | TyArrow _ -> true
            | _ -> false
        
        // Get all the overloads of the operator
        let definitions = List.filter unary <| List.choose get_op gamma0
        if definitions.Length = 0 then
            type_error "Unknown unary operator '%s'" operator
            
        // Infer the argument
        let arg_ty, arg_subst = typeinfer_expr env arg
        
        // Construct the arrow
        let ret_ty = fresh_var ()
        let op_ty = TyArrow (arg_ty, ret_ty)
        let try_unify acc ty =
            match acc with
            | Some acc -> Some acc
            | None     ->
                try
                    let subst = unify op_ty ty
                    let subst = compose_subst subst arg_subst
                    Some (apply_subst ret_ty subst, subst)
                with
                    | TypeError _ -> None
                
        match List.fold try_unify None definitions with
            | Some res -> res
            | None     -> type_error "Cannot find a possible instantiation for operator '%s' with arguments %s %s"
                                        operator operator (pretty_ty arg_ty)
    
    | IfThenElse(guard, thenBranch, elseBranch) ->
        // Infer the type of the guard and expect that is a Boolean
        let guard_ty, guard_subst = typeinfer_expr env guard
        let guard_subst = compose_subst (unify guard_ty TyBool) guard_subst
        let env = apply_subst_in_env env guard_subst
        
        // Infer the type of the then branch
        let then_ty, then_subst = typeinfer_expr env thenBranch
        let subst = compose_subst then_subst guard_subst
        let env = apply_subst_in_env env subst
        
        // Do we have an else branch
        match elseBranch with
            | Some elseBranch ->
                // Infer the type pf the else branch
                let else_ty, else_subs = typeinfer_expr env elseBranch
                // Apply new infos
                let then_ty = apply_subst then_ty else_subs
                let same_subst = unify then_ty else_ty
                let subst = compose_subst same_subst <| compose_subst else_subs subst
                apply_subst then_ty subst, subst
            | None ->
                // No, we must have Unit as the then type
                let guard_subst = unify guard_ty TyUnit
                TyUnit, compose_subst guard_subst subst
    
    | Let(name, annotation, it, body) ->
        // Infer the type of the it expression
        let it_type, it_subst = typeinfer_expr env it
        let env = apply_subst_in_env env it_subst
        // Do we have an annotation?
        let it_type, it_subst =
            match annotation with
            // If not we generalize
            | None -> generalize env it_type, it_subst
            // Else we unify with the annotation
            | Some annotation ->
                let it_type_un = unify annotation it_type
                let it_type = apply_subst it_type it_type_un
                Forall ([], it_type), compose_subst it_type_un it_subst
        let env = (name, it_type) :: env
        
        // Infer the body
        let body_ty, body_scheme = typeinfer_expr env body
        body_ty, compose_subst body_scheme it_subst               
    
    | LetRec(name, annotation, it, body) ->
        let function_ty = fresh_var ()
                          
        // Create the environment where it is type inferred
        let it_env = extend_env (name, function_ty) env
        let it_ty, it_subst = typeinfer_expr it_env it
        
        // Check that it_ty is compatible with it (infinite type check)
        let function_ty = apply_subst function_ty it_subst
        let function_subst = unify function_ty it_ty
        
        // Check that it is used as a function (we must infer that it is a 'a -> 'b) otherwise is used as a value
        match it_ty with
        | TyArrow _ -> ()
        | _ -> type_error "The right hand side of the recursive inferred that '%s' is used to define a value"
                    name
        
        // Use the fact that function_ty and it_ty must be the same
        let it_ty = apply_subst it_ty function_subst 
        let it_subst = compose_subst function_subst it_subst
        
        // Check the annotation if present
        let it_ty, it_subst =
            match annotation with
            | Some (TyArrow _ as annotation) ->
                let annotation_subst = unify it_ty annotation
                let it_ty = apply_subst it_ty annotation_subst
                it_ty, compose_subst annotation_subst it_subst
            | Some _ -> type_error "Recursive definitions can only be used to define functions"
            | None -> it_ty, it_subst
        
        // Infer the type of the body
        let body_env = apply_subst_in_env env it_subst
        let body_env = (name, generalize body_env it_ty) :: body_env
        let body_ty, body_subst = typeinfer_expr body_env body
        
        body_ty, compose_subst body_subst it_subst
        
    
    | Tuple args ->
        let accumulate (env, subst, ty) it =
            let env = apply_subst_in_env env subst
            let it_ty, it_subst = typeinfer_expr env it
            
            // Use the new info
            let ty = List.map (fun t -> apply_subst t it_subst) ty
            let subst = compose_subst it_subst subst
            
            env, subst, ty @ [ it_ty ]
            
        let _, subst, ty = List.fold accumulate (env, [], []) args
        TyTuple ty, subst

    // (??) I guess that reactive patterns are not that smart 
    | _ -> unexpected_error "typeinfer_expr: Should be unreachable %A" e


//// type checker
////
//    
//let rec typecheck_expr (env : ty env) (e : expr) : ty =
//    match e with
//    | Lit (LInt _) -> TyInt
//    | Lit (LFloat _) -> TyFloat
//    | Lit (LString _) -> TyString
//    | Lit (LChar _) -> TyChar
//    | Lit (LBool _) -> TyBool
//    | Lit LUnit -> TyUnit
//
//    | Var x ->
//        let _, t = List.find (fun (y, _) -> x = y) env
//        t
//
//    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
//    
//    | Lambda (x, Some t1, e) ->
//        let t2 = typecheck_expr ((x, t1) :: env) e
//        TyArrow (t1, t2)
//
//    | App (e1, e2) ->
//        let t1 = typecheck_expr env e1
//        let t2 = typecheck_expr env e2
//        match t1 with
//        | TyArrow (l, r) ->
//            if l = t2 then r 
//            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
//        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)
//
//    | Let (x, tyo, e1, e2) ->
//        let t1 = typecheck_expr env e1
//        match tyo with
//        | None -> ()
//        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
//        typecheck_expr ((x, t1) :: env) e2
//
//    | IfThenElse (e1, e2, e3o) ->
//        let t1 = typecheck_expr env e1
//        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
//        let t2 = typecheck_expr env e2
//        match e3o with
//        | None ->
//            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
//            TyUnit
//        | Some e3 ->
//            let t3 = typecheck_expr env e3
//            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
//            t2
//
//    | Tuple es ->
//        TyTuple (List.map (typecheck_expr env) es)
//
//    | LetRec (f, None, e1, e2) ->
//        unexpected_error "typecheck_expr: unannotated let rec is not supported"
//        
//    | LetRec (f, Some tf, e1, e2) ->
//        let env0 = (f, tf) :: env
//        let t1 = typecheck_expr env0 e1
//        match t1 with
//        | TyArrow _ -> ()
//        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
//        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
//        typecheck_expr env0 e2
//
//    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
//        let t1 = typecheck_expr env e1
//        let t2 = typecheck_expr env e2
//        match t1, t2 with
//        | TyInt, TyInt -> TyInt
//        | TyFloat, TyFloat -> TyFloat
//        | TyInt, TyFloat
//        | TyFloat, TyInt -> TyFloat
//        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
//        
//    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
//        let t1 = typecheck_expr env e1
//        let t2 = typecheck_expr env e2
//        match t1, t2 with
//        | TyInt, TyInt -> ()
//        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
//        TyBool
//
//    | BinOp (e1, ("and" | "or" as op), e2) ->
//        let t1 = typecheck_expr env e1
//        let t2 = typecheck_expr env e2
//        match t1, t2 with
//        | TyBool, TyBool -> ()
//        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
//        TyBool
//
//    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op
//
//    | UnOp ("not", e) ->
//        let t = typecheck_expr env e
//        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
//        TyBool
//            
//    | UnOp ("-", e) ->
//        let t = typecheck_expr env e
//        match t with
//        | TyInt -> TyInt
//        | TyFloat -> TyFloat
//        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)
//
//    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op
//
//    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
