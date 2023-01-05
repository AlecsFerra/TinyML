(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

// """"""Pattern Synonyms""""""" for literal values
let (|VInt|_|) = function
    | VLit (LInt i) -> Some i
    | _ -> None
let VInt x = VLit (LInt x)

let (|VFloat|_|) = function
    | VLit (LFloat i) -> Some i
    | _ -> None
let VFloat x = VLit (LFloat x)

let (|VBool|_|) = function
    | VLit (LBool i) -> Some i
    | _ -> None
let VBool x = VLit (LBool x)

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v

    | Lambda (x, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        

    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )

    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    // TODO: test this is ok or fix it
    | LetRec (f, _, e1, e2) ->
        let v1 = eval_expr env e1
        match v1 with
        // DONE:
        // | Closure (venv1, x, e) -> RecClosure (venv1, f, x, e)
        | Closure (venv1, x, e) ->
            let rec_closure = RecClosure (venv1, f, x, e)
            eval_expr ((f, rec_closure) :: env) e2
        | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        // TODO finish this implementation

    // TODO: implement other binary ops
    // DONE:
    | BinOp (lhs, operator, rhs) ->
        let lvalue = eval_expr env lhs
        let rvalue = eval_expr env rhs
        let op =
            match operator with
            // Numerical combination between Int and Float
            | "+" -> combine "+" [ integral_operator (+); float_operator (+) ]
            | "-" -> combine "-" [ integral_operator (-); float_operator (-) ]
            | "*" -> combine "*" [ integral_operator (*); float_operator (*) ]
            | "%" -> combine "%" [ integral_operator (%); float_operator (%) ]
            | "/" -> combine "/" [ integral_operator (/); float_operator (/) ]
            // Comparison Int
            | "<" -> combine "<" [ integral_comparison (<) ]
            | "<=" -> combine "<=" [ integral_comparison (<=) ]
            | ">" -> combine ">" [ integral_comparison (>) ]
            | ">=" -> combine ">=" [ integral_comparison (>=) ]
            | "=" -> combine "=" [ integral_comparison (=) ]
            | "<>" -> combine "<>" [ integral_comparison (<>) ]
            // Logical Bool
            | "and" -> combine "and" [ boolean_operator (&&) ]
            | "or" -> combine "or" [ boolean_operator (||) ]
            // ._.
            | any -> unexpected_error "eval_expr: unsupported operator: %s" any
        op lvalue rvalue

    // Forgot unary operators and tuples???
    | UnOp(operator, expr) ->
        let e = eval_expr env expr
        let op = match operator with
                 | "not" ->
                    function
                    | VBool b -> VBool (not b)
                    | _ -> unexpected_error "eval_expr: illegal operands in operator (%s): %s %s"
                                                operator operator (pretty_value e)
                 | "-"  ->
                   function
                   | VInt i -> VInt (- i)
                   | VFloat f -> VFloat (- f)
                   | _ -> unexpected_error "eval_expr: illegal operands in operator (%s): %s %s"
                                                operator operator (pretty_value e)
                 | any -> unexpected_error "eval_expr: unsupported operator: %s" any
        op e
    | Tuple exprs -> VTuple <| List.map (eval_expr env) exprs
    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and try_apply arg fs =
    let combine x f = Option.orElseWith (fun () -> f arg) x
    List.fold combine None fs
    
and combine name ops l r =
    match try_apply (l, r) ops with
    | Some x -> x
    | None -> unexpected_error "eval_expr: illegal operands in binary operator (%s): %s %s %s"
                name (pretty_value l) name (pretty_value r)

and integral_operator op = function
    | VInt l, VInt r -> Some (VInt (op l r))
    | _ -> None

and integral_comparison op = function
    | VInt l, VInt r -> Some (VBool (op l r))
    | _ -> None
    
and float_operator op = function
    | VFloat l, VFloat r -> Some (VFloat (op l r))
    | VFloat l, VInt r -> Some (VFloat (op l (float r)))
    | VInt l, VFloat r -> Some (VFloat (op (float l) r))
    | _ -> None
    
and boolean_operator op = function
    | VBool l, VBool r -> Some (VBool (op l r))
    | _ -> None