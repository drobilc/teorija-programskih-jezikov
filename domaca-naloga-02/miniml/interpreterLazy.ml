module S = Syntax

let rec eval_exp = function
  | S.Var _ -> failwith "Expected a closed term"
  | (S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ | S.Cons _ | S.Pair _) as e -> e
  | S.Plus (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Int (n1 + n2)
  | S.Minus (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Int (n1 - n2)
  | S.Times (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Int (n1 * n2)
  | S.Equal (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Bool (n1 = n2)
  | S.Less (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Bool (n1 < n2)
  | S.Greater (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Bool (n1 > n2)
  | S.IfThenElse (e, e1, e2) -> (
      match eval_exp e with
      | S.Bool true -> eval_exp e1
      | S.Bool false -> eval_exp e2
      | _ -> failwith "Boolean expected")
  | S.Apply (e1, e2) -> (
      let f = eval_exp e1 in
      match f with
      | S.Lambda (x, e) -> eval_exp (S.subst_exp [ (x, e2) ] e)
      | S.RecLambda (f, x, e) as rec_f ->
          eval_exp (S.subst_exp [ (f, rec_f); (x, e2) ] e)
      | _ -> failwith "Function expected")
  | S.Nil -> S.Nil
  | S.Fst e -> (
      match eval_exp e with
      | S.Pair (fst, _) -> eval_exp fst
      | _ -> failwith "Pair expected")
  | S.Snd e -> (
      match eval_exp e with
      | S.Pair (_, snd) -> eval_exp snd
      | _ -> failwith "Pair expected")
  | S.Match (e, e1, x, xs, e2) -> (
      match eval_exp e with
        | S.Nil -> eval_exp e1
        | S.Cons (head, tail) -> eval_exp (S.subst_exp [ (x, head); (xs, tail) ] e2)
        | _ -> failwith "List expected")

and eval_int e =
  match eval_exp e with S.Int n -> n | _ -> failwith "Integer expected"

let is_value = function
  | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ -> true
  | S.Nil | S.Pair _ | S.Cons _ -> true
  | S.Var _ | S.Plus _ | S.Minus _ | S.Times _ | S.Equal _ | S.Less _
  | S.Greater _ | S.IfThenElse _ | S.Apply _
  | S.Match _ | S.Fst _ | S.Snd _ ->
      false

let rec step = function
  | S.Var _ | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ | S.Nil ->
      failwith "Expected a non-terminal expression"
  | S.Plus (S.Int n1, S.Int n2) -> S.Int (n1 + n2)
  | S.Plus (S.Int n1, e2) -> S.Plus (S.Int n1, step e2)
  | S.Plus (e1, e2) -> S.Plus (step e1, e2)
  | S.Minus (S.Int n1, S.Int n2) -> S.Int (n1 - n2)
  | S.Minus (S.Int n1, e2) -> S.Minus (S.Int n1, step e2)
  | S.Minus (e1, e2) -> S.Minus (step e1, e2)
  | S.Times (S.Int n1, S.Int n2) -> S.Int (n1 * n2)
  | S.Times (S.Int n1, e2) -> S.Times (S.Int n1, step e2)
  | S.Times (e1, e2) -> S.Times (step e1, e2)
  | S.Equal (S.Int n1, S.Int n2) -> S.Bool (n1 = n2)
  | S.Equal (S.Int n1, e2) -> S.Equal (S.Int n1, step e2)
  | S.Equal (e1, e2) -> S.Equal (step e1, e2)
  | S.Less (S.Int n1, S.Int n2) -> S.Bool (n1 < n2)
  | S.Less (S.Int n1, e2) -> S.Less (S.Int n1, step e2)
  | S.Less (e1, e2) -> S.Less (step e1, e2)
  | S.Greater (S.Int n1, S.Int n2) -> S.Bool (n1 > n2)
  | S.Greater (S.Int n1, e2) -> S.Greater (S.Int n1, step e2)
  | S.Greater (e1, e2) -> S.Greater (step e1, e2)
  | S.IfThenElse (S.Bool b, e1, e2) -> if b then e1 else e2
  | S.IfThenElse (e, e1, e2) -> S.IfThenElse (step e, e1, e2)
  | S.Apply (S.Lambda (x, e), v) -> S.subst_exp [ (x, v) ] e
  | S.Apply ((S.RecLambda (f, x, e) as rec_f), v) ->
      S.subst_exp [ (f, rec_f); (x, v) ] e
  | S.Apply (e1, e2) -> S.Apply (step e1, e2)
  | S.Fst (S.Pair (fst, _)) -> (step fst)
  | S.Snd (S.Pair (_, snd)) -> (step snd)
  | S.Match (S.Nil, e1, _, _, _) -> e1
  | S.Match (S.Cons (head, tail), _, x, xs, e2) -> S.subst_exp [ (x, head) ; (xs, tail) ] e2
  | S.Match (e, e1, x, xs, e2) -> S.Match (step e, e1, x, xs, e2)
  | _ as e -> failwith ("Error: " ^ (S.string_of_exp e))

let big_step e =
  let v = eval_exp e in
  print_endline (S.string_of_exp v)

let rec small_step e =
  print_endline (S.string_of_exp e);
  if not (is_value e) then (
    print_endline "  ~>";
    small_step (step e))
