Require Import List String ZArith.

Variant value: Type :=
  | tint : Z      -> value
  | tbool: bool   -> value.

Inductive expr: Type :=
  | e_var  : string -> expr
  | e_val  : value  -> expr
  | e_succ : expr   -> expr
  | e_neg  : expr   -> expr
  | e_not  : expr   -> expr
(*   | e_oplus: expr   -> expr -> expr *)
  | e_gt   : expr   -> expr -> expr.

Fixpoint eval_expr (e: expr): expr :=
  match e with
    | e_var s   => e_var s
    | e_val v   => e_val v
    | e_succ e1 =>
      let ee1 := eval_expr e1 in
      match ee1 with
        | e_val (tint n) => e_val (tint (n+1))
        | _              => e_succ ee1
      end
   | e_neg e1 =>
     let ee1 := eval_expr e1 in
     match e1 with
       | e_val (tint n) => e_val (tint (-n))
       | _              => e_neg ee1
     end
   | e_not e1   =>
     let ee1 := eval_expr e1 in
     match ee1 with
       | e_val (tbool b) => e_val (tbool (negb b))
       | _               => e_not ee1
     end
   | e_gt e1 e2 =>
     let ee1 := eval_expr e1 in
     let ee2 := eval_expr e2 in
     match (e1, e2) with
       | (e_val (tint n), e_val (tint m)) => e_val (tbool (Z.gtb n m)) 
       | _                                => e_gt ee1 ee2
     end
  end.

Fixpoint subst_expr (e: expr) (x: string) (s: expr): expr :=
  match e with
    | e_var y    => if eqb x y then s else e
    | e_succ e1  => e_succ (subst_expr e1 x s)
    | e_neg e1   => e_neg (subst_expr e1 x s)
    | e_not e1   => e_not (subst_expr e1 x s)
    | e_gt e1 e2 => e_gt (subst_expr e1 x s) (subst_expr e2 x s)
(*  | e_oplus e1 e2 => e_oplus (subst_expr e1 x s) (subst_expr e2 x s) *)
    | _          => e
  end.
