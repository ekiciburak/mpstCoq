From MPSTCoq Require Export src.unscoped src.expressions src.processes src.sessions.
Require Import List String Relations.

Fixpoint find_proc (l: label) (lst: list (label*expr*process)): option (expr*process) :=
  match lst with
    | nil                     => Datatypes.None
    | pair (pair u e) p :: xs => if eqb l u then Datatypes.Some (pair e p) else find_proc l xs 
  end.

Definition beta (s: session): session :=
  match s with
    | s_cons (s_cons (s_par p1 (p_recv q1 l)) (s_par q2 (p_send p2 lbl e Q))) M =>
      if andb (andb (eqb p1 p2) (eqb q1 q2)) (negb (eqb p1 q1))
      then
        let v  := eval_expr e in
        let rp := find_proc lbl l in
        match rp with
          | Datatypes.None             => s
          | Datatypes.Some (pair ej pj) => 
            match ej with
               | e_var x => s_cons (s_cons (s_par p1 (subst_expr_proc pj x v)) (s_par q1 Q)) M
               | _       => s
            end
        end
      else s
    | _  => s
  end.

Inductive betaI: relation session :=
  | r_comm: forall p l q lbl e Q M x v rp ej pj,
            v  = eval_expr e ->
            rp = find_proc lbl l ->
            let rp := Datatypes.Some (pair ej pj) in
            ej = e_var x ->
            betaI (s_cons (s_cons (s_par p (p_recv q l)) (s_par q (p_send p lbl e Q))) M)
                  (s_cons (s_cons (s_par p (subst_expr_proc pj x v)) (s_par q Q)) M)
  | t_cond: forall p e P Q M, 
            eval_expr e = e_val (tbool true) ->
            betaI (s_cons (s_par p (p_ite e P Q)) M)
                  (s_cons (s_par p P) M)
  | f_cond: forall p e P Q M, 
            eval_expr e = e_val (tbool false) ->
            betaI (s_cons (s_par p (p_ite e P Q)) M)
                  (s_cons (s_par p Q) M)
  | r_struct: forall M1 M2 M1' M2',
                     s_cong M1' M1 ->
                     betaI M1 M2 ->
                     s_cong M2 M2' ->
                     betaI M1' M2'.
