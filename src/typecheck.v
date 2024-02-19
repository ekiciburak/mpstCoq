From MPSTCoq Require Import src.expressions src.processes src.global src.local src.projection.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.

Inductive ctx: Type :=
  | empty: ctx
  | consS: string -> gsort -> ctx -> ctx
  | consT: fin    -> local -> ctx -> ctx.

Definition extendS (m: ctx) (s: string) (t: gsort) :=
  consS s t m.

Definition extendT (m: ctx) (s: fin) (t: local) :=
  consT s t m.

Fixpoint lookupS (m: ctx) (s: string): option gsort :=
  match m with
    | empty          => None
    | consS s' t' xs => if eqb s s' then Some t' else lookupS xs s
    | consT s' t' xs => lookupS xs s
  end.

Fixpoint lookupT (m: ctx) (s: fin): option local :=
  match m with
    | empty          => None
    | consT s' t' xs => if Nat.eqb s s' then Some t' else lookupT xs s
    | consS s' t' xs => lookupT xs s
  end.

Fixpoint typ_expr (m: ctx) (e: expr): option gsort :=
  match e with
    | e_var x   => lookupS m x
    | e_val v   => 
      match v with
        | tint i  => Some gint
        | tbool b => Some gbool
      end
    | e_succ e1 => 
      let se1 := typ_expr m e1 in
      match se1 with
        | Some gint => Some gint
        | _         => None
      end
    | e_neg e1 => 
      let se1 := typ_expr m e1 in
      match se1 with
        | Some gint => Some gint
        | _         => None
      end
    | e_not e1 => 
      let se1 := typ_expr m e1 in
      match se1 with
        | Some goobl => Some gbool
        | _          => None
      end
    | e_gt e1 e2 => 
      let se1 := typ_expr m e1 in
      let se2 := typ_expr m e2 in
      match pair se1 se2 with
        | pair (Some gint) (Some gint) => Some gint
        | _                            => None
      end
  end.

Fixpoint typ_proc (m: ctx) (p: process): option local :=
  match p with
    | p_inact         => Some l_end
    | p_var x         => lookupT m x
    | p_send p l e P  => 
      let ste := typ_expr m e in
      let stP := typ_proc m P in
      match pair ste stP with
        | pair (Some te) (Some tP) => Some (l_send p (cons (pair (pair l te) tP) nil))
        | _                        => None
      end
    | p_recv p l      =>
      let fix next l :=
        match l with
          | pair (pair lbl (e_var x)) P :: xs =>
            let ste := lookupS m x in
            match ste with
              | Some te => 
                let stP := typ_proc (extendS m x te) P in
                match stP with
                  | Some tP => pair (pair lbl te) tP :: next xs
                  | None    => nil
                end
              | None => nil 
            end
          | _   => nil
        end
      in Some (l_recv p (next l))
    | p_ite e P1 P2   =>
      let ste  := typ_expr m e in
      let stP1 := typ_proc m P1 in
      let stP2 := typ_proc m P2 in
      match pair (pair ste stP1) stP2 with
        | pair (pair (Some gbool) (Some tP1)) (Some tP2) =>
          if local_eq tP1 tP2 then Some tP1 else None 
        | _                                                => None
      end
    | p_rec P         => 
      let stb := lookupT m 0 in
      match stb with
        | Some tb => 
          let stP := typ_proc (extendT m 0 tb) P in
          match stP with
            | Some tP => Some tP
            | None    => None
          end
        | None    => None 
      end
  end.

Fixpoint step_global_peq (l: list (prod (prod label gsort) global)) (lbl: label): option global :=
  match l with
    | nil                          => None
    | pair (pair lbl1 s1) g1 :: xs => if eqb lbl1 lbl then Some g1 else step_global_peq xs lbl
  end.

Fixpoint gt_step (g: global) (p q: part) (lbl: glabel): option global :=
  match g with
    | g_send a b l =>
      if andb (eqb p a) (eqb q b) then step_global_peq l lbl
      else if andb (andb (andb (negb (eqb a p)) (negb (eqb b q))) (negb (eqb a q))) (negb (eqb b p))
      then
        let fix next l :=
          match l with
            | pair (pair lbl1 s) g1 :: xs =>
              let ssg1 := gt_step g1 p q lbl in
              match ssg1 with
                | Some sg1 => pair (pair lbl1 s) sg1 :: next xs
                | None     => next xs
              end
            | nil                         => nil
          end
        in Some (g_send a b (next l))
      else None
(*     | g_rec g1 => gt_step (subst_global ((g_rec g1) .: g_var) g1) p q lbl *)
    | _        => None
  end.

Print Forall.

From mathcomp Require Import all_ssreflect. 

Inductive gt_stepI: part -> part -> glabel -> global -> global -> Prop := 
  | gt_sendE_m : forall a b p q lbl1 lbl2 s x xs,
                 lbl1 = lbl2 ->
                 a = p ->
                 b = q ->
                 gt_stepI p q lbl2 (g_send a b ((pair (pair lbl1 s) x) :: xs)) x
  | gt_sendE_nm: forall a b p q lbl1 (xs: seq (glabel * gsort * global)) (ys: seq (glabel * gsort * global)),
                 a <> p ->
                 b <> q ->
                 a <> q ->
                 b <> p ->
                 (List.In lbl1 (map fst (map fst xs)) -> False) ->
                 Forall (fun u => gt_stepI p q lbl1 u.1 u.2) (zip (map snd xs) (map snd ys)) ->
                 gt_stepI p q lbl1 (g_send a b xs) (g_send a b ys)
  | gt_mu      : forall p q lbl g,
                 gt_stepI p q lbl (g_rec g) (subst_global ((g_rec g) .: g_var) g).

Lemma _46: forall G p q lbl,
           exists l,
           projection G p = Some (l_send q (project_list l p)) ->
           gt_step G p q lbl = step_global_peq l lbl.
Proof. intros. 
       specialize(_46inv G p q); intro H.
       destruct H as (l, H).
       exists l.
       intro Ha.
       specialize(H Ha).
       destruct H.
       subst. simpl.
       rewrite !eqb_refl. simpl.
       easy.
       admit.
Admitted.





