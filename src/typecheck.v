From MPSTCoq Require Import src.unscoped src.expressions src.processes src.global src.local src.projection.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.

Inductive ctx: Type :=
  | empty: ctx
  | consS: fin -> expressions.sort -> ctx -> ctx
  | consT: fin -> local -> ctx -> ctx.

Definition extendS (m: ctx) (s: fin) (t: expressions.sort) :=
  consS s t m.

Definition extendT (m: ctx) (s: fin) (t: local) :=
  consT s t m.

Fixpoint lookupS (m: ctx) (s: fin): option expressions.sort :=
  match m with
    | empty          => None
    | consS s' t' xs => if Nat.eqb s s' then Some t' else lookupS xs s
    | consT s' t' xs => lookupS xs s
  end.

Fixpoint lookupT (m: ctx) (s: fin): option local :=
  match m with
    | empty          => None
    | consT s' t' xs => if Nat.eqb s s' then Some t' else lookupT xs s
    | consS s' t' xs => lookupT xs s
  end.

Fixpoint infr_expr (m: ctx) (e: expr): option expressions.sort :=
  match e with
    | e_var x   => lookupS m x
    | e_val v   => 
      match v with
        | vint i  => Some sint
        | vbool b => Some sbool
      end
    | e_succ e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some gint => Some gint
        | _         => None
      end
    | e_neg e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some gint => Some gint
        | _         => None
      end
    | e_not e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some goobl => Some sbool
        | _          => None
      end
    | e_gt e1 e2 => 
      let se1 := infr_expr m e1 in
      let se2 := infr_expr m e2 in
      match pair se1 se2 with
        | pair (Some sint) (Some sint) => Some sbool
        | _                            => None
      end
    | e_plus e1 e2 => 
      let se1 := infr_expr m e1 in
      let se2 := infr_expr m e2 in
      match pair se1 se2 with
        | pair (Some sint) (Some sint) => Some sint
        | _                            => None
      end
  end.

Inductive typ_expr: ctx -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = lookupS c s ->
                              typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e sint ->
                         typ_expr c (e_succ e) sint
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint.

Fixpoint matchSel (l: label) (xs: list(label*(expressions.sort)*local)%type): option ((expressions.sort)*local)%type :=
  match xs with
    | nil           => None
    | (lbl,s,t)::ys => if eqb l lbl then Some(s,t) else matchSel l ys
  end.

Inductive typ_proc: fin -> fin -> ctx -> process -> local -> Prop :=
  | tc_inact: forall m em c, typ_proc m em c (p_inact) (l_end)
  | tc_var  : forall m em c s t, Some t = lookupT c s ->
                                 typ_proc m em c (p_var s) t
  | tc_mu   : forall m em c p t, let c' := extendT c m t in
                                 typ_proc (S m) em c' p t ->
                                 typ_proc m em c (p_rec t p) t
  | tc_recv : forall m em c p L ST P T,
                     List.Forall (fun u => typ_proc m (S em) (extendS c em (fst u)) (fst (snd u)) (snd (snd u))) (zip ST (zip P T)) ->
                     typ_proc m em c (p_recv p (zip (zip L ST) P)) (l_recv p (zip (zip L ST) T))
  | tc_send: forall m em c p l e P xs S T, Some(S,T) = matchSel l xs ->
                                           typ_expr c e S ->
                                           typ_proc m em c P T ->
                                           typ_proc m em c (p_send p l e P) (l_send p xs).

Fixpoint infr_proc (m: ctx) (p: process) (u: fin) (n: fin): option local :=
  match p with
    | p_inact         => Some l_end
    | p_var x         => lookupT m x
    | p_send p l e P  => 
      let ste := infr_expr m e in
      let stP := infr_proc m P u n in
      match pair ste stP with
        | pair (Some te) (Some tP) => Some (l_send p (cons (pair (pair l te) tP) nil))
        | _                        => None
      end
    | p_recv p l      =>
      let fix next l :=
        match l with
          | pair (pair lbl te) P :: xs =>
            let stP := infr_proc (extendS m n te) P u (S n) in
            match stP with
              | Some tP => pair (pair lbl te) tP :: next xs
              | None    => nil
            end
          | _   => nil
        end
      in (let k := (next l) in 
              if isNil k then None else Some (l_recv p k))
    | p_ite e P1 P2   =>
      let ste  := infr_expr m e in
      let stP1 := infr_proc m P1 u n in
      let stP2 := infr_proc m P2 u n in
      match pair (pair ste stP1) stP2 with
        | pair (pair (Some gbool) (Some tP1)) (Some tP2) =>
          if local_eq tP1 tP2 then Some tP1 else None 
        | _                                                => None
      end
    | p_rec tb P         => 
      let stP := infr_proc (extendT m u tb) P (S u) n in
      match stP with
        | Some tP => Some tP
        | None    => None
      end
  end.

(*
Definition st := p_recv "q" [("l1", sint, 
                             (p_recv "q" [("l2", sbool, 
                                          (p_send "p" "l3" (e_plus (e_var 0) (e_val (vint 10))) 
                                          (p_recv "q" [("l2", sbool, 
                                          (p_send "p" "l3" (e_plus (e_var 2) (e_val (vint 10))) p_inact))])))]))].
Eval compute in (infr_proc empty st 0 0).
*)

Fixpoint step_global_peq (l: list (prod (prod label sort) global)) (lbl: label): option global :=
  match l with
    | nil                          => None
    | pair (pair lbl1 s1) g1 :: xs => if eqb lbl1 lbl then Some g1 else step_global_peq xs lbl
  end.

Fixpoint gt_step (g: global) (p q: part) (lbl: label): option global :=
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
    | g_rec g1 => Some (subst_global ((g_rec g1) .: g_var) g1)
    | _        => None
  end.

(* Inductive gt_stepI: part -> part -> label -> global -> global -> Prop := 
  | gt_sendE_m : forall a b p q lbl1 lbl2 s x xs,
                 lbl1 = lbl2 ->
                 a = p ->
                 b = q ->
                 gt_stepI p q lbl2 (g_send a b ((pair (pair lbl1 s) x) :: xs)) x
  | gt_sendE_nm: forall a b p q lbl1 (xs: seq (label * sort * global)) (ys: seq (label * sort * global)),
                 a <> p ->
                 b <> q ->
                 a <> q ->
                 b <> p ->
                 (List.In lbl1 (map fst (map fst xs)) -> False) ->
                 Forall (fun u => gt_stepI p q lbl1 u.1 u.2) (zip (map snd xs) (map snd ys)) ->
                 gt_stepI p q lbl1 (g_send a b xs) (g_send a b ys)
  | gt_mu      : forall p q lbl g,
                 gt_stepI p q lbl (g_rec g) (subst_global ((g_rec g) .: g_var) g). *)


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
       induction G; intros.
       + simpl in *. easy.
       + simpl in *. easy.
       + simpl in *. admit.
       + simpl in *. admit.
Admitted.





