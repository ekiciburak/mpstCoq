From MPSTCoq Require Export src.unscoped src.expressions src.processes src.sessions.
Require Import List String Relations ZArith.
Require Import Setoid Morphisms Coq.Program.Basics.
Import ListNotations.

Inductive betaP: relation session :=
  | r_comm  : forall p q xs l e Q M,
              let v := eval_expr e in
              betaP ((p <-- p_recv q xs) ||| (q <-- p_send p l e Q) ||| M)
                    ((p <-- subst_expr_proc (p_recv q xs) l v) ||| (q <-- Q) ||| M)
  | rt_ite  : forall p P Q M,
              betaP ((p <-- p_ite (e_val (vbool true)) P Q) ||| M) ((p <-- P) ||| M)
  | rf_ite  : forall p P Q M,
              betaP ((p <-- p_ite (e_val (vbool false)) P Q) ||| M) ((p <-- Q) ||| M)
  | r_struct: forall M1 M1' M2 M2', scong M1 M1' -> scong M2' M2 -> betaP M1' M2' -> betaP M1 M2.

Declare Instance Equivalence_beta : Equivalence betaP.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Definition beta_multistep := multi betaP.

#[global] Declare Instance RW_scong3: Proper (scong ==> scong ==> impl) betaP.
#[global] Declare Instance RW_scong4: Proper (scong ==> scong ==> impl) beta_multistep.

Definition PAlice: process := 
  p_send "Bob" "l1" (e_val (vint 50)) (p_recv "Carol" [("l3",sint,p_inact)]).

Definition PBob: process :=
  p_recv "Alice" [("l1",sint,p_send "Carol" "l2" (e_val (vint 100)) p_inact);
                  ("l4",sint,p_send "Carol" "l2" (e_val (vint 2)) p_inact)
                 ].

Definition PCarol: process :=
  p_recv "Bob" [("l2", sint, p_send "Alice" "l3" (e_plus (e_var 0) (e_val (vint 1))) p_inact)].

Definition MS: session := ("Alice" <-- PAlice) ||| ("Bob" <-- PBob) ||| ("Carol" <-- PCarol).

Definition MS': session := ("Alice" <-- p_inact) ||| ("Bob" <-- p_inact) ||| ("Carol" <-- p_inact).

(* Eval compute in (eval_expr (e_plus (e_val (vint 100)) (e_val (vint 5)))). *)

Example redMS: beta_multistep MS MS'.
Proof. unfold beta_multistep, MS, MS', PAlice, PBob.

       setoid_rewrite sc_par3.
       setoid_rewrite sc_par2.
       setoid_rewrite sc_par4.
       setoid_rewrite <- sc_par3.

       apply multi_step with
       (y := ((("Bob" <-- p_send "Carol" "l2" (e_val (vint 100)) p_inact) |||
              ("Alice" <-- (p_recv "Carol" [("l3", sint, p_inact)]))) ||| ("Carol" <-- PCarol))
       ).
       apply r_comm.
       unfold PCarol.

       setoid_rewrite sc_par2.
       setoid_rewrite <- sc_par3.
       apply multi_step with
       (y := ((("Carol" <-- p_send "Alice" "l3" (e_plus (e_val (vint 100)) (e_val (vint 1)))  p_inact) |||
              ("Bob" <-- p_inact)) ||| ("Alice" <-- p_recv "Carol" [("l3", sint, p_inact)]))
       ).
       apply r_comm.

       setoid_rewrite sc_par2.
       setoid_rewrite <- sc_par3.
       apply multi_step with
       (y := ((("Alice" <-- p_inact) |||
              ("Carol" <-- p_inact)) ||| ("Bob" <-- p_inact))
       ).
       apply r_comm.
       apply multi_refl.
Qed.

(*
Definition PAliceT: process := 
  p_rec (p_send "Bob" "l1" (e_val (vint 50%Z)) (p_recv "Carol" [("l3",sint,(p_var 0))])).

Definition MSA (M: session): session := ("Alice" <-- PAliceT ||| M).

Definition MSA' (M: session): session := ("Alice" <-- p_inact ||| M).

Example redMSA: forall M, beta_multistep (MSA M) (MSA' M).
Proof. unfold beta_multistep, MSA, MSA', PAliceT.
       intro M.
       rewrite sc_rec.
 *)



