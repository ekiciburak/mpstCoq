From MPSTCoq Require Export src.unscoped src.expressions src.global.

Require Import List String.
Open Scope list_scope.


Section local.
Inductive local  : Type :=
  | l_var : ( fin ) -> local 
  | l_end : local 
  | l_send : ( part   ) -> ( list (prod (prod (label  ) (sort  )) (local  )) ) -> local 
  | l_recv : ( part   ) -> ( list (prod (prod (label  ) (sort  )) (local  )) ) -> local 
  | l_rec : ( local   ) -> local .

Lemma congr_l_end  : l_end  = l_end  .
Proof. congruence. Qed.

Lemma congr_l_send  { s0 : part   } { s1 : list (prod (prod (label  ) (sort  )) (local  )) } { t0 : part   } { t1 : list (prod (prod (label  ) (sort  )) (local  )) } (H1 : s0 = t0) (H2 : s1 = t1) : l_send  s0 s1 = l_send  t0 t1 .
Proof. congruence. Qed.

Lemma congr_l_recv  { s0 : part   } { s1 : list (prod (prod (label  ) (sort  )) (local  )) } { t0 : part   } { t1 : list (prod (prod (label  ) (sort  )) (local  )) } (H1 : s0 = t0) (H2 : s1 = t1) : l_recv  s0 s1 = l_recv  t0 t1 .
Proof. congruence. Qed.

Lemma congr_l_rec  { s0 : local   } { t0 : local   } (H1 : s0 = t0) : l_rec  s0 = l_rec  t0 .
Proof. congruence. Qed.

Definition upRen_local_local   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_local   (xilocal : ( fin ) -> fin) (s : local ) : local  :=
    match s return local  with
    | l_var  s => (l_var ) (xilocal s)
    | l_end   => l_end 
    | l_send  s0 s1 => l_send  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_local xilocal))) s1)
    | l_recv  s0 s1 => l_recv  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_local xilocal))) s1)
    | l_rec  s0 => l_rec  ((ren_local (upRen_local_local xilocal)) s0)
    end.

Definition up_local_local   (sigma : ( fin ) -> local ) : ( fin ) -> local  :=
  (scons) ((l_var ) (var_zero)) ((funcomp) (ren_local (shift)) sigma).

Fixpoint subst_local   (sigmalocal : ( fin ) -> local ) (s : local ) : local  :=
    match s return local  with
    | l_var  s => sigmalocal s
    | l_end   => l_end 
    | l_send  s0 s1 => l_send  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_local sigmalocal))) s1)
    | l_recv  s0 s1 => l_recv  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_local sigmalocal))) s1)
    | l_rec  s0 => l_rec  ((subst_local (up_local_local sigmalocal)) s0)
    end.


Fixpoint local_eq (l1 l2: local): bool :=
  match pair l1 l2 with
    | pair (l_var n1) (l_var n2) => Nat.eqb n1 n2
    | pair (l_send p1 la) (l_send p2 lb) =>
      let fix next la lb :=
        match pair la lb with
          | pair ((pair (pair lbl1 s1) lc1) :: xs1) ((pair (pair lbl2 s2) lc2) :: xs2) =>
            if (andb (andb (eqb lbl1 lbl2) (sort_eq s1 s2)) (local_eq lc1 lc2)) then next xs1 xs2
            else false
          | pair nil nil => true
          | _            => false
        end
      in ((eqb p1 p2) && (next la lb))
    | pair (l_recv p1 la) (l_recv p2 lb) =>
      let fix next la lb :=
        match pair la lb with
          | pair ((pair (pair lbl1 s1) lc1) :: xs1) ((pair (pair lbl2 s2) lc2) :: xs2) =>
            if (andb (andb (eqb lbl1 lbl2) (sort_eq s1 s2)) (local_eq lc1 lc2)) then next xs1 xs2
            else false
          | pair nil nil => true
          | _            => false
        end
      in (andb (eqb p1 p2) (next la lb))
    | pair (l_rec la) (l_rec lb) => local_eq la lb
    | _                          => false
  end.

Fixpoint unfold_lrec (s: local): local :=
  match s with
    | l_rec t      => subst_local ((l_rec t) .: l_var) t
    | l_send p l =>
      let fix next l :=
        match l with
          | nil                          => nil
          | pair (pair lbl srt) g1 :: xs => pair (pair lbl srt) (unfold_lrec g1) :: next xs 
        end 
      in l_send p (next l)
    | l_recv p l =>
      let fix next l :=
        match l with
          | nil                          => nil
          | pair (pair lbl srt) g1 :: xs => pair (pair lbl srt) (unfold_lrec g1) :: next xs 
        end 
      in l_send p (next l)
    | _            => s
  end.

(* Let lt := l_rec (l_send "p" (cons (pair (pair "x" gnat) (l_var 0)) nil)).
Print lt.
Compute unfold_lrec lt.

Let lt2 := Eval compute in unfold_lrec lt.
Print lt2.
Let lt3 := Eval compute in unfold_lrec lt2.
Print lt3. *)

Definition upId_local_local  (sigma : ( fin ) -> local ) (Eq : forall x, sigma x = (l_var ) x) : forall x, (up_local_local sigma) x = (l_var ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_local  (sigmalocal : ( fin ) -> local ) (Eqlocal : forall x, sigmalocal x = (l_var ) x) (s : local ) : subst_local sigmalocal s = s :=
    match s return subst_local sigmalocal s = s with
    | l_var  s => Eqlocal s
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (idSubst_local sigmalocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (idSubst_local sigmalocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal)) s0)
    end.

Definition upExtRen_local_local   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_local_local xi) x = (upRen_local_local zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_local   (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) (Eqlocal : forall x, xilocal x = zetalocal x) (s : local ) : ren_local xilocal s = ren_local zetalocal s :=
    match s return ren_local xilocal s = ren_local zetalocal s with
    | l_var  s => (ap) (l_var ) (Eqlocal s)
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (extRen_local xilocal zetalocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (extRen_local xilocal zetalocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) s0)
    end.

Definition upExt_local_local   (sigma : ( fin ) -> local ) (tau : ( fin ) -> local ) (Eq : forall x, sigma x = tau x) : forall x, (up_local_local sigma) x = (up_local_local tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_local   (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (Eqlocal : forall x, sigmalocal x = taulocal x) (s : local ) : subst_local sigmalocal s = subst_local taulocal s :=
    match s return subst_local sigmalocal s = subst_local taulocal s with
    | l_var  s => Eqlocal s
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (ext_local sigmalocal taulocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (ext_local sigmalocal taulocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) s0)
    end.

Definition up_ren_ren_local_local    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_local_local tau) (upRen_local_local xi)) x = (upRen_local_local theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_local    (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) (rholocal : ( fin ) -> fin) (Eqlocal : forall x, ((funcomp) zetalocal xilocal) x = rholocal x) (s : local ) : ren_local zetalocal (ren_local xilocal s) = ren_local rholocal s :=
    match s return ren_local zetalocal (ren_local xilocal s) = ren_local rholocal s with
    | l_var  s => (ap) (l_var ) (Eqlocal s)
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal)) s0)
    end.

Definition up_ren_subst_local_local    (xi : ( fin ) -> fin) (tau : ( fin ) -> local ) (theta : ( fin ) -> local ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_local_local tau) (upRen_local_local xi)) x = (up_local_local theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_local    (xilocal : ( fin ) -> fin) (taulocal : ( fin ) -> local ) (thetalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) taulocal xilocal) x = thetalocal x) (s : local ) : subst_local taulocal (ren_local xilocal s) = subst_local thetalocal s :=
    match s return subst_local taulocal (ren_local xilocal s) = subst_local thetalocal s with
    | l_var  s => Eqlocal s
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal)) s0)
    end.

Definition up_subst_ren_local_local    (sigma : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) (theta : ( fin ) -> local ) (Eq : forall x, ((funcomp) (ren_local zetalocal) sigma) x = theta x) : forall x, ((funcomp) (ren_local (upRen_local_local zetalocal)) (up_local_local sigma)) x = (up_local_local theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_local (shift) (upRen_local_local zetalocal) ((funcomp) (shift) zetalocal) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_local zetalocal (shift) ((funcomp) (shift) zetalocal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_local (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_local    (sigmalocal : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) (thetalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) (ren_local zetalocal) sigmalocal) x = thetalocal x) (s : local ) : ren_local zetalocal (subst_local sigmalocal s) = subst_local thetalocal s :=
    match s return ren_local zetalocal (subst_local sigmalocal s) = subst_local thetalocal s with
    | l_var  s => Eqlocal s
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal)) s0)
    end.

Definition up_subst_subst_local_local    (sigma : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (theta : ( fin ) -> local ) (Eq : forall x, ((funcomp) (subst_local taulocal) sigma) x = theta x) : forall x, ((funcomp) (subst_local (up_local_local taulocal)) (up_local_local sigma)) x = (up_local_local theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_local (shift) (up_local_local taulocal) ((funcomp) (up_local_local taulocal) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_local taulocal (shift) ((funcomp) (ren_local (shift)) taulocal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_local (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_local    (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (thetalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) (subst_local taulocal) sigmalocal) x = thetalocal x) (s : local ) : subst_local taulocal (subst_local sigmalocal s) = subst_local thetalocal s :=
    match s return subst_local taulocal (subst_local sigmalocal s) = subst_local thetalocal s with
    | l_var  s => Eqlocal s
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal)) s0)
    end.

Definition rinstInst_up_local_local   (xi : ( fin ) -> fin) (sigma : ( fin ) -> local ) (Eq : forall x, ((funcomp) (l_var ) xi) x = sigma x) : forall x, ((funcomp) (l_var ) (upRen_local_local xi)) x = (up_local_local sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_local   (xilocal : ( fin ) -> fin) (sigmalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) (l_var ) xilocal) x = sigmalocal x) (s : local ) : ren_local xilocal s = subst_local sigmalocal s :=
    match s return ren_local xilocal s = subst_local sigmalocal s with
    | l_var  s => Eqlocal s
    | l_end   => congr_l_end 
    | l_send  s0 s1 => congr_l_send ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1)
    | l_recv  s0 s1 => congr_l_recv ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1)
    | l_rec  s0 => congr_l_rec ((rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal)) s0)
    end.

Lemma rinstInst_local   (xilocal : ( fin ) -> fin) : ren_local xilocal = subst_local ((funcomp) (l_var ) xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_local xilocal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_local  : subst_local (l_var ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_local (l_var ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_local  : @ren_local   (id) = id .
Proof. exact ((eq_trans) (rinstInst_local ((id) (_))) instId_local). Qed.

Lemma varL_local   (sigmalocal : ( fin ) -> local ) : (funcomp) (subst_local sigmalocal) (l_var ) = sigmalocal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_local   (xilocal : ( fin ) -> fin) : (funcomp) (ren_local xilocal) (l_var ) = (funcomp) (l_var ) xilocal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_local    (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (s : local ) : subst_local taulocal (subst_local sigmalocal s) = subst_local ((funcomp) (subst_local taulocal) sigmalocal) s .
Proof. exact (compSubstSubst_local sigmalocal taulocal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_local    (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) : (funcomp) (subst_local taulocal) (subst_local sigmalocal) = subst_local ((funcomp) (subst_local taulocal) sigmalocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_local sigmalocal taulocal n)). Qed.

Lemma compRen_local    (sigmalocal : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) (s : local ) : ren_local zetalocal (subst_local sigmalocal s) = subst_local ((funcomp) (ren_local zetalocal) sigmalocal) s .
Proof. exact (compSubstRen_local sigmalocal zetalocal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_local    (sigmalocal : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) : (funcomp) (ren_local zetalocal) (subst_local sigmalocal) = subst_local ((funcomp) (ren_local zetalocal) sigmalocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_local sigmalocal zetalocal n)). Qed.

Lemma renComp_local    (xilocal : ( fin ) -> fin) (taulocal : ( fin ) -> local ) (s : local ) : subst_local taulocal (ren_local xilocal s) = subst_local ((funcomp) taulocal xilocal) s .
Proof. exact (compRenSubst_local xilocal taulocal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_local    (xilocal : ( fin ) -> fin) (taulocal : ( fin ) -> local ) : (funcomp) (subst_local taulocal) (ren_local xilocal) = subst_local ((funcomp) taulocal xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_local xilocal taulocal n)). Qed.

Lemma renRen_local    (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) (s : local ) : ren_local zetalocal (ren_local xilocal s) = ren_local ((funcomp) zetalocal xilocal) s .
Proof. exact (compRenRen_local xilocal zetalocal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_local    (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) : (funcomp) (ren_local zetalocal) (ren_local xilocal) = ren_local ((funcomp) zetalocal xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_local xilocal zetalocal n)). Qed.

End local.











Global Instance Subst_local   : Subst1 (( fin ) -> local ) (local ) (local ) := @subst_local   .

Global Instance Ren_local   : Ren1 (( fin ) -> fin) (local ) (local ) := @ren_local   .

Global Instance VarInstance_local  : Var (fin) (local ) := @l_var  .

Notation "x '__local'" := (l_var x) (at level 5, format "x __local") : subst_scope.

Notation "x '__local'" := (@ids (_) (_) VarInstance_local x) (at level 5, only printing, format "x __local") : subst_scope.

Notation "'var'" := (l_var) (only printing, at level 1) : subst_scope.

Class Up_local X Y := up_local : ( X ) -> Y.

Notation "↑__local" := (up_local) (only printing) : subst_scope.

Notation "↑__local" := (up_local_local) (only printing) : subst_scope.

Global Instance Up_local_local   : Up_local (_) (_) := @up_local_local   .

Notation "s [ sigmalocal ]" := (subst_local sigmalocal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmalocal ]" := (subst_local sigmalocal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xilocal ⟩" := (ren_local xilocal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xilocal ⟩" := (ren_local xilocal) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_local,  Ren_local,  VarInstance_local.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_local,  Ren_local,  VarInstance_local in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_local| progress rewrite ?compComp_local| progress rewrite ?compComp'_local| progress rewrite ?rinstId_local| progress rewrite ?compRen_local| progress rewrite ?compRen'_local| progress rewrite ?renComp_local| progress rewrite ?renComp'_local| progress rewrite ?renRen_local| progress rewrite ?renRen'_local| progress rewrite ?varL_local| progress rewrite ?varLRen_local| progress (unfold up_ren, upRen_local_local, up_local_local)| progress (cbn [subst_local ren_local])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_local in *| progress rewrite ?compComp_local in *| progress rewrite ?compComp'_local in *| progress rewrite ?rinstId_local in *| progress rewrite ?compRen_local in *| progress rewrite ?compRen'_local in *| progress rewrite ?renComp_local in *| progress rewrite ?renComp'_local in *| progress rewrite ?renRen_local in *| progress rewrite ?renRen'_local in *| progress rewrite ?varL_local in *| progress rewrite ?varLRen_local in *| progress (unfold up_ren, upRen_local_local, up_local_local in *)| progress (cbn [subst_local ren_local] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_local).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_local).
