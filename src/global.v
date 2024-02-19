From MPSTCoq Require Export src.unscoped.
Require Import List String.
Open Scope string_scope.

Definition gpart := string.
Definition glabel := string.

Inductive gsort: Type :=
  | gint : gsort
  | gnat : gsort 
  | gbool: gsort.

Definition subsort (s1 s2: gsort): bool :=
  match pair s1 s2 with
    | pair gnat gint => true
    | _              => false
  end.

Definition gsort_eq (gs1 gs2: gsort): bool :=
  match pair gs1 gs2 with
    | pair gint gint   => true
    | pair gnat gnat   => true
    | pair gbool gbool => true
    | _                => false 
  end.

Section global.
Inductive global  : Type :=
  | g_var : ( fin ) -> global 
  | g_end : global 
  | g_send : ( gpart   ) -> ( gpart   ) -> ( list (prod (prod (glabel  ) (gsort  )) (global  )) ) -> global 
  | g_rec : ( global   ) -> global .

Lemma congr_g_end  : g_end  = g_end  .
Proof. congruence. Qed.

Lemma congr_g_send  { s0 : gpart   } { s1 : gpart   } { s2 : list (prod (prod (glabel  ) (gsort  )) (global  )) } { t0 : gpart   } { t1 : gpart   } { t2 : list (prod (prod (glabel  ) (gsort  )) (global  )) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : g_send  s0 s1 s2 = g_send  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_g_rec  { s0 : global   } { t0 : global   } (H1 : s0 = t0) : g_rec  s0 = g_rec  t0 .
Proof. congruence. Qed.

Definition upRen_global_global   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_global   (xiglobal : ( fin ) -> fin) (s : global ) : global  :=
    match s return global  with
    | g_var  s => (g_var ) (xiglobal s)
    | g_end   => g_end 
    | g_send  s0 s1 s2 => g_send  ((fun x => x) s0) ((fun x => x) s1) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_global xiglobal))) s2)
    | g_rec  s0 => g_rec  ((ren_global (upRen_global_global xiglobal)) s0)
    end.

Definition up_global_global   (sigma : ( fin ) -> global ) : ( fin ) -> global  :=
  (scons) ((g_var ) (var_zero)) ((funcomp) (ren_global (shift)) sigma).

Fixpoint subst_global   (sigmaglobal : ( fin ) -> global ) (s : global ) : global  :=
    match s return global  with
    | g_var  s => sigmaglobal s
    | g_end   => g_end 
    | g_send  s0 s1 s2 => g_send  ((fun x => x) s0) ((fun x => x) s1) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_global sigmaglobal))) s2)
    | g_rec  s0 => g_rec  ((subst_global (up_global_global sigmaglobal)) s0)
    end.

Fixpoint unfold_grec (s: global): global :=
  match s with
    | g_rec g      => subst_global ((g_rec g) .: g_var) g
    | g_send p q l =>
      let fix next l :=
        match l with
          | nil                          => nil
          | pair (pair lbl srt) g1 :: xs => pair (pair lbl srt) (unfold_grec g1) :: next xs 
        end 
      in g_send p q (next l)
    | _            => s
  end.

Let gt := g_rec (g_send "p" "q" (cons (pair (pair "x" gint) (g_var 0)) nil)).
Print gt.
Compute unfold_grec gt.

Definition upId_global_global  (sigma : ( fin ) -> global ) (Eq : forall x, sigma x = (g_var ) x) : forall x, (up_global_global sigma) x = (g_var ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_global (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_global  (sigmaglobal : ( fin ) -> global ) (Eqglobal : forall x, sigmaglobal x = (g_var ) x) (s : global ) : subst_global sigmaglobal s = s :=
    match s return subst_global sigmaglobal s = s with
    | g_var  s => Eqglobal s
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (idSubst_global sigmaglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((idSubst_global (up_global_global sigmaglobal) (upId_global_global (_) Eqglobal)) s0)
    end.

Definition upExtRen_global_global   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_global_global xi) x = (upRen_global_global zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_global   (xiglobal : ( fin ) -> fin) (zetaglobal : ( fin ) -> fin) (Eqglobal : forall x, xiglobal x = zetaglobal x) (s : global ) : ren_global xiglobal s = ren_global zetaglobal s :=
    match s return ren_global xiglobal s = ren_global zetaglobal s with
    | g_var  s => (ap) (g_var ) (Eqglobal s)
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (extRen_global xiglobal zetaglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((extRen_global (upRen_global_global xiglobal) (upRen_global_global zetaglobal) (upExtRen_global_global (_) (_) Eqglobal)) s0)
    end.

Definition upExt_global_global   (sigma : ( fin ) -> global ) (tau : ( fin ) -> global ) (Eq : forall x, sigma x = tau x) : forall x, (up_global_global sigma) x = (up_global_global tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_global (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_global   (sigmaglobal : ( fin ) -> global ) (tauglobal : ( fin ) -> global ) (Eqglobal : forall x, sigmaglobal x = tauglobal x) (s : global ) : subst_global sigmaglobal s = subst_global tauglobal s :=
    match s return subst_global sigmaglobal s = subst_global tauglobal s with
    | g_var  s => Eqglobal s
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (ext_global sigmaglobal tauglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((ext_global (up_global_global sigmaglobal) (up_global_global tauglobal) (upExt_global_global (_) (_) Eqglobal)) s0)
    end.

Definition up_ren_ren_global_global    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_global_global tau) (upRen_global_global xi)) x = (upRen_global_global theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_global    (xiglobal : ( fin ) -> fin) (zetaglobal : ( fin ) -> fin) (rhoglobal : ( fin ) -> fin) (Eqglobal : forall x, ((funcomp) zetaglobal xiglobal) x = rhoglobal x) (s : global ) : ren_global zetaglobal (ren_global xiglobal s) = ren_global rhoglobal s :=
    match s return ren_global zetaglobal (ren_global xiglobal s) = ren_global rhoglobal s with
    | g_var  s => (ap) (g_var ) (Eqglobal s)
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenRen_global xiglobal zetaglobal rhoglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((compRenRen_global (upRen_global_global xiglobal) (upRen_global_global zetaglobal) (upRen_global_global rhoglobal) (up_ren_ren (_) (_) (_) Eqglobal)) s0)
    end.

Definition up_ren_subst_global_global    (xi : ( fin ) -> fin) (tau : ( fin ) -> global ) (theta : ( fin ) -> global ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_global_global tau) (upRen_global_global xi)) x = (up_global_global theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_global (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_global    (xiglobal : ( fin ) -> fin) (tauglobal : ( fin ) -> global ) (thetaglobal : ( fin ) -> global ) (Eqglobal : forall x, ((funcomp) tauglobal xiglobal) x = thetaglobal x) (s : global ) : subst_global tauglobal (ren_global xiglobal s) = subst_global thetaglobal s :=
    match s return subst_global tauglobal (ren_global xiglobal s) = subst_global thetaglobal s with
    | g_var  s => Eqglobal s
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenSubst_global xiglobal tauglobal thetaglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((compRenSubst_global (upRen_global_global xiglobal) (up_global_global tauglobal) (up_global_global thetaglobal) (up_ren_subst_global_global (_) (_) (_) Eqglobal)) s0)
    end.

Definition up_subst_ren_global_global    (sigma : ( fin ) -> global ) (zetaglobal : ( fin ) -> fin) (theta : ( fin ) -> global ) (Eq : forall x, ((funcomp) (ren_global zetaglobal) sigma) x = theta x) : forall x, ((funcomp) (ren_global (upRen_global_global zetaglobal)) (up_global_global sigma)) x = (up_global_global theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_global (shift) (upRen_global_global zetaglobal) ((funcomp) (shift) zetaglobal) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_global zetaglobal (shift) ((funcomp) (shift) zetaglobal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_global (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_global    (sigmaglobal : ( fin ) -> global ) (zetaglobal : ( fin ) -> fin) (thetaglobal : ( fin ) -> global ) (Eqglobal : forall x, ((funcomp) (ren_global zetaglobal) sigmaglobal) x = thetaglobal x) (s : global ) : ren_global zetaglobal (subst_global sigmaglobal s) = subst_global thetaglobal s :=
    match s return ren_global zetaglobal (subst_global sigmaglobal s) = subst_global thetaglobal s with
    | g_var  s => Eqglobal s
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstRen_global sigmaglobal zetaglobal thetaglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((compSubstRen_global (up_global_global sigmaglobal) (upRen_global_global zetaglobal) (up_global_global thetaglobal) (up_subst_ren_global_global (_) (_) (_) Eqglobal)) s0)
    end.

Definition up_subst_subst_global_global    (sigma : ( fin ) -> global ) (tauglobal : ( fin ) -> global ) (theta : ( fin ) -> global ) (Eq : forall x, ((funcomp) (subst_global tauglobal) sigma) x = theta x) : forall x, ((funcomp) (subst_global (up_global_global tauglobal)) (up_global_global sigma)) x = (up_global_global theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_global (shift) (up_global_global tauglobal) ((funcomp) (up_global_global tauglobal) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_global tauglobal (shift) ((funcomp) (ren_global (shift)) tauglobal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_global (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_global    (sigmaglobal : ( fin ) -> global ) (tauglobal : ( fin ) -> global ) (thetaglobal : ( fin ) -> global ) (Eqglobal : forall x, ((funcomp) (subst_global tauglobal) sigmaglobal) x = thetaglobal x) (s : global ) : subst_global tauglobal (subst_global sigmaglobal s) = subst_global thetaglobal s :=
    match s return subst_global tauglobal (subst_global sigmaglobal s) = subst_global thetaglobal s with
    | g_var  s => Eqglobal s
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstSubst_global sigmaglobal tauglobal thetaglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((compSubstSubst_global (up_global_global sigmaglobal) (up_global_global tauglobal) (up_global_global thetaglobal) (up_subst_subst_global_global (_) (_) (_) Eqglobal)) s0)
    end.

Definition rinstInst_up_global_global   (xi : ( fin ) -> fin) (sigma : ( fin ) -> global ) (Eq : forall x, ((funcomp) (g_var ) xi) x = sigma x) : forall x, ((funcomp) (g_var ) (upRen_global_global xi)) x = (up_global_global sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_global (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_global   (xiglobal : ( fin ) -> fin) (sigmaglobal : ( fin ) -> global ) (Eqglobal : forall x, ((funcomp) (g_var ) xiglobal) x = sigmaglobal x) (s : global ) : ren_global xiglobal s = subst_global sigmaglobal s :=
    match s return ren_global xiglobal s = subst_global sigmaglobal s with
    | g_var  s => Eqglobal s
    | g_end   => congr_g_end 
    | g_send  s0 s1 s2 => congr_g_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (rinst_inst_global xiglobal sigmaglobal Eqglobal))) s2)
    | g_rec  s0 => congr_g_rec ((rinst_inst_global (upRen_global_global xiglobal) (up_global_global sigmaglobal) (rinstInst_up_global_global (_) (_) Eqglobal)) s0)
    end.

Lemma rinstInst_global   (xiglobal : ( fin ) -> fin) : ren_global xiglobal = subst_global ((funcomp) (g_var ) xiglobal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_global xiglobal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_global  : subst_global (g_var ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_global (g_var ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_global  : @ren_global   (id) = id .
Proof. exact ((eq_trans) (rinstInst_global ((id) (_))) instId_global). Qed.

Lemma varL_global   (sigmaglobal : ( fin ) -> global ) : (funcomp) (subst_global sigmaglobal) (g_var ) = sigmaglobal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_global   (xiglobal : ( fin ) -> fin) : (funcomp) (ren_global xiglobal) (g_var ) = (funcomp) (g_var ) xiglobal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_global    (sigmaglobal : ( fin ) -> global ) (tauglobal : ( fin ) -> global ) (s : global ) : subst_global tauglobal (subst_global sigmaglobal s) = subst_global ((funcomp) (subst_global tauglobal) sigmaglobal) s .
Proof. exact (compSubstSubst_global sigmaglobal tauglobal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_global    (sigmaglobal : ( fin ) -> global ) (tauglobal : ( fin ) -> global ) : (funcomp) (subst_global tauglobal) (subst_global sigmaglobal) = subst_global ((funcomp) (subst_global tauglobal) sigmaglobal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_global sigmaglobal tauglobal n)). Qed.

Lemma compRen_global    (sigmaglobal : ( fin ) -> global ) (zetaglobal : ( fin ) -> fin) (s : global ) : ren_global zetaglobal (subst_global sigmaglobal s) = subst_global ((funcomp) (ren_global zetaglobal) sigmaglobal) s .
Proof. exact (compSubstRen_global sigmaglobal zetaglobal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_global    (sigmaglobal : ( fin ) -> global ) (zetaglobal : ( fin ) -> fin) : (funcomp) (ren_global zetaglobal) (subst_global sigmaglobal) = subst_global ((funcomp) (ren_global zetaglobal) sigmaglobal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_global sigmaglobal zetaglobal n)). Qed.

Lemma renComp_global    (xiglobal : ( fin ) -> fin) (tauglobal : ( fin ) -> global ) (s : global ) : subst_global tauglobal (ren_global xiglobal s) = subst_global ((funcomp) tauglobal xiglobal) s .
Proof. exact (compRenSubst_global xiglobal tauglobal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_global    (xiglobal : ( fin ) -> fin) (tauglobal : ( fin ) -> global ) : (funcomp) (subst_global tauglobal) (ren_global xiglobal) = subst_global ((funcomp) tauglobal xiglobal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_global xiglobal tauglobal n)). Qed.

Lemma renRen_global    (xiglobal : ( fin ) -> fin) (zetaglobal : ( fin ) -> fin) (s : global ) : ren_global zetaglobal (ren_global xiglobal s) = ren_global ((funcomp) zetaglobal xiglobal) s .
Proof. exact (compRenRen_global xiglobal zetaglobal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_global    (xiglobal : ( fin ) -> fin) (zetaglobal : ( fin ) -> fin) : (funcomp) (ren_global zetaglobal) (ren_global xiglobal) = ren_global ((funcomp) zetaglobal xiglobal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_global xiglobal zetaglobal n)). Qed.

End global.









Global Instance Subst_global   : Subst1 (( fin ) -> global ) (global ) (global ) := @subst_global   .

Global Instance Ren_global   : Ren1 (( fin ) -> fin) (global ) (global ) := @ren_global   .

Global Instance VarInstance_global  : Var (fin) (global ) := @g_var  .

Notation "x '__global'" := (g_var x) (at level 5, format "x __global") : subst_scope.

Notation "x '__global'" := (@ids (_) (_) VarInstance_global x) (at level 5, only printing, format "x __global") : subst_scope.

Notation "'var'" := (g_var) (only printing, at level 1) : subst_scope.

Class Up_global X Y := up_global : ( X ) -> Y.

Notation "↑__global" := (up_global) (only printing) : subst_scope.

Notation "↑__global" := (up_global_global) (only printing) : subst_scope.

Global Instance Up_global_global   : Up_global (_) (_) := @up_global_global   .

Notation "s [ sigmaglobal ]" := (subst_global sigmaglobal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaglobal ]" := (subst_global sigmaglobal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiglobal ⟩" := (ren_global xiglobal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiglobal ⟩" := (ren_global xiglobal) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_global,  Ren_global,  VarInstance_global.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_global,  Ren_global,  VarInstance_global in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_global| progress rewrite ?compComp_global| progress rewrite ?compComp'_global| progress rewrite ?rinstId_global| progress rewrite ?compRen_global| progress rewrite ?compRen'_global| progress rewrite ?renComp_global| progress rewrite ?renComp'_global| progress rewrite ?renRen_global| progress rewrite ?renRen'_global| progress rewrite ?varL_global| progress rewrite ?varLRen_global| progress (unfold up_ren, upRen_global_global, up_global_global)| progress (cbn [subst_global ren_global])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_global in *| progress rewrite ?compComp_global in *| progress rewrite ?compComp'_global in *| progress rewrite ?rinstId_global in *| progress rewrite ?compRen_global in *| progress rewrite ?compRen'_global in *| progress rewrite ?renComp_global in *| progress rewrite ?renComp'_global in *| progress rewrite ?renRen_global in *| progress rewrite ?renRen'_global in *| progress rewrite ?varL_global in *| progress rewrite ?varLRen_global in *| progress (unfold up_ren, upRen_global_global, up_global_global in *)| progress (cbn [subst_global ren_global] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_global).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_global).
