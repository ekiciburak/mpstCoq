Require Import List String ZArith.
From MPSTCoq Require Import src.unscoped.

Variant value: Type :=
  | vint : Z      -> value
  | vbool: bool   -> value.

Variant sort: Type :=
  | sint : sort
  | sbool: sort.

Section expr.
Inductive expr  : Type :=
  | e_var : ( fin ) -> expr 
  | e_val : ( value   ) -> expr 
  | e_succ : ( expr   ) -> expr 
  | e_neg : ( expr   ) -> expr 
  | e_not : ( expr   ) -> expr 
  | e_gt : ( expr   ) -> ( expr   ) -> expr
  | e_plus: ( expr   ) -> ( expr   ) -> expr.

Lemma congr_e_val  { s0 : value   } { t0 : value   } (H1 : s0 = t0) : e_val  s0 = e_val  t0 .
Proof. congruence. Qed.

Lemma congr_e_succ  { s0 : expr   } { t0 : expr   } (H1 : s0 = t0) : e_succ  s0 = e_succ  t0 .
Proof. congruence. Qed.

Lemma congr_e_neg  { s0 : expr   } { t0 : expr   } (H1 : s0 = t0) : e_neg  s0 = e_neg  t0 .
Proof. congruence. Qed.

Lemma congr_e_not  { s0 : expr   } { t0 : expr   } (H1 : s0 = t0) : e_not  s0 = e_not  t0 .
Proof. congruence. Qed.

Lemma congr_e_gt  { s0 : expr   } { s1 : expr   } { t0 : expr   } { t1 : expr   } (H1 : s0 = t0) (H2 : s1 = t1) : e_gt  s0 s1 = e_gt  t0 t1 .
Proof. congruence. Qed.

Lemma congr_e_plus { s0 : expr   } { s1 : expr   } { t0 : expr   } { t1 : expr   } (H1 : s0 = t0) (H2 : s1 = t1) : e_plus  s0 s1 = e_plus  t0 t1 .
Proof. congruence. Qed.


(* Lemma congr_elam  { s0 : expr   } { t0 : expr   } (H1 : s0 = t0) : elam  s0 = elam  t0 .
Proof. congruence. Qed. *)

Definition upRen_expr_expr   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_expr   (xiexpr : ( fin ) -> fin) (s : expr ) : expr  :=
    match s return expr  with
    | e_var  s => (e_var ) (xiexpr s)
    | e_val  s0 => e_val  ((fun x => x) s0)
    | e_succ  s0 => e_succ  ((ren_expr xiexpr) s0)
    | e_neg  s0 => e_neg  ((ren_expr xiexpr) s0)
    | e_not  s0 => e_not  ((ren_expr xiexpr) s0)
    | e_gt  s0 s1 => e_gt  ((ren_expr xiexpr) s0) ((ren_expr xiexpr) s1)
    | e_plus  s0 s1 => e_plus  ((ren_expr xiexpr) s0) ((ren_expr xiexpr) s1)
(*     | elam  s0 => elam  ((ren_expr (upRen_expr_expr xiexpr)) s0) *)
    end.

Definition up_expr_expr   (sigma : ( fin ) -> expr ) : ( fin ) -> expr  :=
  (scons) ((e_var ) (var_zero)) ((funcomp) (ren_expr (unscoped.shift)) sigma).

Fixpoint subst_expr   (sigmaexpr : ( fin ) -> expr ) (s : expr ) : expr  :=
    match s return expr  with
    | e_var  s => sigmaexpr s
    | e_val  s0 => e_val  ((fun x => x) s0)
    | e_succ  s0 => e_succ  ((subst_expr sigmaexpr) s0)
    | e_neg  s0 => e_neg  ((subst_expr sigmaexpr) s0)
    | e_not  s0 => e_not  ((subst_expr sigmaexpr) s0)
    | e_gt  s0 s1 => e_gt  ((subst_expr sigmaexpr) s0) ((subst_expr sigmaexpr) s1)
    | e_plus  s0 s1 => e_plus  ((subst_expr sigmaexpr) s0) ((subst_expr sigmaexpr) s1)
(*     | elam  s0 => elam  ((subst_expr (up_expr_expr sigmaexpr)) s0) *)
    end.

Definition upId_expr_expr  (sigma : ( fin ) -> expr ) (Eq : forall x, sigma x = (e_var ) x) : forall x, (up_expr_expr sigma) x = (e_var ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_expr (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_expr  (sigmaexpr : ( fin ) -> expr ) (Eqexpr : forall x, sigmaexpr x = (e_var ) x) (s : expr ) : subst_expr sigmaexpr s = s :=
    match s return subst_expr sigmaexpr s = s with
    | e_var  s => Eqexpr s
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((idSubst_expr sigmaexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((idSubst_expr sigmaexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((idSubst_expr sigmaexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((idSubst_expr sigmaexpr Eqexpr) s0) ((idSubst_expr sigmaexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((idSubst_expr sigmaexpr Eqexpr) s0) ((idSubst_expr sigmaexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((idSubst_expr (up_expr_expr sigmaexpr) (upId_expr_expr (_) Eqexpr)) s0)  *)
    end.

Definition upExtRen_expr_expr   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_expr_expr xi) x = (upRen_expr_expr zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (unscoped.shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_expr   (xiexpr : ( fin ) -> fin) (zetaexpr : ( fin ) -> fin) (Eqexpr : forall x, xiexpr x = zetaexpr x) (s : expr ) : ren_expr xiexpr s = ren_expr zetaexpr s :=
    match s return ren_expr xiexpr s = ren_expr zetaexpr s with
    | e_var  s => (ap) (e_var ) (Eqexpr s)
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((extRen_expr xiexpr zetaexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((extRen_expr xiexpr zetaexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((extRen_expr xiexpr zetaexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((extRen_expr xiexpr zetaexpr Eqexpr) s0) ((extRen_expr xiexpr zetaexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((extRen_expr xiexpr zetaexpr Eqexpr) s0) ((extRen_expr xiexpr zetaexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((extRen_expr (upRen_expr_expr xiexpr) (upRen_expr_expr zetaexpr) (upExtRen_expr_expr (_) (_) Eqexpr)) s0) *)
    end.

Definition upExt_expr_expr   (sigma : ( fin ) -> expr ) (tau : ( fin ) -> expr ) (Eq : forall x, sigma x = tau x) : forall x, (up_expr_expr sigma) x = (up_expr_expr tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_expr (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_expr   (sigmaexpr : ( fin ) -> expr ) (tauexpr : ( fin ) -> expr ) (Eqexpr : forall x, sigmaexpr x = tauexpr x) (s : expr ) : subst_expr sigmaexpr s = subst_expr tauexpr s :=
    match s return subst_expr sigmaexpr s = subst_expr tauexpr s with
    | e_var  s => Eqexpr s
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((ext_expr sigmaexpr tauexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((ext_expr sigmaexpr tauexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((ext_expr sigmaexpr tauexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((ext_expr sigmaexpr tauexpr Eqexpr) s0) ((ext_expr sigmaexpr tauexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((ext_expr sigmaexpr tauexpr Eqexpr) s0) ((ext_expr sigmaexpr tauexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((ext_expr (up_expr_expr sigmaexpr) (up_expr_expr tauexpr) (upExt_expr_expr (_) (_) Eqexpr)) s0) *)
    end.

Definition up_ren_ren_expr_expr    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_expr_expr tau) (upRen_expr_expr xi)) x = (upRen_expr_expr theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_expr    (xiexpr : ( fin ) -> fin) (zetaexpr : ( fin ) -> fin) (rhoexpr : ( fin ) -> fin) (Eqexpr : forall x, ((funcomp) zetaexpr xiexpr) x = rhoexpr x) (s : expr ) : ren_expr zetaexpr (ren_expr xiexpr s) = ren_expr rhoexpr s :=
    match s return ren_expr zetaexpr (ren_expr xiexpr s) = ren_expr rhoexpr s with
    | e_var  s => (ap) (e_var ) (Eqexpr s)
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s0) ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s0) ((compRenRen_expr xiexpr zetaexpr rhoexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((compRenRen_expr (upRen_expr_expr xiexpr) (upRen_expr_expr zetaexpr) (upRen_expr_expr rhoexpr) (up_ren_ren (_) (_) (_) Eqexpr)) s0) *)
    end.

Definition up_ren_subst_expr_expr    (xi : ( fin ) -> fin) (tau : ( fin ) -> expr ) (theta : ( fin ) -> expr ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_expr_expr tau) (upRen_expr_expr xi)) x = (up_expr_expr theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_expr (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_expr    (xiexpr : ( fin ) -> fin) (tauexpr : ( fin ) -> expr ) (thetaexpr : ( fin ) -> expr ) (Eqexpr : forall x, ((funcomp) tauexpr xiexpr) x = thetaexpr x) (s : expr ) : subst_expr tauexpr (ren_expr xiexpr s) = subst_expr thetaexpr s :=
    match s return subst_expr tauexpr (ren_expr xiexpr s) = subst_expr thetaexpr s with
    | e_var  s => Eqexpr s
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s0) ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s0) ((compRenSubst_expr xiexpr tauexpr thetaexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((compRenSubst_expr (upRen_expr_expr xiexpr) (up_expr_expr tauexpr) (up_expr_expr thetaexpr) (up_ren_subst_expr_expr (_) (_) (_) Eqexpr)) s0) *)
    end.

Definition up_subst_ren_expr_expr    (sigma : ( fin ) -> expr ) (zetaexpr : ( fin ) -> fin) (theta : ( fin ) -> expr ) (Eq : forall x, ((funcomp) (ren_expr zetaexpr) sigma) x = theta x) : forall x, ((funcomp) (ren_expr (upRen_expr_expr zetaexpr)) (up_expr_expr sigma)) x = (up_expr_expr theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_expr (unscoped.shift) (upRen_expr_expr zetaexpr) ((funcomp) (unscoped.shift) zetaexpr) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_expr zetaexpr (unscoped.shift) ((funcomp) (unscoped.shift) zetaexpr) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_expr (unscoped.shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_expr    (sigmaexpr : ( fin ) -> expr ) (zetaexpr : ( fin ) -> fin) (thetaexpr : ( fin ) -> expr ) (Eqexpr : forall x, ((funcomp) (ren_expr zetaexpr) sigmaexpr) x = thetaexpr x) (s : expr ) : ren_expr zetaexpr (subst_expr sigmaexpr s) = subst_expr thetaexpr s :=
    match s return ren_expr zetaexpr (subst_expr sigmaexpr s) = subst_expr thetaexpr s with
    | e_var  s => Eqexpr s
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s0) ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s0) ((compSubstRen_expr sigmaexpr zetaexpr thetaexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((compSubstRen_expr (up_expr_expr sigmaexpr) (upRen_expr_expr zetaexpr) (up_expr_expr thetaexpr) (up_subst_ren_expr_expr (_) (_) (_) Eqexpr)) s0) *)
    end.

Definition up_subst_subst_expr_expr    (sigma : ( fin ) -> expr ) (tauexpr : ( fin ) -> expr ) (theta : ( fin ) -> expr ) (Eq : forall x, ((funcomp) (subst_expr tauexpr) sigma) x = theta x) : forall x, ((funcomp) (subst_expr (up_expr_expr tauexpr)) (up_expr_expr sigma)) x = (up_expr_expr theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_expr (unscoped.shift) (up_expr_expr tauexpr) ((funcomp) (up_expr_expr tauexpr) (unscoped.shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_expr tauexpr (unscoped.shift) ((funcomp) (ren_expr (unscoped.shift)) tauexpr) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_expr (unscoped.shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_expr    (sigmaexpr : ( fin ) -> expr ) (tauexpr : ( fin ) -> expr ) (thetaexpr : ( fin ) -> expr ) (Eqexpr : forall x, ((funcomp) (subst_expr tauexpr) sigmaexpr) x = thetaexpr x) (s : expr ) : subst_expr tauexpr (subst_expr sigmaexpr s) = subst_expr thetaexpr s :=
    match s return subst_expr tauexpr (subst_expr sigmaexpr s) = subst_expr thetaexpr s with
    | e_var  s => Eqexpr s
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s0) ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s0) ((compSubstSubst_expr sigmaexpr tauexpr thetaexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((compSubstSubst_expr (up_expr_expr sigmaexpr) (up_expr_expr tauexpr) (up_expr_expr thetaexpr) (up_subst_subst_expr_expr (_) (_) (_) Eqexpr)) s0) *)
    end.

Definition rinstInst_up_expr_expr   (xi : ( fin ) -> fin) (sigma : ( fin ) -> expr ) (Eq : forall x, ((funcomp) (e_var ) xi) x = sigma x) : forall x, ((funcomp) (e_var ) (upRen_expr_expr xi)) x = (up_expr_expr sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_expr (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_expr   (xiexpr : ( fin ) -> fin) (sigmaexpr : ( fin ) -> expr ) (Eqexpr : forall x, ((funcomp) (e_var ) xiexpr) x = sigmaexpr x) (s : expr ) : ren_expr xiexpr s = subst_expr sigmaexpr s :=
    match s return ren_expr xiexpr s = subst_expr sigmaexpr s with
    | e_var  s => Eqexpr s
    | e_val  s0 => congr_e_val ((fun x => (eq_refl) x) s0)
    | e_succ  s0 => congr_e_succ ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s0)
    | e_neg  s0 => congr_e_neg ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s0)
    | e_not  s0 => congr_e_not ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s0)
    | e_gt  s0 s1 => congr_e_gt ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s0) ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s1)
    | e_plus  s0 s1 => congr_e_plus ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s0) ((rinst_inst_expr xiexpr sigmaexpr Eqexpr) s1)
(*     | elam  s0 => congr_elam ((rinst_inst_expr (upRen_expr_expr xiexpr) (up_expr_expr sigmaexpr) (rinstInst_up_expr_expr (_) (_) Eqexpr)) s0) *)
    end.

Lemma rinstInst_expr   (xiexpr : ( fin ) -> fin) : ren_expr xiexpr = subst_expr ((funcomp) (e_var ) xiexpr) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_expr xiexpr (_) (fun n => eq_refl) x)). Qed.

Lemma instId_expr  : subst_expr (e_var ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_expr (e_var ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_expr  : @ren_expr   (id) = id .
Proof. exact ((eq_trans) (rinstInst_expr ((id) (_))) instId_expr). Qed.

Lemma varL_expr   (sigmaexpr : ( fin ) -> expr ) : (funcomp) (subst_expr sigmaexpr) (e_var ) = sigmaexpr .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_expr   (xiexpr : ( fin ) -> fin) : (funcomp) (ren_expr xiexpr) (e_var ) = (funcomp) (e_var ) xiexpr .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_expr    (sigmaexpr : ( fin ) -> expr ) (tauexpr : ( fin ) -> expr ) (s : expr ) : subst_expr tauexpr (subst_expr sigmaexpr s) = subst_expr ((funcomp) (subst_expr tauexpr) sigmaexpr) s .
Proof. exact (compSubstSubst_expr sigmaexpr tauexpr (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_expr    (sigmaexpr : ( fin ) -> expr ) (tauexpr : ( fin ) -> expr ) : (funcomp) (subst_expr tauexpr) (subst_expr sigmaexpr) = subst_expr ((funcomp) (subst_expr tauexpr) sigmaexpr) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_expr sigmaexpr tauexpr n)). Qed.

Lemma compRen_expr    (sigmaexpr : ( fin ) -> expr ) (zetaexpr : ( fin ) -> fin) (s : expr ) : ren_expr zetaexpr (subst_expr sigmaexpr s) = subst_expr ((funcomp) (ren_expr zetaexpr) sigmaexpr) s .
Proof. exact (compSubstRen_expr sigmaexpr zetaexpr (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_expr    (sigmaexpr : ( fin ) -> expr ) (zetaexpr : ( fin ) -> fin) : (funcomp) (ren_expr zetaexpr) (subst_expr sigmaexpr) = subst_expr ((funcomp) (ren_expr zetaexpr) sigmaexpr) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_expr sigmaexpr zetaexpr n)). Qed.

Lemma renComp_expr    (xiexpr : ( fin ) -> fin) (tauexpr : ( fin ) -> expr ) (s : expr ) : subst_expr tauexpr (ren_expr xiexpr s) = subst_expr ((funcomp) tauexpr xiexpr) s .
Proof. exact (compRenSubst_expr xiexpr tauexpr (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_expr    (xiexpr : ( fin ) -> fin) (tauexpr : ( fin ) -> expr ) : (funcomp) (subst_expr tauexpr) (ren_expr xiexpr) = subst_expr ((funcomp) tauexpr xiexpr) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_expr xiexpr tauexpr n)). Qed.

Lemma renRen_expr    (xiexpr : ( fin ) -> fin) (zetaexpr : ( fin ) -> fin) (s : expr ) : ren_expr zetaexpr (ren_expr xiexpr s) = ren_expr ((funcomp) zetaexpr xiexpr) s .
Proof. exact (compRenRen_expr xiexpr zetaexpr (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_expr    (xiexpr : ( fin ) -> fin) (zetaexpr : ( fin ) -> fin) : (funcomp) (ren_expr zetaexpr) (ren_expr xiexpr) = ren_expr ((funcomp) zetaexpr xiexpr) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_expr xiexpr zetaexpr n)). Qed.

End expr.


Global Instance Subst_expr   : Subst1 (( fin ) -> expr ) (expr ) (expr ) := @subst_expr   .

Global Instance Ren_expr   : Ren1 (( fin ) -> fin) (expr ) (expr ) := @ren_expr   .

Global Instance VarInstance_expr  : Var (fin) (expr ) := @e_var  .

Notation "x '__expr'" := (e_var x) (at level 5, format "x __expr") : subst_scope.

Notation "x '__expr'" := (@ids (_) (_) VarInstance_expr x) (at level 5, only printing, format "x __expr") : subst_scope.

Notation "'var'" := (e_var) (only printing, at level 1) : subst_scope.

Class Up_expr X Y := up_expr : ( X ) -> Y.

Notation "↑__expr" := (up_expr) (only printing) : subst_scope.

Notation "↑__expr" := (up_expr_expr) (only printing) : subst_scope.

Global Instance Up_expr_expr   : Up_expr (_) (_) := @up_expr_expr   .

Notation "s [ sigmaexpr ]" := (subst_expr sigmaexpr s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexpr ]" := (subst_expr sigmaexpr) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexpr ⟩" := (ren_expr xiexpr s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexpr ⟩" := (ren_expr xiexpr) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_expr,  Ren_expr,  VarInstance_expr.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_expr,  Ren_expr,  VarInstance_expr in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_expr| progress rewrite ?compComp_expr| progress rewrite ?compComp'_expr| progress rewrite ?rinstId_expr| progress rewrite ?compRen_expr| progress rewrite ?compRen'_expr| progress rewrite ?renComp_expr| progress rewrite ?renComp'_expr| progress rewrite ?renRen_expr| progress rewrite ?renRen'_expr| progress rewrite ?varL_expr| progress rewrite ?varLRen_expr| progress (unfold up_ren, upRen_expr_expr, up_expr_expr)| progress (cbn [subst_expr ren_expr])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_expr in *| progress rewrite ?compComp_expr in *| progress rewrite ?compComp'_expr in *| progress rewrite ?rinstId_expr in *| progress rewrite ?compRen_expr in *| progress rewrite ?compRen'_expr in *| progress rewrite ?renComp_expr in *| progress rewrite ?renComp'_expr in *| progress rewrite ?renRen_expr in *| progress rewrite ?renRen'_expr in *| progress rewrite ?varL_expr in *| progress rewrite ?varLRen_expr in *| progress (unfold up_ren, upRen_expr_expr, up_expr_expr in *)| progress (cbn [subst_expr ren_expr] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_expr).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_expr).

Fixpoint eval_expr (e: expr): expr :=
  match e with
    | e_var s   => e_var s
    | e_val v   => e_val v
    | e_succ e1 =>
      let ee1 := eval_expr e1 in
      match ee1 with
        | e_val (vint n) => e_val (vint (n+1))
        | _              => e_succ ee1
      end
   | e_neg e1 =>
     let ee1 := eval_expr e1 in
     match e1 with
       | e_val (vint n) => e_val (vint (-n))
       | _              => e_neg ee1
     end
   | e_not e1   =>
     let ee1 := eval_expr e1 in
     match ee1 with
       | e_val (vbool b) => e_val (vbool (negb b))
       | _               => e_not ee1
     end
   | e_gt e1 e2 =>
     let ee1 := eval_expr e1 in
     let ee2 := eval_expr e2 in
     match (e1, e2) with
       | (e_val (vint n), e_val (vint m)) => e_val (vbool (Z.gtb n m)) 
       | _                                => e_gt ee1 ee2
     end
   | e_plus e1 e2 =>
     let ee1 := eval_expr e1 in
     let ee2 := eval_expr e2 in
     match (e1, e2) with
       | (e_val (vint n), e_val (vint m)) => e_val (vint (n + m)) 
       | _                                => e_plus ee1 ee2
     end
  end.
