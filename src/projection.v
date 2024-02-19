From MPSTCoq Require Import src.global src.local.
Require Import List String Datatypes Lia.
Import ListNotations.
Open Scope list_scope.

Fixpoint g_part_list_h (g: global) (acc: list gpart): list gpart :=
  match g with
    | g_end        => acc
    | g_var n      => acc
    | g_rec g1     => g_part_list_h g1 acc
    | g_send p q l =>
      let fix next l :=
        match l with
          | nil                        => nil
          | pair (pair lbl s) g1 :: xs => (g_part_list_h g1 acc) ++ next xs
        end
      in (p :: q :: (List.filter (fun a => andb (negb (eqb a p)) (negb (eqb a q))) (next l)))
  end.

Definition g_part_list (g: global): list gpart := g_part_list_h g nil.

(* Let gt := g_rec (g_send "p" "q" (cons (pair (pair "x" gint) (g_var 0)) nil)).
Compute g_part_list gt.
Let gt2 := Eval compute in unfold_grec gt.
Print gt2.
Compute g_part_list gt2.
Let gt3 := Eval compute in unfold_grec gt2.
Print gt3.
Compute g_part_list gt3.
 *)

Fixpoint is_list_eqH (l: list (llabel*gsort*local)) (acc: (llabel*gsort*local)): bool :=
  match pair l acc with
    | pair ((pair (pair lbl gs) lt) :: xs) (pair (pair lbl2 gs2) lt2) =>
       if (andb (andb (eqb lbl lbl2) (gsort_eq gs gs2)) (local_eq lt lt2))
       then is_list_eqH xs acc
       else false
    | pair nil _ => true
  end.

Definition is_list_eq (l: list (llabel*gsort*local)): bool :=
  match l with
    | (pair (pair lbl gs) lt) :: xs => is_list_eqH xs (pair (pair lbl gs) lt)
    | nil                           => true
  end.

Definition is_part_in (g: global) (p: gpart): bool :=
  let l := g_part_list g in
  let fix next l :=
    match l with
      | x :: xs => andb (eqb x p) (next xs)
      | nil     => false 
    end
  in next l.

Definition merge (t1: local) (t2: local): option local :=
  if local_eq t1 t2 then Some t1
  else
    match pair t1 t2 with
      | pair (l_recv p l1) (l_recv q l2) =>
        if eqb p q then Some (l_recv p (l1 ++ l2))
        else None
      | _                                => None
    end.

Fixpoint merge_listH (l: list (llabel*gsort*local)) (t: local): option local :=
  match l with
    | nil                       => Some t
    | pair (pair lbl s) x :: xs => 
      let smm := merge t x in
      match smm with
        | Some mm => merge_listH xs mm
        | None    => merge_listH xs t
      end
  end.

Definition merge_list (l: list (llabel*gsort*local)): option local :=
  match l with
    | nil                       => None
    | pair (pair lbl s) x :: xs => merge_listH xs x
  end.

Fixpoint map_snd {A B C: Type} (f: B -> C) (l: list (prod A B)): list (prod A C) :=
  match l with
    | nil            => nil
    | pair a b :: xs => pair a (f b) :: map_snd f xs
  end.

Fixpoint remove_opH (l: list (prod (prod llabel gsort) (option local))) (acc: list (prod (prod llabel gsort) local)): 
  list (prod (prod llabel gsort) local) :=
  match l with
    | nil                              => acc
    | pair (pair lbl s) (Some x) :: xs => remove_opH xs (acc ++ [(pair (pair lbl s) x)])
    | pair (pair lbl s) None :: xs     => remove_opH xs acc
  end.

Definition remove_op (l: list (prod (prod llabel gsort) (option local))): list (prod (prod llabel gsort) local) := remove_opH l nil.

Fixpoint projection (g: global) (r: gpart): option local :=
  match g with
    | g_end        => Some l_end
    | g_var n      => Some (l_var n)
    | g_send p q l =>
      if andb (negb (eqb p q)) (eqb p r) then
(*       Some (l_send q (remove_op (map_snd (fun g => projection g p) l))) *)
        let fix next l r :=
          match l with
            | pair (pair lbl srt) g1 :: xs => 
              let pg1 := projection g1 r in
              match pg1 with
                | Some spg1 => pair (pair lbl srt) spg1 :: (next xs r)
                | None      => next xs r
              end
            | nil                          => nil
          end
        in Some (l_send q (next l r))
      else if andb (negb (eqb p q)) (eqb q r) then
        let fix next l r :=
          match l with
            | pair (pair lbl srt) g1 :: xs => 
             let pg1 := projection g1 r in
              match pg1 with
                | Some spg1 => pair (pair lbl srt) spg1 :: (next xs r)
                | None      => next xs r
              end
            | nil                          => nil
          end
      in Some (l_recv p (next l r))
      else if andb (negb (eqb p q)) (andb (negb (eqb p r)) (negb (eqb q r))) then
       let fix next l r :=
          match l with
            | pair (pair lbl srt) g1 :: xs =>
             let spg1 := projection g1 r in
             match spg1 with
               | Some pg1 => pair (pair lbl srt) pg1 :: next xs r
               | None     => next xs r
             end
            | nil                     => nil 
          end
      in 
      let ll := next l r in merge_list ll
      else None
    | g_rec g1 => if is_part_in g r 
                  then 
                  let mp := (projection g1 r) in
                    match mp with
                      | Some smp => Some (l_rec smp)
                      | None     => None
                    end 
                  else Some l_end
  end.

Fixpoint next l r: list (prod (prod llabel gsort) local)  :=
  match l with
    | pair (pair lbl srt) g1 :: xs => 
      let pg1 := projection g1 r in
      match pg1 with
        | Some spg1 => pair (pair lbl srt) spg1 :: (next xs r)
        | None      => next xs r
      end
    | nil                          => nil
  end.

Lemma proj_remove: forall l gt lt p x xs,
         projection gt p = Some lt ->
         remove_opH (map_snd (fun g : global => projection g p) l) (x :: xs) = 
         x :: remove_opH (map_snd (fun g : global => projection g p) l) xs.
Proof. intro l.
       induction l; intros.
       - simpl. easy.
       - simpl. destruct a as ((lbl2,s2),G2).
         simpl. 
         case_eq (projection G2 p); intros.
         specialize (IHl G2 l0 p x (xs ++ [pair (pair lbl2 s2) l0]) H0).
         rewrite IHl.
         easy.
         rewrite (IHl gt lt). easy. easy.
Qed.

Fixpoint is_in_global (l: list (prod (prod glabel gsort) global)) (lbl: llabel): bool :=
  match l with
    | nil                          => false
    | pair (pair lbl1 s1) g1 :: xs => if eqb lbl1 lbl then true else is_in_global xs lbl
  end.

Definition project_list (l: list (prod (prod glabel gsort) global)) (p: gpart): list (prod (prod llabel gsort) local) :=
  remove_op (map_snd (fun g => projection g p) l).

Lemma next_eq: forall l p, next l p = project_list l p.
Proof. intro l.
       induction l; intros.
       - simpl. unfold project_list, remove_op. simpl. easy.
       - simpl. destruct a as ((lbl,s),lt).
         case_eq ( projection lt p); intros lt2. intro H.
         unfold project_list, remove_op. simpl.
         rewrite H.
         rewrite IHl.
         rewrite (proj_remove l lt lt2). easy.
         easy.
         unfold remove_op. simpl.
         rewrite IHl. unfold project_list, remove_op.
         simpl.
         rewrite lt2. easy.
Qed.

Lemma merge_proceeds: forall (lt1 lt2: local),
  if local_eq lt1 lt2 then merge lt1 lt2 = Some lt1
  else exists l p, merge lt1 lt2 = Some (l_recv p l) \/ merge lt1 lt2 = None.
Proof. intros lt1.
       induction lt1; intros.
       - case_eq lt2; intros.
         + case_eq (Nat.eqb n n0); intros.
           * apply EqNat.beq_nat_true_stt in H0.
             subst. simpl. rewrite PeanoNat.Nat.eqb_refl.
             unfold merge. simpl.
             rewrite PeanoNat.Nat.eqb_refl.
             easy.
           * simpl. rewrite H0.
             exists nil. exists "". right.
             unfold merge. simpl. rewrite H0.
             easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
       - case_eq lt2; intros.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
       - case_eq lt2; intros.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + case_eq (local_eq (l_send l l0) (l_send l1 l2)); intros.
           * unfold merge. rewrite H0. easy.
           * exists nil. exists "". right. unfold merge.
             rewrite H0. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
       - case_eq lt2; intros.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + case_eq (local_eq (l_recv l l0) (l_recv l1 l2)); intros.
           * unfold merge. rewrite H0. easy.
           * case_eq (eqb l l1); intros.
             ** exists (l0 ++ l2). exists l. left. unfold merge.
                rewrite H0, H1.
                easy.
             ** exists nil. exists l. right.
                unfold merge. rewrite H0, H1. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
       - case_eq lt2; intros.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + simpl. unfold merge. simpl. exists nil. exists "". right. easy.
         + case_eq (local_eq (l_rec lt1) (l_rec l)); intros.
           * unfold merge. simpl in *. rewrite H0. easy.
           * exists nil. exists "". right.
             unfold merge. rewrite H0. easy.
Qed.

Lemma merge_listH_proceeds: forall l t,
  exists nl p, merge_listH l t = Some (l_recv p nl) \/ merge_listH l t = Some t.
Proof. intro l.
       induction l; intros.
       - simpl. exists nil. exists "". simpl. right. easy.
       - destruct a as ((lbl,s),lt).
         simpl.
         specialize (merge_proceeds t lt); intro HH.
         case_eq (local_eq t lt); intro Ha.
         + rewrite Ha in HH.
           rewrite HH.
           specialize (IHl t).
           destruct IHl as (nl,(p, IHl)).
           exists nl. exists p. easy.
         + rewrite Ha in HH.
           destruct HH as (nl, (p, [HH | HH])).
           rewrite HH.
           specialize (IHl (l_recv p nl)).
           destruct IHl as (nl2,(q,[IHl | IHl])).
           exists nl2. exists q.
           left. easy.
           exists nl. exists p.
           left. easy.
           rewrite HH.
           specialize(IHl t).
           destruct IHl as (nl2,(q,[IHl | IHl])).
           exists nl2. exists q.
           left. easy.
           exists nl. exists p.
           right. easy.
Qed.

Lemma merge_list_proceeds: forall l,
  match l with
    | nil   => merge_list l = None
    | pair (pair lbl s) t ::xs => exists nl p, merge_list l = Some (l_recv p nl) \/ merge_list l = Some t
  end.
Proof. intros.
       induction l; intros.
       - simpl. easy.
       - simpl. destruct a, p.
         specialize (merge_listH_proceeds l l0); intro HH.
         destruct HH as (nl, (p, [HH | HH])).
         exists nl. exists p.
         left. easy.
         exists nl. exists p. right. easy.
Qed.

Lemma _46inv: forall G p q,
              exists l,
              projection G p = Some (l_send q (project_list l p)) ->
              G = g_send p q l \/ (merge_list (project_list l p) = Some (l_send q (project_list l p))).
Proof. intros G.
       induction G.
       - intros. exists nil. intros. simpl in *. easy.
       - intros. exists nil. intros. simpl in *. easy.
       - intros p q.
         exists l. intro H.
         simpl in H.
         case_eq(andb (negb (g =? g0)) (g =? p)); intros.
         rewrite H0 in H.
         rewrite next_eq in H.
         inversion H.
         subst.
         rewrite Bool.andb_true_iff in H0.
         destruct H0. 
         rewrite eqb_eq in H1.
         subst. left. easy.
         rewrite H0 in H.
         case_eq(andb (negb (g =? g0)) (g0 =? p)); intros.
         rewrite H1 in H.
         rewrite next_eq in H.
         easy.
         rewrite H1 in H.
         case_eq(andb (negb (g =? g0)) (andb (negb (g =? p)) (negb (g0 =? p)))); intros.
         rewrite H2 in H.
         rewrite next_eq in H.
         right. easy.
         rewrite H2 in H. easy.
       - intros.
         specialize(IHG p q).
         simpl.
         destruct IHG as (l, IHG).
         exists l.
         intros.
         case_eq(is_part_in (g_rec G) p); intros.
         rewrite H0 in H.
         case_eq(projection G p); intros.
         rewrite H1 in H. easy.
         rewrite H1 in H. easy.
         rewrite H0 in H.
         easy.
Qed.




(*
Definition gg := g_send "q" "r" (cons (pair (pair "l3" gint) g_end)
                                (cons (pair (pair "l4" gint) g_end) nil)).

Compute projection gg "r".

Definition g := g_send "p" "q" (cons (pair (pair "l1" gint) gg)
                               (cons (pair (pair "l2" gbool) gg) nil)).

Print g.

Compute projection g "q".

Definition G1 := g_send "q" "r" (cons (pair (pair "l3" gint) g_end)
                                (cons (pair (pair "l5" gint) g_end) nil)).

Print G1.

Compute projection G1 "p".

Definition G2 := g_send "q" "r" (cons (pair (pair "l4" gint) g_end)
                                (cons (pair (pair "l5" gint) g_end) nil)).

Definition G := g_send "p" "q" (cons (pair (pair "l1" gint) G1)
                               (cons (pair (pair "l2" gbool) G2) nil)).

Compute projection G "r". *)



























