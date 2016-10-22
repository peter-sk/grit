Require Export Basic.
Require Export Even.
Require Export Bool.
Require Export Recdef.
Require Import Allmaps.
Require Export BinaryTrees.
Require Export BinPos.

Definition Valuation := positive -> bool.

Section Literal.

Inductive Literal : Type :=
  | pos : positive -> Literal
  | neg : positive -> Literal.

Definition negate (l:Literal) : Literal :=
  match l with
  | pos n => neg n
  | neg n => pos n
  end.

Lemma literal_eq_dec : forall l l':Literal, {l = l'} + {l <> l'}.
induction l; induction l'; intros; try (right; discriminate);
elim Pos.eq_dec with p p0; intro; try (rewrite a; auto);
right; intro H; inversion H; auto.
Qed.

Fixpoint L_satisfies (v:Valuation) (l:Literal) : Prop :=
  match l with
  | pos x => if (v x) then True else False
  | neg x => if (v x) then False else True
  end.

Lemma L_satisfies_neg : forall v l, L_satisfies v l <-> ~ L_satisfies v (negate l).
intros; induction l; simpl; split; case (v p); auto.
Qed.

Lemma L_satisfies_neg_neg : forall v l, L_satisfies v l <-> L_satisfies v (negate (negate l)).
induction l; simpl; elim (v p); simpl; split; auto.
Qed.

Section Compare.

Definition Literal_compare (l l':Literal) : comparison :=
  match l, l' with 
  | pos n, pos n' => Pos.compare n n'
  | neg n, neg n' => Pos.compare n n'
  | neg n, pos n' => Lt
  | pos n, neg n' => Gt
  end.

Lemma eq_Lit_compare : forall l l', Literal_compare l l' = Eq -> l = l'.
induction l; induction l'; intros; inversion H; auto.
elim (Pos.compare_eq_iff p p0); intros; rewrite H0; auto.
elim (Pos.compare_eq_iff p p0); intros; rewrite H0; auto.
Qed.

Lemma Lit_compare_eq : forall l, Literal_compare l l = Eq.
induction l; elim (Pos.compare_eq_iff p p); auto.
Qed.

Lemma Lit_compare_trans : forall l l' l'', Literal_compare l l' = Lt -> Literal_compare l' l'' = Lt ->
                                           Literal_compare l l'' = Lt.
induction l; induction l'; induction l''; simpl; auto; intros.
elim (Pos.compare_lt_iff p p0); elim (Pos.compare_lt_iff p p1); intros.
apply H2; transitivity p0; auto.
inversion H.
inversion H0.
elim (Pos.compare_lt_iff p p0); elim (Pos.compare_lt_iff p p1); intros.
apply H2; transitivity p0; auto.
Qed.

Lemma Lit_compare_sym_Gt : forall l l', Literal_compare l l' = Gt -> Literal_compare l' l = Lt.
induction l; induction l'; simpl; intros;
elim (Pos.compare_lt_iff p0 p); elim (Pos.compare_gt_iff p p0); intros; auto.
Qed.

Lemma Lit_compare_sym_Lt : forall l l', Literal_compare l l' = Lt -> Literal_compare l' l = Gt.
induction l; induction l'; simpl; intros;
elim (Pos.compare_lt_iff p p0); elim (Pos.compare_gt_iff p0 p); intros; auto.
Qed.

End Compare.

End Literal.

Section Clauses.

Definition Clause := list Literal.

Fixpoint C_satisfies (v:Valuation) (c:Clause) : Prop :=
  match c with
  | nil => False
  | l :: c' => (L_satisfies v l) \/ (C_satisfies v c')
  end.

Lemma C_satisfies_exists : forall v c, C_satisfies v c ->
  exists l, In l c /\ L_satisfies v l.
induction c; intros.
inversion H.
inversion_clear H.
exists a; split; auto.
left; auto.

elim IHc; auto.
intros; exists x.
inversion_clear H; split; auto.
right; auto.
Qed.

Lemma exists_C_satisfies : forall v c l, In l c -> L_satisfies v l ->
  C_satisfies v c.
induction c; auto.
intros.
inversion_clear H.
rewrite H1; left; auto.
right; apply IHc with l; auto.
Qed.

Definition myclause := ((1,true) :: (2,false) :: (3,true) :: nil).
Definition myvaluation (n:nat) := if (even_odd_dec n) then false else true.

(*
Check (C_satisfies myvaluation myclause).
Eval simpl in (C_satisfies myvaluation myclause).
*)

Definition C_unsat (c:Clause) : Prop := forall v:Valuation, ~(C_satisfies v c).

Lemma C_unsat_empty : C_unsat nil.
red; auto.
Qed.

Definition true_C : Clause := (pos 1::neg 1::nil).

Lemma true_C_true : forall v:Valuation, C_satisfies v true_C.
simpl.
intro; elim (v 1%positive); auto.
Qed.

Lemma C_sat_clause : forall c:Clause, c <> nil -> ~(C_unsat c).
intro c; case c; intros.
elim H; auto.
intro Hu; red in Hu.
induction l.
apply Hu with (fun _ => true); simpl; auto.
apply Hu with (fun _ => false); simpl; auto.
Qed.

Lemma clause_eq_dec : forall c c':Clause, {c = c'} + {c <> c'}.
induction c, c'; auto.
right; discriminate.
right; discriminate.
elim (literal_eq_dec a l); intro Hs;
elim (IHc c'); intro Hc;
try (rewrite Hs; rewrite Hc; auto);
right; intro; inversion H;
try apply Hc; try apply Hs; auto.
Qed.

Lemma clause_eq_nil_cons : forall c: Clause, {c = nil} + {exists l c', c = l :: c'} .
intro c; case c; auto.
clear c; intros l c; right.
exists l; exists c; auto.
Qed.

Section Compare.

Fixpoint Clause_compare (cl cl':Clause) : comparison :=
  match cl, cl' with 
  | nil, nil => Eq
  | nil, _::_ => Lt
  | _::_, nil => Gt
  | l::c, l'::c' => match (Literal_compare l l') with
                    | Lt => Lt
                    | Gt => Gt
                    | Eq => Clause_compare c c'
  end end.

Lemma eq_Clause_compare : forall cl cl', Clause_compare cl cl' = Eq -> cl = cl'.
induction cl; induction cl'; intros; try (inversion H; auto; fail).
simpl in H.
revert H; set (w := Literal_compare a a0); assert (w = Literal_compare a a0); auto; clearbody w.
revert H; elim w; intros.
rewrite eq_Lit_compare with a a0; auto; rewrite IHcl with cl'; auto.
inversion H0.
inversion H0.
Qed.

Lemma Clause_compare_eq : forall cl, Clause_compare cl cl = Eq.
induction cl; simpl; auto; rewrite Lit_compare_eq; auto.
Qed.

Lemma Clause_compare_trans : forall cl cl' cl'', Clause_compare cl cl' = Lt -> Clause_compare cl' cl'' = Lt ->
                                           Clause_compare cl cl'' = Lt.
induction cl; induction cl'; induction cl''; simpl; auto; intros.
inversion H0.
inversion H.
revert H H0.
set (w0 := Literal_compare a a0); assert (w0 = Literal_compare a a0); auto; clearbody w0; revert H.
set (w1 := Literal_compare a a1); assert (w1 = Literal_compare a a1); auto; clearbody w1; revert H.
set (w2 := Literal_compare a0 a1); assert (w2 = Literal_compare a0 a1); auto; clearbody w2; revert H.
elim w0; elim w1; elim w2; auto; intros; try (inversion H2; fail); try (inversion H3; fail);
symmetry in H; symmetry in H0; symmetry in H1.
(* 1/8 *)
apply IHcl with cl'; auto.
(* 2/8 *)
replace a0 with a1 in H.
rewrite Lit_compare_eq in H; inversion H.
transitivity a; [symmetry | idtac]; apply eq_Lit_compare; auto.
(* 3/8 *)
replace a with a1 in H0.
rewrite Lit_compare_eq in H0; inversion H0.
transitivity a0; symmetry; apply eq_Lit_compare; auto.
(* 4/8 *)
rewrite (eq_Lit_compare _ _ H1) in H0.
rewrite <- H; auto.
(* 5/8 *)
rewrite (eq_Lit_compare _ _ H) in H1; rewrite (eq_Lit_compare _ _ H0) in H1.
rewrite Lit_compare_eq in H1; inversion H1.
(* 6/8 *)
rewrite (Lit_compare_trans a a0 a1) in H0; auto.
inversion H0.
(* 7/8 *)
rewrite (eq_Lit_compare _ _ H) in H1; rewrite H1 in H0; inversion H0.
(* 8/8 *)
rewrite (Lit_compare_trans a a0 a1) in H0; auto.
Qed.

Lemma Clause_compare_sym_Gt : forall cl cl', Clause_compare cl cl' = Gt -> Clause_compare cl' cl = Lt.
induction cl; induction cl'; simpl; intros; auto.
inversion H.
revert H; clear IHcl'.
set (w := Literal_compare a a0); assert (w = Literal_compare a a0); auto; clearbody w; revert H.
case w; intros.
rewrite (eq_Lit_compare _ _ (eq_sym H)); rewrite Lit_compare_eq; auto.
inversion H0.
rewrite (Lit_compare_sym_Gt _ _ (eq_sym H)); auto.
Qed.

Lemma Clause_compare_sym_Lt : forall cl cl', Clause_compare cl cl' = Lt -> Clause_compare cl' cl = Gt.
induction cl; induction cl'; simpl; intros; auto.
inversion H.
revert H; clear IHcl'.
set (w := Literal_compare a a0); assert (w = Literal_compare a a0); auto; clearbody w; revert H.
case w; intros.
rewrite (eq_Lit_compare _ _ (eq_sym H)); rewrite Lit_compare_eq; auto.
rewrite (Lit_compare_sym_Lt _ _ (eq_sym H)); auto.
inversion H0.
Qed.

End Compare.

End Clauses.

Section SetClauses.

Definition SetClause := BinaryTree Literal.

Definition SC_add := BT_add Literal_compare.
Definition SC_in := BT_In (T := Literal).
Definition SC_diff := BT_diff Literal_compare.
Definition SC_wf := BT_wf Literal_compare.
Definition SC_empty := nought (T := Literal).

Fixpoint Clause_to_SetClause (cl:Clause) : SetClause :=
  match cl with
  | nil => nought
  | l :: cl' => SC_add l (Clause_to_SetClause cl')
  end.

Lemma C_to_SC_wf : forall (cl:Clause), SC_wf (Clause_to_SetClause cl).
induction cl; simpl; red; simpl; auto.
apply BT_wf_add; auto.
apply eq_Lit_compare.
apply Lit_compare_eq.
apply Lit_compare_trans.
apply Lit_compare_sym_Gt.
apply Lit_compare_sym_Lt.
Qed.

Fixpoint SetClause_to_Clause (cl:SetClause) : Clause :=
  match cl with
  | nought => nil
  | node l cl' cl'' => l :: (SetClause_to_Clause cl') ++ (SetClause_to_Clause cl'')
  end.

Lemma list_append_split : forall A, forall P : A -> Prop,
  forall (l1 l2 w1 w2 : list A),
  (forall x, In x l1 -> P x) /\ (forall x, In x w1 -> P x) /\
  (forall x, In x l2 -> ~P x) /\ (forall x, In x w2 -> ~P x)
  -> (l1 ++ l2) = (w1 ++ w2) -> l1 = w1 /\ l2 = w2.
induction l1; induction w1; simpl; auto; intros.
(* 1/3 *)
exfalso; inversion_clear H; inversion_clear H2; inversion_clear H3.
apply H2 with a; auto.
rewrite H0; left; auto.
(* 2/3 *)
exfalso; inversion_clear H; inversion_clear H2; inversion_clear H3.
apply H4 with a; auto.
rewrite <- H0; left; auto.
(* 3/3 *)
inversion_clear H; inversion_clear H2; inversion_clear H3.
inversion H0.
elim (IHl1 l2 w1 w2); intros; auto.
rewrite H7; rewrite H3; auto.
Qed.

(* Coercion Clause_to_SetClause : Clause >-> SetClause. *)
Coercion SetClause_to_Clause : SetClause >-> Clause.

(*
Fixpoint SC_satisfies (v:Valuation) (cl:SetClause) : Prop :=
  match cl with
  | nought => False
  | node l cl' cl'' => (L_satisfies v l) \/ (C_satisfies v cl') \/ (C_satisfies v cl'')
  end.
*)

Lemma C_to_SC_In_1 : forall l c, In l c -> SC_in l (Clause_to_SetClause c).
induction c; auto.

simpl; intros.
set (eqL := eq_Lit_compare).
set (Leq := Lit_compare_eq).
inversion_clear H.
rewrite H0; clear H0.
apply BT_add_in; auto.
apply BT_add_mon; auto; apply IHc; auto.
Qed.

Lemma SC_to_C_In_1 : forall l c, In l (SetClause_to_Clause c) -> SC_in l c.
induction c; auto.

simpl; intros.
set (eqL := eq_Lit_compare).
set (Leq := Lit_compare_eq).
inversion_clear H; auto.
elim (in_app_or _ _ _ H0); auto.
Qed.

Lemma C_to_SC_In_2 : forall l c, SC_in l (Clause_to_SetClause c) -> In l c.
induction c; auto.

simpl; intros.
set (eqL := eq_Lit_compare).
set (Leq := Lit_compare_eq).
elim (BT_in_add _ _ _ _ _ H); auto.
Qed.

Lemma SC_to_C_In_2 : forall l c, SC_in l c -> In l (SetClause_to_Clause c).
induction c; auto.

simpl; intros.
set (eqL := eq_Lit_compare).
set (Leq := Lit_compare_eq).
inversion_clear H.
right; apply in_or_app; auto.
inversion_clear H0; auto.
right; apply in_or_app; auto.
Qed.

Lemma SetClause_to_Clause_inv : forall cl cl', SC_wf cl -> SC_wf cl' ->
  SetClause_to_Clause cl = SetClause_to_Clause cl' -> cl = cl'.
induction cl; induction cl'; simpl; intros; auto; inversion H1.
inversion_clear H; inversion_clear H5; inversion_clear H6.
inversion_clear H0; inversion_clear H8; inversion_clear H9.
elim list_append_split with
  (l1 := SetClause_to_Clause cl1) (l2 := SetClause_to_Clause cl2)
  (w1 := SetClause_to_Clause cl'1) (w2 := SetClause_to_Clause cl'2)
  (P := fun x => Literal_compare x t = Lt); intros; auto.
rewrite IHcl1 with cl'1; auto.
rewrite IHcl2 with cl'2; auto.
repeat split; intros.
apply H5; apply SC_to_C_In_1; auto.
rewrite H3; apply H8; apply SC_to_C_In_1; auto.
rewrite H7; [discriminate | apply SC_to_C_In_1; auto].
rewrite H3; rewrite H10; [discriminate | apply SC_to_C_In_1; auto].
Qed.

Lemma SC_satisfies_exists : forall (v:Valuation) (c:SetClause), C_satisfies v c ->
  exists l, SC_in l c /\ L_satisfies v l.
induction c; intros.
inversion H.

inversion_clear H.
exists t; split; simpl; auto.

elim (C_satisfies_exists _ _ H0); intros.
inversion_clear H; exists x; split; auto.
elim (in_app_or _ _ _ H1).
left; apply SC_to_C_In_1; auto.
right; right; apply SC_to_C_In_1; auto.
Qed.

Lemma exists_SC_satisfies : forall (v:Valuation) (c:SetClause) l,
  SC_in l c -> L_satisfies v l -> C_satisfies v c.
induction c; auto.
intros.
apply exists_C_satisfies with l; auto.
apply SC_to_C_In_2; auto.
Qed.

Lemma C_to_C_satisfies_1 : forall (v:Valuation) (c:Clause),
  C_satisfies v c -> C_satisfies v (SetClause_to_Clause (Clause_to_SetClause c)).
intros.
elim (C_satisfies_exists _ _ H); intros.
inversion_clear H0.
apply exists_C_satisfies with x; auto.
apply SC_to_C_In_2; apply C_to_SC_In_1; auto.
Qed.

Lemma C_to_C_satisfies_2 : forall (v:Valuation) (c:Clause),
  C_satisfies v (SetClause_to_Clause (Clause_to_SetClause c)) -> C_satisfies v c.
intros.
elim (C_satisfies_exists _ _ H); intros.
inversion_clear H0.
apply exists_C_satisfies with x; auto.
apply C_to_SC_In_2; apply SC_to_C_In_1; auto.
Qed.

(*
Definition C_unsat (c:Clause) : Prop := forall v:Valuation, ~(C_satisfies v c).

Lemma C_unsat_empty : C_unsat nought.
red; auto.
Qed.
*)

Definition true_SC : SetClause := (node (pos 1) (node (neg 1) nought nought) nought).

(*
Lemma true_C_true : forall v:Valuation, C_satisfies v true_C.
simpl.
intro; elim (v 1); auto.
Qed.

Lemma C_sat_clause : forall c:Clause, c <> nought -> ~(C_unsat c).
intro c; case c; intros.
elim H; auto.
intro Hu; red in Hu.
induction l.
apply Hu with (fun _ => true); simpl; auto.
apply Hu with (fun _ => false); simpl; auto.
Qed.
*)

Lemma SetClause_eq_dec : forall c c':SetClause, {c = c'} + {c <> c'}.
induction c, c'; auto.
right; discriminate.
right; discriminate.
elim (literal_eq_dec t l); intro Hs;
elim (IHc1 c'1); intro Hc1;
elim (IHc2 c'2); intro Hc2;
try (rewrite Hs; rewrite Hc1; rewrite Hc2; auto);
right; intro; inversion H;
try apply Hc; try apply Hs; auto.
Qed.

Lemma SetClause_eq_nil_cons : forall c: SetClause, {l:Literal & {c':SetClause & {c'':SetClause | c = node l c' c''}}} + {c = nought}.
intro c; case c; auto.
clear c; intros l c; left.
exists l; exists c; exists b; auto.
Qed.

End SetClauses.

Section CNF.

Definition CNF := BinaryTree Clause.

Definition CNF_in := BT_In (T := Clause).
Definition CNF_remove := BT_remove Clause_compare.
Definition CNF_wf := BT_wf Clause_compare.
Definition CNF_join := BT_add_all _ Clause_compare.
Definition CNF_add := BT_add Clause_compare.
Definition CNF_empty_constant := nought (T := Clause).

Lemma CNF_eq_dec : forall c c':CNF, {c = c'} + {c <> c'}.
induction c, c'; auto; try (right; discriminate).
elim (clause_eq_dec t c); intro H1;
elim (IHc1 c'1); intro H2;
elim (IHc2 c'2); intro H3;
try (rewrite H1; rewrite H2; rewrite H3; auto);
right; intro H; inversion H;
try (apply H1); try (apply H2); auto.
Qed.

Fixpoint satisfies (v:Valuation) (c:CNF) : Prop :=
  match c with
  | nought => True
  | node cl c' c'' => (C_satisfies v cl) /\ (satisfies v c') /\ (satisfies v c'')
  end.

Lemma satisfies_forall : forall v c, satisfies v c ->
  forall c', CNF_in c' c -> C_satisfies v c'.
induction c; intros; inversion_clear H0; inversion_clear H.
apply IHc1; inversion_clear H2; auto.
inversion_clear H1.
rewrite H; auto.
apply IHc2; inversion_clear H2; auto.
Qed.

Lemma forall_satisfies : forall v c, (forall c', CNF_in c' c -> C_satisfies v c') ->
  satisfies v c.
induction c; simpl; auto.
repeat split; auto.
Qed.

Lemma satisfies_remove : forall c:CNF, forall cl:Clause, forall v,
  satisfies v c -> satisfies v (CNF_remove cl c).
intros; apply forall_satisfies; intros.
apply satisfies_forall with c; auto.
eapply BT_remove_in; auto.
exact eq_Clause_compare.
exact Clause_compare_eq.
exact H0.
Qed.

Definition entails (c:CNF) (c':Clause) : Prop :=
  forall v:Valuation, satisfies v c -> C_satisfies v c'.

Definition unsat (c:CNF) : Prop := forall v:Valuation, ~(satisfies v c).

(*
Lemma unsat_remove : forall c:CNF, forall c':Clause,
  unsat (remove clause_eq_dec c' c) -> unsat c.
red; intros; intro.
apply H with v; apply satisfies_remove; auto.
Qed.
*)

Lemma unsat_subset : forall (c c':CNF),
  (forall cl, CNF_in cl c -> CNF_in cl c') -> unsat c -> unsat c'.
intros; intro; intro.
apply H0 with v.
apply forall_satisfies; intros; apply satisfies_forall with c'; auto.
Qed.

Lemma CNF_empty : forall c, entails c nil -> unsat c.
red; intros; intro.
apply C_unsat_empty with v.
apply H; auto.
Qed.

(*
Definition c1 := ((1,true) :: (2,false) :: nil).
Definition c2 := ((1,false) :: (2,true) :: nil).
Definition c3 := ((1,false) :: nil).
Definition c4 := ((2,true) :: (3,false) :: nil).
Definition cnf1 := (c1::c2::c3::c4::nil).

Eval simpl in (satisfies myvaluation cnf1).
*)

End CNF.

Section Unit_Propagation.

Lemma SC_in_add : forall (l l':Literal) (cl:SetClause),
  In l (SetClause_to_Clause (SC_add l' cl)) -> l = l' \/ In l (SetClause_to_Clause cl).
induction cl; intros.
inversion H; auto.
elim (BT_in_add _ _ _ _ _ (SC_to_C_In_1 _ _ H)); auto; clear H; intros; inversion_clear H; auto.
elim IHcl1; auto.
right; right; apply in_or_app; auto.
apply SC_to_C_In_2; apply BT_add_mon; auto.
apply eq_Lit_compare.
inversion_clear H0.
right; left; auto.
elim IHcl2; auto.
right; right; apply in_or_app; auto.
apply SC_to_C_In_2; apply BT_add_mon; auto.
apply eq_Lit_compare.
Qed.

Lemma propagate_singleton : forall (cs:CNF) (c c':SetClause), forall l,
  SC_diff c c' = (node l nought nought) ->
  entails cs (SetClause_to_Clause (SC_add (negate l) c')) -> entails (CNF_add c cs) c'.
intros.
red; intros.
set (eqC := eq_Clause_compare).
set (Ceq := Clause_compare_eq).

assert (C_satisfies v c).
apply (satisfies_forall _ _ H1).
apply BT_add_in; auto.

assert (satisfies v cs).
apply forall_satisfies; intros; apply (satisfies_forall _ _ H1); auto.
apply BT_add_mon; auto.

elim (C_satisfies_exists _ _ H2); intros l' Hl.
inversion_clear Hl.
elim (BT_diff_in_rev _ _ eq_Lit_compare Lit_compare_eq _ _ _ H l'); intros; auto.
apply exists_C_satisfies with l'; auto.
apply SC_to_C_In_2; auto.
clear H; inversion_clear H6.
inversion H.
inversion_clear H.
generalize (H0 v H3); clear H0.
rewrite <- H6.
intro H0; simpl in H0.
elim (C_satisfies_exists _ _ H0); intros.
inversion_clear H; apply exists_C_satisfies with x; auto.
elim (SC_in_add _ _ _ H7); auto; intros.
elim (L_satisfies_neg v l'); intros.
elim H9; auto; rewrite <- H; auto.
inversion H6.
apply SC_to_C_In_1; auto.
Qed.

Lemma propagate_empty : forall (cs:CNF) (c c':SetClause),
  SC_diff c c' = nought -> entails (BT_add Clause_compare c cs) c'.
red; intros.

set (eqC := eq_Clause_compare).
set (Ceq := Clause_compare_eq).

assert (C_satisfies v c).
apply (satisfies_forall _ _ H0).
apply BT_add_in; auto.

assert (satisfies v cs).
apply forall_satisfies; intros; apply (satisfies_forall _ _ H0); auto.
apply BT_add_mon; auto.

elim (C_satisfies_exists _ _ H1).
intros l Hl; inversion_clear Hl.
apply exists_C_satisfies with l; auto.
elim (BT_diff_in_rev _ _ eq_Lit_compare Lit_compare_eq _ _ _ H l); intros; auto.
apply SC_to_C_In_2; auto.
inversion H5.
apply SC_to_C_In_1; auto.
Qed.

Lemma propagate_entails : forall (cs:CNF) (c c':SetClause), CNF_in c cs ->
  entails (BT_add Clause_compare c cs) c' -> entails cs c'.
intros.
red; intros.
apply H0; auto.
apply forall_satisfies; intros.
elim (BT_in_add _ _ _ _ _ H2); intros.
apply satisfies_forall with cs; auto.
rewrite H3; clear H3 H2 c'0.
apply satisfies_forall with cs; auto.
Qed.

Lemma propagate_true : forall (cs:CNF) (c:SetClause),
  entails (CNF_add true_SC cs) c -> entails cs c.
intros.
red; intros.
apply H; auto.
apply forall_satisfies; intros.
elim (BT_in_add _ _ _ _ _ H1); intros.
apply satisfies_forall with cs; auto.
rewrite H2; apply true_C_true.
Qed.

End Unit_Propagation.

Section ICNF.

Definition ICNF := Map {cl:SetClause | SC_wf cl}.

Definition empty_ICNF : ICNF := M0 _.

Fixpoint ICNF_to_CNF (c:ICNF) : CNF :=
  match c with
  | M0 => nought
  | M1 _ cl => let (c,_) := cl in node (SetClause_to_Clause c) nought nought
  | M2 c' c'' => BT_add_all _ Clause_compare (ICNF_to_CNF c') (ICNF_to_CNF c'')
  end.

Coercion ICNF_to_CNF : ICNF >-> CNF.

Lemma ICNF_to_CNF_wf : forall (c:ICNF), CNF_wf (c:CNF).
induction c; red; simpl; auto.
induction a0; simpl; auto.
repeat split; intros; inversion H.
apply BT_wf_add_all; auto.
exact eq_Clause_compare.
exact Clause_compare_eq.
exact Clause_compare_trans.
exact Clause_compare_sym_Gt.
exact Clause_compare_sym_Lt.
Qed.

Lemma ICNF_get_in : forall c (cl:SetClause) i Hc,
  MapGet _ c i = Some (exist SC_wf cl Hc) -> CNF_in cl (ICNF_to_CNF c).
induction c; simpl; intros.
inversion H.
revert H; elim BinNat.N.eqb; simpl; intro; inversion H; simpl; auto.

set (eqC := eq_Clause_compare).
set (Ceq := Clause_compare_eq).
revert H; induction i; auto.
intro; apply BT_add_all_in; auto; revert H; apply IHc1.
induction p.
intro; apply BT_add_all_mon; auto; revert H; apply IHc2.
intro; apply BT_add_all_in; auto; revert H; apply IHc1.
intro; apply BT_add_all_mon; auto; revert H; apply IHc2.
Qed.

Lemma in_ICNF_get : forall c (cl:SetClause), SC_wf cl ->
  CNF_in cl (ICNF_to_CNF c) -> exists i Hc, MapGet _ c i = Some (exist SC_wf cl Hc).
induction c; simpl; intros.
inversion H0.
induction a0; inversion_clear H0; inversion_clear H1.

generalize p; rewrite SetClause_to_Clause_inv with x cl; auto; intros.
exists a; exists p0; elim (BinNat.N.eqb_eq a a); intros.
rewrite H2; simpl; auto.

inversion H0.
elim (BT_in_add_all _ _ _ _ _ H0); intro.
elim (IHc1 _ H H1); intros j Hj.

induction j.
exists BinNums.N0; auto.
exists (BinNums.Npos (BinNums.xO p)); auto.

elim (IHc2 _ H H1); intros j Hj.
induction j.
exists (BinNums.Npos BinNums.xH); auto.
exists (BinNums.Npos (BinNums.xI p)); auto.
Qed.

Lemma in_ICNF_get' : forall c (cl:Clause), CNF_in cl (ICNF_to_CNF c) ->
  exists i sc Hsc, MapGet _ c i = Some (exist SC_wf sc Hsc) /\ cl = SetClause_to_Clause sc.
induction c; simpl; intros.
inversion H.
induction a0; inversion_clear H; inversion_clear H0.

exists a; exists x; exists p; elim (BinNat.N.eqb_eq a a); intros.
rewrite H1; simpl; auto.

inversion H.
elim (BT_in_add_all _ _ _ _ _ H); intro.
elim (IHc1 _ H0); intros j Hj.

induction j.
exists BinNums.N0; auto.
exists (BinNums.Npos (BinNums.xO p)); auto.

elim (IHc2 _ H0); intros j Hj.
induction j.
exists (BinNums.Npos BinNums.xH); auto.
exists (BinNums.Npos (BinNums.xI p)); auto.
Qed.

Definition get_ICNF (c:ICNF) i : SetClause :=
  match (MapGet _ c i) with
  | None => true_SC
  | Some cl => let (c,_) := cl in c
  end.

(*
Fixpoint get_ICNF (c:ICNF) (i:nat) : Clause :=
  match c with
  | nil => true_C
  | c'::cs => let (j,cl) := c' in if (eq_nat_dec i j) then cl else (get_ICNF cs i)
  end.
*)

Lemma get_ICNF_in_or_default : forall c i,
  {CNF_in (get_ICNF c i) (ICNF_to_CNF c)} + {get_ICNF c i = true_SC}.
induction c; intro i; auto.
induction a0; unfold get_ICNF; simpl; elim BinNat.N.eqb; auto.

set (eqC := eq_Clause_compare).
set (Ceq := Clause_compare_eq).

unfold get_ICNF; induction i.
simpl.
elim (IHc1 BinNums.N0); auto.
left; apply BT_add_all_in; auto.

induction p; intros; simpl.
elim (IHc2 (BinNums.Npos p)); auto.
left; apply BT_add_all_mon; auto.

elim (IHc1 (BinNums.Npos p)); auto.
left; apply BT_add_all_in; auto.

elim (IHc2 (BinNums.N0)); auto.
left; apply BT_add_all_mon; auto.
Qed.

Definition del_ICNF i (c:ICNF) : ICNF :=
  MapRemove _ c i.

(*
Fixpoint del_ICNF (i:nat) (c:ICNF) : ICNF :=
  match c with
  | nil => nil
  | c'::cs => let (j,cl) := c' in if (eq_nat_dec i j) then cs else c'::(del_ICNF i cs)
  end.
*)

Lemma ICNF_get_del : forall T c (cl:T) i j,
  MapGet _ (MapRemove _ c j) i = Some cl -> MapGet _ c i = Some cl.
induction c; intros cl i j; auto.

simpl.
set (Haj := BinNat.N.eqb a j); assert (Haj = BinNat.N.eqb a j); auto; clearbody Haj.
set (Hai := BinNat.N.eqb a i); assert (Hai = BinNat.N.eqb a i); auto; clearbody Hai.
revert H H0.
elim Haj; elim Hai; simpl; auto; intros.
inversion H1.
rewrite <- H0 in H1; auto.
rewrite <- H0 in H1; auto.

simpl.
elim BinNat.N.odd; rewrite makeM2_M2;
simpl; induction i; auto.
induction p; auto.
apply IHc2.
apply IHc2.
apply IHc1.
induction p; auto.
apply IHc1.
Qed.

Lemma MapRemove_in : forall c (cl:Clause) j,
  CNF_in cl (ICNF_to_CNF (MapRemove _ c j)) -> CNF_in cl (ICNF_to_CNF c).
intros.
elim in_ICNF_get' with (MapRemove _ c j) cl; auto.
intros i Hi; inversion_clear Hi; inversion_clear H0; inversion_clear H1.
generalize (ICNF_get_in _ _ _ _ H0); intro.
rewrite H2.
apply ICNF_get_in with i x0.
apply ICNF_get_del with j; auto.
Qed.

Lemma del_ICNF_in : forall (i:ad) (c:ICNF) (cl:Clause),
  CNF_in cl ((del_ICNF i c):CNF) -> CNF_in cl (c:CNF).
induction c; auto.
induction a0; intros; simpl.
revert H; simpl.
induction a; elim BinNat.N.eqb; simpl; auto.
intros.
apply MapRemove_in with i; auto.
Qed.

(*
Lemma makeM2_wf : forall (c c':ICNF), CNF_wf (c':CNF) -> CNF_wf (ICNF_to_CNF (makeM2 Clause c c')).
set (Ceq := Clause_compare_eq).
set (eqC := eq_Clause_compare).
set (Csym1 := Clause_compare_sym_Gt).
set (Csym2 := Clause_compare_sym_Lt).
unfold CNF_wf; induction c; simpl; induction c'; simpl; auto; intros.
repeat split; auto; intros; inversion H0.
set (Z := Clause_compare a0 a2); assert (Z = Clause_compare a0 a2); auto; clearbody Z.
induction Z; simpl; auto.
repeat split; intros; try inversion H1; try inversion H2; try inversion H3; auto.
repeat split; intros; try inversion H1; try inversion H2; try inversion H3; auto.
apply BT_wf_add; auto.
apply BT_wf_add_all; auto.
apply BT_wf_add_all; auto.
apply BT_wf_add_all; auto.
Qed.

Lemma CNF_wf_M2_rev : forall (c c':ICNF), CNF_wf (((M2 Clause c c'):ICNF):CNF) -> CNF_wf (c':CNF).
unfold CNF_wf; induction c'; simpl; auto.
repeat split; intros; inversion H0.
intros.
set (Ceq := Clause_compare_eq).
set (eqC := eq_Clause_compare).
set (Csym1 := Clause_compare_sym_Gt).
set (Csym2 := Clause_compare_sym_Lt).
apply BT_wf_add_all; auto.
apply BT_add_all_wf_rev with (ICNF_to_CNF (c'1:ICNF)); auto.
apply BT_add_all_wf_rev with (c:CNF); auto.
Qed.

Lemma del_ICNF_wf : forall (i:ad) (c:ICNF), CNF_wf (c:CNF) -> CNF_wf (del_ICNF i c:CNF).
intros i c; revert i.
induction c; intros; simpl; auto.
elim BinNat.N.eqb; simpl; auto.
red; simpl; auto.

red in H.
elim BinNat.N.odd; simpl; apply makeM2_wf; auto.
apply IHc2; apply CNF_wf_M2_rev with c1; auto.
apply CNF_wf_M2_rev with c1; auto.
Qed.
*)

Definition add_ICNF i (cl:SetClause) Hcl (c:ICNF) :=
  MapPut _ c i (exist _ cl Hcl).

(*
Definition add_ICNF (i:nat) (cl:Clause) (c:ICNF) := ((i,cl) :: c) : ICNF.
*)

Lemma MapPut1_in : forall p i j (ci cj:SetClause) (cl:Clause) Hci Hcj,
  CNF_in cl (ICNF_to_CNF (MapPut1 _ i (exist _ ci Hci) j (exist _ cj Hcj) p)) -> cl = ci \/ cl = cj.
induction p; simpl; auto; intros i j ci cj cl;
elim BinNat.N.odd; simpl; auto.
(* 1/6 *)
do 2 intro.
change (CNF_in cl (BT_add Clause_compare cj (node (SetClause_to_Clause ci) nought nought)) -> cl = ci \/ cl = cj).
intro.
elim (BT_in_add _ _ _ _ _ H); auto.
intro; simpl in H0.
inversion_clear H0; inversion H1; auto.
inversion H0.
(* 2/6 *)
do 2 intro.
change (CNF_in cl (BT_add Clause_compare ci (node (SetClause_to_Clause cj) nought nought)) -> cl = ci \/ cl = cj).
intro.
elim (BT_in_add _ _ _ _ _ H); auto.
intro; simpl in H0.
inversion_clear H0; inversion H1; auto.
inversion H0.
(* 3/6 *)
intros.
eapply IHp; auto.
apply H.
(* 4/6 *)
intros.
elim (BT_in_add_all _ _ _ _ _ H).
apply IHp; auto.
intro; inversion H0.
(* 5/6 *)
do 2 intro.
change (CNF_in cl (BT_add Clause_compare cj (node (SetClause_to_Clause ci) nought nought)) -> cl = ci \/ cl = cj).
intro.
elim (BT_in_add _ _ _ _ _ H); auto.
intro; simpl in H0.
inversion_clear H0; inversion H1; auto.
inversion H0.
(* 6/6 *)
do 2 intro.
change (CNF_in cl (BT_add Clause_compare ci (node (SetClause_to_Clause cj) nought nought)) -> cl = ci \/ cl = cj).
intro.
intros.
elim (BT_in_add _ _ _ _ _ H); auto.
intro; simpl in H0.
inversion_clear H0; inversion H1; auto.
inversion H0.
Qed.

Lemma MapPut_in : forall c (cl:Clause) (cl':SetClause) Hcl' j,
  CNF_in cl (ICNF_to_CNF (MapPut _ c j (exist _ cl' Hcl'))) -> cl = cl' \/ CNF_in cl (ICNF_to_CNF c).
induction c; simpl; intros.
inversion_clear H; auto.
revert H; elim BinNat.N.lxor; simpl; intros.
inversion_clear H; inversion_clear H0; inversion H; auto.
induction a0.
elim (MapPut1_in _ _ _ _ _ _ _ _ H); auto.
right; right; left; auto.

set (eqC := eq_Clause_compare).
set (Ceq := Clause_compare_eq).

revert H; induction j; auto.
simpl; intro.
elim (BT_in_add_all _ _ _ _ _ H); intros.
elim (IHc1 _ _ _ _ H0); intros; auto.
right; apply BT_add_all_in; auto.
right; apply BT_add_all_mon; auto.

case p; simpl; intros; auto.
elim (BT_in_add_all _ _ _ _ _ H); clear H; intros.
right; apply BT_add_all_in; auto.
elim (IHc2 _ _  _ _ H); intros; auto.
right; apply BT_add_all_mon; auto.
elim (BT_in_add_all _ _ _ _ _ H); clear H; intros.
elim (IHc1 _ _  _ _ H); intros; auto.
right; apply BT_add_all_in; auto.
right; apply BT_add_all_mon; auto.
elim (BT_in_add_all _ _ _ _ _ H); clear H; intros.
right; apply BT_add_all_in; auto.
elim (IHc2 _ _ _ _ H); intros; auto.
right; apply BT_add_all_mon; auto.
Qed.

Lemma add_ICNF_unsat : forall i (cl:SetClause) Hcl, forall c:ICNF,
  unsat ((add_ICNF i cl Hcl c):ICNF) -> entails c cl -> unsat c.
intros; intro; intro.
apply H with v.
unfold add_ICNF.
apply forall_satisfies; intros.
elim (MapPut_in c _ cl _ _ H2); intros.
rewrite H3; auto.
apply satisfies_forall with (ICNF_to_CNF c); auto.
Qed.

End ICNF.

Section Propagation.

Fixpoint propagate (cs: ICNF) (c: SetClause) (is:list ad) : bool := 
  match is with
  | nil => false
  | (i::is) => match SetClause_eq_nil_cons (SC_diff (get_ICNF cs i) c) with
    | inright _ => true
    | inleft H => let (l,Hl) := H in let (c',Hc) := Hl in
                  match SetClause_eq_nil_cons c' with
                  | inleft _ => false
                  | inright _ => let (c'',_) := Hc in
                                 match SetClause_eq_nil_cons c'' with
                                 | inleft _ => false
                                 | inright _ => propagate cs (SC_add (negate l) c) is
  end end end end.

Lemma propagate_sound : forall is cs c, propagate cs c is = true -> entails cs c.
induction is; simpl; intros.
inversion H.
revert H.
rename a into i.
elim SetClause_eq_nil_cons; intros.
induction a; induction p; induction p.
revert H; elim SetClause_eq_nil_cons; intros.
inversion H.
rename x into l.
rewrite b in p; clear b x0.
revert H; elim SetClause_eq_nil_cons; intros.
inversion H.
rewrite b in p; clear b x1.
elim (get_ICNF_in_or_default cs i); intro.
apply propagate_entails with (get_ICNF cs i); auto; apply propagate_singleton with l; auto.

apply propagate_true; apply propagate_singleton with l; auto.
rewrite b in p; auto.

elim (get_ICNF_in_or_default cs i); intro.
apply propagate_entails with (get_ICNF cs i); auto; apply propagate_empty; auto.
apply propagate_true; apply propagate_empty; auto.
rewrite b0 in b; auto.
Qed.

End Propagation.

Section Refutation.

Inductive Action : Type :=
  | D : list ad -> Action
  | O : ad -> Clause -> Action
  | R : ad -> Clause -> list ad -> Action.

Definition LazyT := id (A:=Type).

Inductive lazy_list (A:Type) :=
    lnil : lazy_list A
  | lcons : A -> LazyT (lazy_list A) -> lazy_list A.

Definition Oracle := LazyT (lazy_list Action).

Arguments lazy_list [A].
Arguments lcons [A] _ _.

Fixpoint Oracle_size (O:Oracle) : nat :=
  match O with
  | lnil => 0
  | lcons (D is) O' => length is + 1 + Oracle_size O'
  | lcons _ O' => 1 + Oracle_size O'
  end.

Definition Answer := bool.

Definition force := id (A := Oracle).
Definition fromVal := id (A := Oracle).

Function refute_work (w:ICNF) (c:CNF) (Hc:CNF_wf c) (O:Oracle)
  {measure Oracle_size O} : Answer :=
  match (force O) with
  | lnil => false
  | lcons (D nil) O' => refute_work w c Hc O'
  | lcons (D (i::is)) O' => refute_work (del_ICNF i w) c Hc (fromVal (lcons (D is) O'))
  | lcons (O i cl) O' => if (BT_in_dec _ _ eq_Clause_compare Clause_compare_eq cl c Hc) then (refute_work (add_ICNF i _ (C_to_SC_wf cl) w) c Hc O') else false
  | lcons (R i nil is) O' => propagate w SC_empty is
  | lcons (R i cl is) O' => andb (propagate w (Clause_to_SetClause cl) is) (refute_work (add_ICNF i _ (C_to_SC_wf cl) w) c Hc O')
  end.
unfold force, id; simpl; intros; rewrite teq; auto with arith.
unfold force, id; simpl; intros; rewrite teq; auto with arith.
unfold force, id; simpl; intros; rewrite teq; auto with arith.
unfold force, id; simpl; intros; rewrite teq; auto with arith.
Defined.

Lemma refute_work_correct : forall w c Hc O, refute_work w c Hc O = true -> unsat (CNF_join c (w:CNF)).
set (eqC := eq_Clause_compare).
set (Ceq := Clause_compare_eq).
intros w c Hc O; functional induction (refute_work w c Hc O); intros; auto.
(* 1/6 *)
inversion H.
(* 2/6 *)
apply unsat_subset with (CNF_join c ((del_ICNF i w) : CNF)); auto.
intros.
elim (BT_in_add_all Clause _ _ _ _ H0); intro.
apply BT_add_all_in; auto.
apply BT_add_all_mon; auto.
eapply del_ICNF_in; eauto.
(* 3/6 *)
intro; intro; apply IHa with v; auto.
apply forall_satisfies; intros.
elim (BT_in_add_all _ _ _ _ _ H1); intros; auto.
apply satisfies_forall with (CNF_join c (w:CNF)); auto.
apply BT_add_all_in; auto.
elim (MapPut_in _ _ _ _ _ H2); intros.
rewrite H3.
apply C_to_C_satisfies_1.
apply satisfies_forall with (CNF_join c (w:CNF)); auto.
apply BT_add_all_in; auto.
apply satisfies_forall with (CNF_join c (w:CNF)); auto.
apply BT_add_all_mon; auto.
(* 4/6 *)
inversion H.
(* 5/6 *)
apply unsat_subset with (w:CNF).
intros; apply BT_add_all_mon; auto.
apply CNF_empty.
replace (nil:Clause) with (SetClause_to_Clause nought); auto.
apply propagate_sound with is; auto.
(* 6/6 *)
elim (andb_true_eq _ _ (eq_sym H)); clear H; intros.
intro; intro; apply IHa with v; auto.
apply forall_satisfies; intros.
simpl in H2.
elim (BT_in_add_all _ _ _ _ _ H2); intros; auto.
apply satisfies_forall with (CNF_join c (w:CNF)); auto.
apply BT_add_all_in; auto.
elim (MapPut_in _ _ _ _ _ H3); intros.
rewrite H4.
apply C_to_C_satisfies_1.
generalize (propagate_sound _ _ _ (eq_sym H)); intro.
apply C_to_C_satisfies_2; apply H5.
apply forall_satisfies; intros.
apply satisfies_forall with (CNF_join c (w:CNF)); auto.
apply BT_add_all_mon; auto.
apply satisfies_forall with (CNF_join c (w:CNF)); auto.
apply BT_add_all_mon; auto.
Qed.

Fixpoint make_CNF (l:list Clause) : CNF :=
  match l with
  | nil => CNF_empty_constant
  | cl :: l' => CNF_add cl (make_CNF l')
  end.

Lemma make_CNF_wf : forall l, CNF_wf (make_CNF l).
induction l; red; simpl; auto.
apply BT_wf_add; auto.
exact eq_Clause_compare.
exact Clause_compare_eq.
exact Clause_compare_trans.
exact Clause_compare_sym_Gt.
exact Clause_compare_sym_Lt.
Qed.

Definition refute (c:list Clause) (O:Oracle) : Answer :=
  refute_work empty_ICNF (make_CNF c) (make_CNF_wf c) O.

Theorem refute_correct : forall c O, refute c O = true -> unsat (make_CNF c).
intros c O; intros; red; intros; intro.
elim (refute_work_correct empty_ICNF (make_CNF c) (make_CNF_wf c) O) with v; auto.
apply forall_satisfies; intros; auto.
apply satisfies_forall with (make_CNF c); auto.
elim (BT_in_add_all _ _ _ _ _ H1); auto.
intro; inversion H2.
Qed.

End Refutation.
