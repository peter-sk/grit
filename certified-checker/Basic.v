Require Export List.
Require Export Arith.
Require Export ZArith.

Section Compare.

Lemma compare_Lt_dec : forall C, {C = Lt} + {C <> Lt}.
induction C; auto; right; discriminate.
Qed.

Lemma compare_Gt_dec : forall C, {C = Gt} + {C <> Gt}.
induction C; auto; right; discriminate.
Qed.

Lemma compare_Eq_dec : forall C, {C = Eq} + {C <> Eq}.
induction C; auto; right; discriminate.
Qed.

End Compare.

Section NatCompare.

Lemma nat_compare_eq_rev : forall n, nat_compare n n = Eq.
intro; elim (nat_compare_eq_iff n n); auto.
Qed.

Lemma nat_compare_sym_lt : forall m n, nat_compare m n = Lt -> nat_compare n m = Gt.
double induction n m; simpl; auto.
intro; discriminate H.
Qed.

Lemma nat_compare_sym_gt : forall m n, nat_compare m n = Gt -> nat_compare n m = Lt.
double induction n m; simpl; auto.
intro; discriminate H.
Qed.

Lemma nat_compare_trans : forall m n o, nat_compare m n = Lt -> nat_compare n o = Lt ->
                                        nat_compare m o = Lt.
intros.
elim (nat_compare_lt m n); intros.
elim (nat_compare_lt m o); intros.
elim (nat_compare_lt n o); intros.
apply H3; transitivity n; auto.
Qed.

End NatCompare.

Section Z_stuff.

Open Scope Z_scope.

Lemma Zabs_le_1 : forall z, Z.abs z <= 1 ->
  {z = 0} + {z = 1} + {z = -1}.
intro; case z; auto; intro; case p; simpl; clear p; intros; auto;
compute in H; elim H; auto.
Qed. 
Lemma Zabs_diff_le_1 : forall z z', Z.abs (z - z') <= 1 ->
  {z = z'} + {z = z' + 1} + {z' = z + 1}.
intros z z' H; elim (Zabs_le_1 _ H); intros.
inversion_clear a; auto.
left; left; omega.
left; right; omega.
right; omega.
Qed.

End Z_stuff.

Section RemoveAll.

Variable A:Type.
Variable A_dec : forall x y : A, {x = y} + {x <> y}.

Lemma in_remove : forall l x y, In x l -> x <> y -> In x (remove A_dec y l).
induction l; simpl; intros; auto.
elim A_dec; simpl; intro; inversion_clear H; auto.
exfalso; apply H0; rewrite a0; auto.
Qed.

Fixpoint remove_all (l w:list A) :=
  match l with
  | nil => w
  | x :: l' => remove_all l' (remove A_dec x w)
  end.

Lemma remove_all_orig : forall l w x,
  In x w -> In x l \/ In x (remove_all l w).
induction l; simpl; auto.
intros.
elim (A_dec a x); auto.
intro; elim IHl with (remove A_dec a w) x; auto.
apply in_remove; auto.
Qed.

End RemoveAll.

Arguments remove_all : default implicits.

Definition list_subset (A:Type) (l1 l2:list A) := forall x, In x l1 -> In x l2.
