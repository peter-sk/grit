Require Export Basic.

Section Trees.

Variable T : Type.

(** * Binary trees of type T *)

Inductive BinaryTree : Type :=
  nought : BinaryTree
  | node : T -> BinaryTree -> BinaryTree -> BinaryTree.

(** We are interested in search trees - well-founded binary trees *)

Fixpoint BT_In (t:T) (Tree:BinaryTree) : Prop :=
  match Tree with
  | nought => False
  | node t' L R => BT_In t L \/ t = t' \/ BT_In t R
  end.

Fixpoint BT_wf (T_compare : T -> T -> comparison) (Tree:BinaryTree) :=
  match Tree with
  | nought => True
  | node t L R => BT_wf T_compare L /\ BT_wf T_compare R /\
                 (forall t', BT_In t' L -> T_compare t' t = Lt) /\
                 (forall t', BT_In t' R -> T_compare t' t = Gt)
  end.

Variable T_compare : T -> T -> comparison.

Hypothesis eq_T_compare : forall t t', T_compare t t' = Eq -> t = t'.
Hypothesis T_compare_eq : forall t, T_compare t t = Eq.
Hypothesis T_compare_trans : forall t t' t'', T_compare t t' = Lt -> T_compare t' t'' = Lt ->
                                              T_compare t t'' = Lt.
Hypothesis T_compare_sym_Gt : forall t t', T_compare t t' = Gt -> T_compare t' t = Lt.
Hypothesis T_compare_sym_Lt : forall t t', T_compare t t' = Lt -> T_compare t' t = Gt.

Let BT_Wf := BT_wf T_compare.

Section Balancing.

Open Scope Z_scope.

Fixpoint height (Tree:BinaryTree) : Z :=
  match Tree with
  | nought => 0
  | node _ L R => 1 + (Z.max (height L) (height R))
  end.

Fixpoint balanced (Tree:BinaryTree) :=
  match Tree with
  | nought => True
  | node _ L R => balanced L /\ balanced R /\ Z.abs (height L - height R) <= 1
  end.

Definition BT_rot_L (Tree:BinaryTree) :=
  match Tree with
  | nought => nought
  | node n L nought => node n L nought
  | node n L (node n' RL RR) => node n' (node n L RL) RR
  end.

Lemma BT_rot_L_wf : forall Tree, BT_Wf Tree -> BT_Wf (BT_rot_L Tree).
intro Tree; case Tree; auto.
intros n L R; simpl.
case R; auto.
intros n' RL RR; simpl; intros.
inversion_clear H; inversion_clear H1; inversion_clear H2.
inversion_clear H; inversion_clear H4; inversion_clear H5.
repeat split; auto.
intros; apply H3; left; auto.
intros; inversion_clear H5; auto.
apply T_compare_trans with n; auto.
apply T_compare_sym_Gt; apply H3; right; auto.
inversion_clear H7; auto.
rewrite H5; apply T_compare_sym_Gt; apply H3; right; auto.
Qed.

Lemma BT_rot_L_in : forall t Tree, BT_In t Tree -> BT_In t (BT_rot_L Tree).
intros t Tree; case Tree; auto.
intros n L R; case R; auto.
intros n' RL RR H; simpl.
inversion_clear H; auto.
inversion_clear H0; auto.
inversion_clear H; auto.
Qed.

Lemma BT_in_rot_L : forall t Tree, BT_In t (BT_rot_L Tree) -> BT_In t Tree.
intros t Tree; case Tree; auto.
intros n L R; case R; auto.
intros n' RL RR H; simpl.
inversion_clear H; auto.
inversion_clear H0; auto.
inversion_clear H; auto.
Qed.

Lemma BT_rot_L_wf_rev : forall Tree, BT_Wf (BT_rot_L Tree) -> BT_Wf Tree.
intro Tree; case Tree; auto.
intros n L R; case R; auto.
intros n' RL RR; simpl; intros.
inversion_clear H; inversion_clear H1; inversion_clear H2.
inversion_clear H0; inversion_clear H4; inversion_clear H5.
repeat split; auto.
intros; apply H1; right; auto.
intros; inversion_clear H5; auto.
inversion_clear H7; auto.
rewrite H5; apply T_compare_sym_Lt; apply H1; right; auto.
apply T_compare_sym_Lt; apply T_compare_trans with n'; auto.
apply H1; right; auto.
Qed.

Definition BT_rot_R (Tree:BinaryTree) :=
  match Tree with
  | nought => nought
  | node n nought R => node n nought R
  | node n (node n' LL LR) R => node n' LL (node n LR R)
  end.

Lemma BT_rot_R_wf : forall Tree, BT_Wf Tree -> BT_Wf (BT_rot_R Tree).
intro Tree; case Tree; auto.
intros n L R; simpl.
case L; auto.
intros n' LL LR; simpl; intros.
inversion_clear H; inversion_clear H1; inversion_clear H2.
inversion_clear H0; inversion_clear H4; inversion_clear H5.
repeat split; auto.
intros; apply H1; right; auto.
intros; inversion_clear H5; auto.
inversion_clear H7; auto.
rewrite H5; apply T_compare_sym_Lt; apply H1; right; auto.
apply T_compare_sym_Lt; apply T_compare_trans with n; auto.
apply H1; right; auto.
Qed.

Lemma BT_rot_R_in : forall t Tree, BT_In t Tree -> BT_In t (BT_rot_R Tree).
intros t Tree; case Tree; auto.
intros n L R; case L; auto.
intros n' LL LR H; simpl.
inversion_clear H; auto.
inversion_clear H0; auto.
inversion_clear H; auto.
Qed.

Lemma BT_in_rot_R : forall t Tree, BT_In t (BT_rot_R Tree) -> BT_In t Tree.
intros t Tree; case Tree; auto.
intros n L R; case L; auto.
intros n' LL LR H; simpl.
inversion_clear H; auto.
inversion_clear H0; auto.
inversion_clear H; auto.
Qed.

Lemma BT_rot_R_wf_rev : forall Tree, BT_Wf (BT_rot_R Tree) -> BT_Wf Tree.
intro Tree; case Tree; auto.
intros n L R; case L; auto.
intros n' LL LR; simpl; intros.
inversion_clear H; inversion_clear H1; inversion_clear H2.
inversion_clear H; inversion_clear H4; inversion_clear H5.
repeat split; auto.
intros; apply H3; left; auto.
intros; inversion_clear H5; auto.
apply T_compare_trans with n'; auto.
apply T_compare_sym_Gt; apply H3; right; auto.
inversion_clear H7; auto.
rewrite H5; apply T_compare_sym_Gt; apply H3; right; auto.
Qed.

Definition BT_rot_LL (Tree:BinaryTree) :=
  match Tree with
  | nought => nought
  | node n L R => BT_rot_L (node n L (BT_rot_R R))
  end.

Lemma BT_rot_LL_wf : forall Tree, BT_Wf Tree -> BT_Wf (BT_rot_LL Tree).
intro Tree; case Tree; auto.
unfold BT_rot_LL; intros; apply BT_rot_L_wf.
inversion_clear H; inversion_clear H1; inversion_clear H2.
repeat split; auto.
apply BT_rot_R_wf; auto.
intros; apply H3; apply BT_in_rot_R; auto.
Qed.

Lemma BT_rot_LL_in : forall t Tree, BT_In t Tree -> BT_In t (BT_rot_LL Tree).
intros t Tree; case Tree; auto.
unfold BT_rot_LL; intros; apply BT_rot_L_in; simpl.
inversion_clear H; auto.
inversion_clear H0; auto.
right; right; apply BT_rot_R_in; auto.
Qed.

Lemma BT_in_rot_LL : forall t Tree, BT_In t (BT_rot_LL Tree) -> BT_In t Tree.
intros t Tree; case Tree; auto.
unfold BT_rot_LL; intros.
generalize (BT_in_rot_L _ _ H); intro; simpl.
inversion_clear H0; auto.
inversion_clear H1; auto.
right; right; apply BT_in_rot_R; auto.
Qed.

(** stuff to do here **)

Definition BT_rot_RR (Tree:BinaryTree) :=
  match Tree with
  | nought => nought
  | node n L R => BT_rot_R (node n (BT_rot_L L) R)
  end.

Lemma BT_rot_RR_wf : forall Tree, BT_Wf Tree -> BT_Wf (BT_rot_RR Tree).
intro Tree; case Tree; auto.
unfold BT_rot_RR; intros; apply BT_rot_R_wf.
inversion_clear H; inversion_clear H1; inversion_clear H2.
repeat split; auto.
apply BT_rot_L_wf; auto.
intros; apply H1; apply BT_in_rot_L; auto.
Qed.

Lemma BT_rot_RR_in : forall t Tree, BT_In t Tree -> BT_In t (BT_rot_RR Tree).
intros t Tree; case Tree; auto.
unfold BT_rot_RR; intros; apply BT_rot_R_in; simpl.
inversion_clear H; auto.
left; apply BT_rot_L_in; auto.
Qed.

Lemma BT_in_rot_RR : forall t Tree, BT_In t (BT_rot_RR Tree) -> BT_In t Tree.
intros t Tree; case Tree; auto.
unfold BT_rot_RR; intros.
generalize (BT_in_rot_R _ _ H); intro; simpl.
inversion_clear H0; auto.
left; apply BT_in_rot_L; auto.
Qed.

(** stuff to do here **)

Definition BT_balance (Tree:BinaryTree) :=
  match Tree with
  | nought => nought
  | node n L R => if (Z.eq_dec ((height L)-(height R)) 2)
                  then match L with
                       | nought => node n L R (* absurd case *)
                       | node n' LL LR => if (compare_Gt_dec (Z.compare (height LL) (height LR)))
                                          then BT_rot_R Tree
                                          else BT_rot_RR Tree
                       end
                  else if (Z.eq_dec ((height R)-(height L)) 2)
                  then match R with
                       | nought => node n L R (* absurd case *)
                       | node n' RL RR => if (compare_Lt_dec (Z.compare (height RL) (height RR)))
                                          then BT_rot_L Tree
                                          else BT_rot_LL Tree
                       end
                  else Tree
  end.

Lemma BT_balance_wf : forall Tree, BT_Wf Tree -> BT_Wf (BT_balance Tree).
intro Tree; case Tree; auto.
intros n L R; unfold BT_balance; elim Z.eq_dec.
elim L; auto.
intros n' LL H_LL LR H_LR.
elim compare_Gt_dec; intros.
apply BT_rot_R_wf; auto.
apply BT_rot_RR_wf; auto.
elim Z.eq_dec; auto.
elim R; auto.
intros n' RL H_RL RR H_RR.
elim compare_Lt_dec; intros.
apply BT_rot_L_wf; auto.
apply BT_rot_LL_wf; auto.
Qed.

Lemma BT_balance_in : forall t Tree, BT_In t Tree -> BT_In t (BT_balance Tree).
intros t Tree; case Tree; auto.
intros n L R; unfold BT_balance; elim Z.eq_dec.
elim L; auto.
intros n' LL H_LL LR H_LR.
elim compare_Gt_dec; intros.
apply BT_rot_R_in; auto.
apply BT_rot_RR_in; auto.
elim Z.eq_dec; auto.
elim R; auto.
intros n' RL H_RL RR H_RR.
elim compare_Lt_dec; intros.
apply BT_rot_L_in; auto.
apply BT_rot_LL_in; auto.
Qed.

Lemma BT_in_balance : forall t Tree, BT_In t (BT_balance Tree) -> BT_In t Tree.
intros t Tree; case Tree; auto.
intros n L R; unfold BT_balance; elim Z.eq_dec.
elim L; auto.
intros n' LL H_LL LR H_LR.
elim compare_Gt_dec; intros.
apply BT_in_rot_R; auto.
apply BT_in_rot_RR; auto.
elim Z.eq_dec; auto.
elim R; auto.
intros n' RL H_RL RR H_RR.
elim compare_Lt_dec; intros.
apply BT_in_rot_L; auto.
apply BT_in_rot_LL; auto.
Qed.

(** stuff to do here **)

End Balancing.

Opaque BT_balance.

(** ** Adding one element to a search tree *)

Fixpoint BT_add (t:T) (Tree:BinaryTree) :=
  match Tree with
  | nought => node t nought nought
  | node t' L R => match T_compare t t' with
         | Lt => BT_balance (node t' (BT_add t L) R)
         | Gt => BT_balance (node t' L (BT_add t R))
         | Eq => Tree
         end
  end.

Lemma BT_add_in : forall t Tree, BT_In t (BT_add t Tree).
induction Tree; simpl; auto.
set (Z := T_compare t t0).
assert (Z = T_compare t t0); auto; clearbody Z.
induction Z.
rewrite (eq_T_compare _ _ (eq_sym H)); right; auto.
apply BT_balance_in; left; auto.
apply BT_balance_in; right; auto.
Qed.

Lemma BT_in_add : forall t t' Tree, BT_In t (BT_add t' Tree) ->
                  BT_In t Tree \/ t=t'.
induction Tree.
simpl; intros.
repeat (elim H; clear H; intro H); auto.
intro H; simpl in H; revert H.
set (Z := T_compare t' t0).
assert (Z = T_compare t' t0); auto; clearbody Z.
induction Z; auto.
simpl; intro.
elim (BT_in_balance _ _ H0); clear H0; intro H0; auto.
elim (IHTree1 H0); auto.
simpl; intro.
elim (BT_in_balance _ _ H0); clear H0; intro H0; auto.
repeat (elim H0; clear H0; intro H0); auto.
elim (IHTree2 H0); auto.
Qed.

Lemma BT_wf_add : forall t Tree, BT_Wf Tree -> BT_Wf (BT_add t Tree).
unfold BT_Wf; induction Tree.
repeat split; simpl.
intros; inversion H0.
intros; inversion H0.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
simpl.
set (Z := T_compare t t0).
assert (Z = T_compare t t0); auto; clearbody Z.
induction Z; repeat split; auto; apply BT_balance_wf; repeat split; auto.
intros.
elim (BT_in_add _ _ _ H4); auto.
intro; rewrite H5; auto.
intros.
elim (BT_in_add _ _ _ H4); auto.
intro; rewrite H5; auto.
Qed.

Lemma BT_add_mon : forall t t' Tree, BT_In t' Tree -> BT_In t' (BT_add t Tree).
induction Tree.
intro; inversion H.
intro H; simpl in H; revert H.
set (Z := T_compare t' t0).
assert (Z = T_compare t' t0); auto; clearbody Z.
induction Z; auto.
intro; simpl; elim T_compare; try apply BT_balance_in; simpl; auto.
simpl; elim T_compare; auto; intro H0; try apply BT_balance_in; repeat (elim H0; clear H0; intro H0); intros; simpl; auto.
simpl; elim T_compare; auto; intro H0; try apply BT_balance_in; repeat (elim H0; clear H0; intro H0); intros; simpl; auto.
Qed.

(*
Lemma BT_add_wf_rev : forall t Tree, BT_Wf (BT_add t Tree) -> BT_Wf Tree.
unfold BT_Wf.
intros t Tree; revert t.
induction Tree; repeat split; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; auto.
apply IHTree1 with t'; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; inversion_clear H2; auto.
apply IHTree2 with t'; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; inversion_clear H3; inversion_clear H4; auto.
apply H3; auto.
apply BT_add_mon; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; inversion_clear H3; inversion_clear H4; auto.
apply H5; auto.
apply BT_add_mon; auto.
Qed.

*)

(** old stuff from here *)


(*
(** ** Adding one element to a search tree *)

Fixpoint BT_add (t:T) (Tree:BinaryTree) :=
  match Tree with
  | nought => node t nought nought
  | node t' L R => match T_compare t t' with
         | Lt => node t' (BT_add t L) R
         | Gt => node t' L (BT_add t R)
         | Eq => Tree
         end
  end.

Lemma BT_add_in : forall t Tree, BT_In t (BT_add t Tree).
induction Tree; simpl; auto.
set (Z := T_compare t t0).
assert (Z = T_compare t t0); auto; clearbody Z.
induction Z; simpl; auto.
Qed.

Lemma BT_in_add : forall t t' Tree, BT_In t (BT_add t' Tree) ->
                  BT_In t Tree \/ t=t'.
induction Tree.
simpl; intros.
repeat (elim H; clear H; intro H); auto.
intro H; simpl in H; revert H.
set (Z := T_compare t' t0).
assert (Z = T_compare t' t0); auto; clearbody Z.
induction Z; auto.
simpl; intro.
repeat (elim H0; clear H0; intro H0); auto.
elim (IHTree1 H0); auto.
simpl; intro.
repeat (elim H0; clear H0; intro H0); auto.
elim (IHTree2 H0); auto.
Qed.

Lemma BT_wf_add : forall t Tree, BT_Wf Tree -> BT_Wf (BT_add t Tree).
unfold BT_Wf; induction Tree.
repeat split; simpl.
intros; inversion H0.
intros; inversion H0.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
simpl.
set (Z := T_compare t t0).
assert (Z = T_compare t t0); auto; clearbody Z.
induction Z; repeat split; auto.
intros.
elim (BT_in_add _ _ _ H4); auto.
intro; rewrite H5; auto.
intros.
elim (BT_in_add _ _ _ H4); auto.
intro; rewrite H5; auto.
Qed.

Lemma BT_add_mon : forall t t' Tree, BT_In t' Tree -> BT_In t' (BT_add t Tree).
induction Tree.
intro; inversion H.
intro H; simpl in H; revert H.
set (Z := T_compare t' t0).
assert (Z = T_compare t' t0); auto; clearbody Z.
induction Z; auto.
simpl; elim T_compare; simpl; auto.
simpl; elim T_compare; auto; repeat (intro H0; elim H0; clear H0); intros; simpl; auto.
simpl; elim T_compare; auto; repeat (intro H0; elim H0; clear H0); intros; simpl; auto.
Qed.

Lemma BT_add_wf_rev : forall t Tree, BT_Wf (BT_add t Tree) -> BT_Wf Tree.
unfold BT_Wf.
intros t Tree; revert t.
induction Tree; repeat split; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; auto.
apply IHTree1 with t'; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; inversion_clear H2; auto.
apply IHTree2 with t'; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; inversion_clear H3; inversion_clear H4; auto.
apply H3; auto.
apply BT_add_mon; auto.

rename t0 into t'; revert H; simpl.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; intros; inversion_clear H0; inversion_clear H3; inversion_clear H4; auto.
apply H5; auto.
apply BT_add_mon; auto.
Qed.
*)
(** ** Removing the least element from a search tree *)

Fixpoint BT_split (Tree:BinaryTree) (default:T) : T * BinaryTree :=
  match Tree with
  | nought => (default,nought)
  | node t nought R => (t,R)
  | node t L R => let (t',L') := BT_split L default in
                  (t',node t L' R)
  end.

Lemma BT_split_in_r : forall t t' x Tree Tree', BT_split Tree x = (t,Tree') ->
                      BT_In t' Tree' -> BT_In t' Tree.
unfold BT_Wf; induction Tree.
simpl; intros; inversion H.
rewrite <- H3 in H0; auto.
simpl.
destruct Tree1.
elim (T_compare t' t0); intros; inversion H; auto.

revert IHTree1; set (Tree1 := node t1 Tree1_1 Tree1_2).
elim (BT_split Tree1); intro d; intro.
set (Z := T_compare t' t0).
assert (Z = T_compare t' t0); auto; intro.
induction Z; intros; auto.
(* 1 *)
inversion H0; clear H0.
rewrite H3 in IHTree1; clear H3 d.
rewrite <- H4 in H1; simpl in H1.
repeat (elim H1; clear H1; intro H1); auto.
left; apply IHTree1 with b; auto.
(* 2 *)
inversion H0; clear H0.
rewrite H3 in IHTree1; clear H3 d.
rewrite <- H4 in H1; simpl in H1.
repeat (elim H1; clear H1; intro H1); auto.
left; apply IHTree1 with b; auto.
Qed.

Lemma BT_split_wf : forall Tree x, BT_Wf Tree -> forall t Tree', BT_split Tree x = (t,Tree') -> BT_Wf Tree'.
unfold BT_Wf; induction Tree.
intros; inversion H0; auto.
intros x H; elim H; clear H; intros H' H.
elim H; clear H; intros H'' H.
elim H; clear H; intros H''' H''''.
simpl.
destruct Tree1.
intros; inversion H.
rewrite <- H2; auto.
revert IHTree1; set (Tree1 := node t0 Tree1_1 Tree1_2).
assert (BT_split Tree1 x = BT_split (node t0 Tree1_1 Tree1_2) x); auto.
revert H.
elim (BT_split Tree1 x); intros.
inversion H0.
clear H2 H3 H0; repeat split; auto.
apply IHTree1 with x a; auto.
intros; apply H'''.
apply BT_split_in_r with a x b; auto.
Qed.

Lemma BT_split_in_l : forall t x Tree, Tree <> nought ->
                      forall Tree', BT_split Tree x = (t,Tree') -> BT_In t Tree.
unfold BT_Wf; induction Tree; simpl.
intros; elim H; inversion H0; auto.
destruct Tree1.
intros; inversion H0; auto.

revert IHTree1; set (Tree1 := node t1 Tree1_1 Tree1_2).
assert (BT_split Tree1 = BT_split (node t1 Tree1_1 Tree1_2)); auto.
revert H.
elim (BT_split Tree1); intros.
clear H0.
inversion H1; clear H1.
rewrite H2 in IHTree1; clear H2 a.
left; apply IHTree1 with b; auto.
discriminate.
Qed.

Lemma BT_split_in : forall t t' x Tree Tree', BT_split Tree x = (t',Tree') ->
                    BT_In t Tree -> t = t' \/ BT_In t Tree'.
unfold BT_Wf; induction Tree.
intros; inversion H0.
destruct Tree1.
simpl; intros.
inversion H.
repeat (elim H0; clear H0; intro H0); auto.
left; inversion H; transitivity t0; auto.
rewrite <- H3; auto.

revert IHTree1; set (Tree1 := node t1 Tree1_1 Tree1_2).
assert (BT_split Tree1 x = BT_split (node t1 Tree1_1 Tree1_2) x); auto.
revert H.
elim (BT_split Tree1); intros.
simpl in H; simpl in H0; rewrite <- H in H0.
inversion H0; clear H H0.
rewrite H3 in IHTree1; clear a H3.
elim H1; clear H1; intro H1.
elim (IHTree1 b); auto.
right; left; auto.
inversion_clear H1.
rewrite H; right; right; auto.
right; right; auto.
Qed.

Lemma BT_split_compare : forall Tree x, BT_Wf Tree -> forall t Tree', BT_split Tree x = (t,Tree') ->
                         forall t', BT_In t' Tree' -> T_compare t t' = Lt.
unfold BT_Wf; induction Tree.
intros; inversion H0.
rewrite <- H4 in H1; inversion H1.
clear IHTree2.
intros.
inversion_clear H.
inversion_clear H3.
inversion_clear H4.
destruct Tree1.
simpl in H0.
apply T_compare_sym_Gt.
inversion H0.
rewrite <- H6; apply H5.
rewrite H7; auto.

revert H0; set (Tree1 := node t1 Tree1_1 Tree1_2).
assert (BT_split Tree1 x = BT_split (node t1 Tree1_1 Tree1_2) x); auto.
revert H0.
elim (BT_split Tree1); intros.
simpl in H0; simpl in H4; rewrite <- H0 in H4.
inversion H4.
generalize (IHTree1 x); clear IHTree1; intro IHTree1.
simpl in IHTree1; rewrite <- H0 in IHTree1.
rewrite <- H8 in H1.
revert H1; simpl.
set (Z := T_compare t' t).
assert (Z = T_compare t' t); auto; clearbody Z.
induction Z; auto.
intros; rewrite <- H7; rewrite (eq_T_compare _ _ (eq_sym H1)).
apply H3; auto.
change ((a,b) = BT_split Tree1 x) in H0.
apply BT_split_in_l with x b; auto.
discriminate.
intros.
apply IHTree1 with (Tree' := b); auto.
rewrite H7; auto.
repeat (elim H6; clear H6; intro H6); auto.
rewrite H6 in H1; rewrite T_compare_eq in H1; inversion H1.
rewrite (H5 _ H6) in H1; inversion H1.

change ((a,b) = BT_split Tree1 x) in H0.
fold Tree1 in H2, H3.
assert (BT_In a Tree1).
apply BT_split_in_l with x b; auto.
discriminate.
generalize (H3 a H6); intros.
rewrite H7 in H9.
apply T_compare_trans with t; auto.
Qed.

Hypothesis T_dec : forall t t':T, {t=t'} + {t<>t'}.

Lemma BT_in_dec : forall t Tree, BT_Wf Tree -> {BT_In t Tree} + {~BT_In t Tree}.
induction Tree.
right; simpl; auto.
unfold BT_Wf; simpl; intro.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
set (Z := T_compare t t0).
assert (Z = T_compare t t0); auto; clearbody Z.
induction Z; auto.
elim (IHTree1 H0); [left | right]; auto.
intro; apply b.
repeat (elim H4; clear H4; intro H4); auto.
rewrite H4 in H2; rewrite T_compare_eq in H2; auto; inversion H2.
rewrite H3 in H2; auto; inversion H2.
elim (IHTree2 H); [left | right]; auto.
intro; apply b.
repeat (elim H4; clear H4; intro H4); auto.
rewrite H1 in H2; auto; inversion H2.
rewrite H4 in H2; rewrite T_compare_eq in H2; auto; inversion H2.
Qed.

Lemma BT_all_in_dec : forall f:T->T, forall Tree Tree',
     BT_Wf Tree' ->
     {forall t, BT_In t Tree -> BT_In (f t) Tree'} +
     {~forall t, BT_In t Tree -> BT_In (f t) Tree'}.
intros; induction Tree.
left; simpl; intros; inversion H0.
elim (BT_in_dec (f t) Tree'); auto; intro.
elim IHTree1; intro.
elim IHTree2; intro.
left; intros.
repeat (elim H0; clear H0; intro H0); auto.
rewrite H0; auto.
right; intro; apply b; intros.
apply H0; simpl; auto.
right; intro; apply b; intros.
apply H0; simpl; auto.
right; intro; apply b; intros.
apply H0; simpl; auto.
Qed.

(** ** Removing one element from a search tree *)

Fixpoint BT_remove (t:T) (Tree:BinaryTree) : BinaryTree :=
  match Tree with
  | nought => nought
  | node t' L R => match T_compare t t' with
                   | Eq => match R with
                           | nought => L
                           | R => let (min,R') := BT_split R t in node min L R'
                           end
                   | Lt => node t' (BT_remove t L) R
                   | Gt => node t' L (BT_remove t R)
  end end.

Lemma BT_remove_in : forall t t' Tree Tree', BT_remove t Tree = Tree' ->
                     BT_In t' Tree' -> BT_In t' Tree.
unfold BT_Wf; induction Tree.
simpl; intros.
rewrite <- H in H0; auto.

simpl; intro Tree'.
set (Z := T_compare t t0); assert (Z = T_compare t t0); auto; intro.
induction Z; rewrite <- H0; clear H0 Tree'.
(* 1/3 *)
induction Tree2; auto.
clear IHTree2_1 IHTree2_2.
set (Tree2 := node t1 Tree2_1 Tree2_2); fold Tree2 in IHTree2.
set (Z := BT_split Tree2 t); assert (Z = BT_split Tree2 t); auto; intro.
induction Z.
inversion_clear H1; auto.
inversion_clear H2.
right; right; apply BT_split_in_l with t b; auto.
unfold Tree2; discriminate.
rewrite H1; auto.
right; right; apply BT_split_in_r with a t b; auto.
(* 2/3 *)
intro; inversion_clear H0; auto.
left; apply IHTree1 with (BT_remove t Tree1); auto.
(* 3/3 *)
intro; inversion_clear H0; auto.
inversion_clear H1; auto.
right; right; apply IHTree2 with (BT_remove t Tree2); auto.
Qed.

Lemma BT_remove_wf : forall Tree, BT_Wf Tree -> forall t Tree', BT_remove t Tree = Tree' -> BT_Wf Tree'.
unfold BT_Wf; induction Tree.
simpl; intros.
rewrite <- H0; auto.

simpl; intro H.
inversion_clear H; inversion_clear H1; inversion_clear H2.
intros t' Tree'.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; intro.
induction Z; rewrite <- H4; clear H4 Tree'.
(* 1/3 *)
induction Tree2; auto.
clear IHTree2_1 IHTree2_2.
set (Tree2 := node t0 Tree2_1 Tree2_2); fold Tree2 in H3, H, IHTree2.
set (Z := BT_split Tree2 t'); assert (Z = BT_split Tree2 t'); auto.
induction Z; auto.
repeat split; auto.
(* a *)
apply BT_split_wf with Tree2 t' a; auto.
(* b *)
intros; apply T_compare_trans with t; auto.
apply T_compare_sym_Gt; apply H3.
apply BT_split_in_l with t' b; auto.
unfold Tree2; simpl; discriminate.
(* c *)
intros; apply T_compare_sym_Lt; apply BT_split_compare with Tree2 t' b; auto.
(* 2/3 *)
repeat split; auto.
apply IHTree1 with t'; auto.
intros; apply H1; auto.
apply (BT_remove_in _ _ _ _ (eq_refl _) H4).
(* 3/3 *)
repeat split; auto.
apply IHTree2 with t'; auto.
intros; apply H3; auto.
apply (BT_remove_in _ _ _ _ (eq_refl _) H4).
Qed.

Lemma BT_remove_in_rev : forall t' Tree Tree', BT_remove t' Tree = Tree' ->
                    forall t, BT_In t Tree -> t = t' \/ BT_In t Tree'.
unfold BT_Wf; induction Tree.
simpl; intros.
inversion H0.

simpl; intro Tree'.
set (Z := T_compare t' t); assert (Z = T_compare t' t); auto; intro.
induction Z; rewrite <- H0; clear H0 Tree'.
(* 1/3 *)
induction Tree2; intros.
inversion_clear H0; auto.
inversion_clear H1; auto.
left; symmetry; rewrite H0; apply eq_T_compare; auto.
inversion H0.

clear IHTree2_1 IHTree2_2.
set (Tree2 := node t0 Tree2_1 Tree2_2); fold Tree2 in H0, H, IHTree2.
set (Z := BT_split Tree2 t'); assert (Z = BT_split Tree2 t'); auto.
induction Z; auto.
inversion_clear H0; auto.
right; left; auto.
inversion_clear H2; auto.
left;transitivity t; auto.
symmetry; apply eq_T_compare; auto.
right.
elim (BT_split_in t1 a t' Tree2 b); auto.
right; left; auto.
right; auto.
(* 2/3 *)
intros.
inversion_clear H0; auto.
elim IHTree1 with (BT_remove t' Tree1) t0; auto.
right; left; auto.

inversion_clear H1; auto.
rewrite H0; right; right; auto.
right; right; right; auto.
(* 3/3 *)
intros.
inversion_clear H0; auto.
right; left; auto.
inversion_clear H1; auto.
rewrite H0; right; right; auto.
elim IHTree2 with (BT_remove t' Tree2) t0; auto.
right; right; auto.
Qed.

(** ** Removing all elements of one search tree from another *)

Fixpoint BT_diff (Tree Tree':BinaryTree) : BinaryTree :=
  match Tree' with
  | nought => Tree
  | node t' L R => BT_remove t' (BT_diff (BT_diff Tree L) R)
  end.

Lemma BT_diff_wf : forall Tree Tree', BT_Wf Tree -> forall Tree'', BT_diff Tree Tree' = Tree'' -> BT_Wf Tree''.
unfold BT_Wf; intros Tree Tree'; revert Tree; induction Tree'; simpl; intros; rewrite <- H0; auto.
clear H0 Tree''.
apply BT_remove_wf with (BT_diff (BT_diff Tree Tree'1) Tree'2) t; auto.
apply IHTree'2 with (BT_diff Tree Tree'1); auto.
apply IHTree'1 with Tree; auto.
Qed.

Lemma BT_diff_in : forall t Tree Tree' Tree'', BT_diff Tree Tree' = Tree'' ->
                     BT_In t Tree'' -> BT_In t Tree.
unfold BT_Wf; intros.

rewrite <- H in H0; clear H Tree''.
revert Tree H0.
induction Tree'; simpl; auto.
intros; apply IHTree'1; auto.
apply IHTree'2; auto.
eapply BT_remove_in; auto.
exact H0.
Qed.

Lemma BT_diff_in_rev : forall Tree Tree' Tree'', BT_diff Tree Tree' = Tree'' ->
                       forall t, BT_In t Tree -> BT_In t Tree' \/ BT_In t Tree''.
unfold BT_Wf; intros.
rewrite <- H; clear H Tree''.
revert Tree H0; induction Tree'; simpl; intros; auto.
elim (IHTree'1 Tree); auto; intros.
elim (IHTree'2 (BT_diff Tree Tree'1)); auto; intros.
elim (BT_remove_in_rev t0 (BT_diff (BT_diff Tree Tree'1) Tree'2) (BT_remove t0 (BT_diff (BT_diff Tree Tree'1) Tree'2))) with t; auto.
Qed.

(** ** Mapping from lists *)

Fixpoint list_to_BTree (l:list T) :=
  match l with
  | nil => nought
  | (x::l') => BT_add x (list_to_BTree l')
  end.

Lemma in_list_BTree : forall l t, In t l -> BT_In t (list_to_BTree l).
induction l; simpl; auto; intros.
inversion_clear H.
rewrite H0; apply BT_add_in.
apply BT_add_mon; auto.
Qed.

Lemma in_BTree_list : forall l t, BT_In t (list_to_BTree l) -> In t l.
induction l; simpl; auto; intros.
elim (BT_in_add _ _ _ H); auto.
Qed.

Lemma list_to_BTree_wf : forall l, BT_Wf (list_to_BTree l).
unfold BT_Wf; induction l; simpl; auto.
apply BT_wf_add; auto.
Qed.

(** ** Mapping trees *)

Fixpoint BT_size (Tree:BinaryTree) : nat :=
  match Tree with
  | nought => 0
  | node _ L R => (BT_size L) + (BT_size R) + 1
  end.

Lemma BT_size_split : forall Tree x t Tree', BT_split Tree x = (t,Tree') ->
                      BT_size (Tree') = pred (BT_size Tree).
intros Tree x; induction Tree; simpl; intros.
inversion H; auto.
destruct Tree1.
inversion H; simpl.
rewrite plus_comm; auto.
simpl.
set (Tree1 := node t1 Tree1_1 Tree1_2).
fold Tree1 in H, IHTree1.
assert (BT_split Tree1 x = BT_split (node t1 Tree1_1 Tree1_2) x); auto.
revert H H0; elim (BT_split Tree1).
fold Tree1; intros.
inversion H; clear H.
simpl.
rewrite (IHTree1 _ _ (eq_sym H0)).
replace (BT_size Tree1_1 + BT_size Tree1_2 + 1) with (BT_size Tree1); auto.
rewrite (plus_comm (BT_size Tree1 + BT_size Tree2)).
transitivity (BT_size Tree1+BT_size Tree2); auto.
rewrite <- plus_assoc.
rewrite (plus_comm (BT_size Tree2) 1).
rewrite plus_assoc.
replace (pred (BT_size Tree1) + 1) with (BT_size Tree1); auto.
simpl.
rewrite (plus_comm (BT_size Tree1_1 + BT_size Tree1_2)).
simpl; rewrite <- plus_Snm_nSm; auto.
Qed.

Fixpoint BT_add_all (Tree Tree':BinaryTree) :=
  match Tree with
  | nought => Tree'
  | node t L R => BT_add_all R (BT_add_all L (BT_add t Tree'))
  end.

Lemma BT_wf_add_all : forall Tree Tree', BT_Wf Tree' -> BT_Wf (BT_add_all Tree Tree').
induction Tree; auto.
intros; simpl.
apply IHTree2; apply IHTree1; apply BT_wf_add; auto.
Qed.

(*
Lemma BT_add_all_wf_rev : forall Tree Tree', BT_Wf (BT_add_all Tree Tree') -> BT_Wf Tree'.
induction Tree; simpl; auto.
intros.
apply BT_add_wf_rev with t; auto.
Qed.
*)

Lemma BT_add_all_mon : forall Tree Tree' t, BT_In t Tree' -> BT_In t (BT_add_all Tree Tree').
induction Tree.
simpl; intros; auto.
simpl; intros.
apply IHTree2; apply IHTree1; apply BT_add_mon; auto.
Qed.

Lemma BT_add_all_in : forall Tree Tree' t, BT_In t Tree -> BT_In t (BT_add_all Tree Tree').
induction Tree.
simpl; intros; inversion H.
simpl; intros.
repeat (elim H; clear H; intro H); auto.
apply BT_add_all_mon; auto.
apply BT_add_all_mon; apply BT_add_all_mon.
rewrite H; apply BT_add_in; auto.
Qed.

Lemma BT_in_add_all : forall Tree Tree' t, BT_In t (BT_add_all Tree Tree') ->
                      BT_In t Tree \/ BT_In t Tree'.
induction Tree; simpl; auto.
intros.
elim (IHTree2 _ _ H); intros; auto.
elim (IHTree1 _ _ H0); intros; auto.
elim (BT_in_add _ _ _ H1); intros; auto.
Qed.

Section Map.

Variable f:T->T.

Fixpoint BT_map (Tree:BinaryTree) : BinaryTree :=
  match Tree with
  | nought => nought
  | node t L R => BT_add_all (BT_map L) (BT_add (f t) (BT_map R))
  end.

Lemma BT_map_in : forall t Tree, BT_In t Tree -> BT_In (f t) (BT_map Tree).
induction Tree; auto.
repeat (intro H; elim H; clear H); simpl; intros.
apply BT_add_all_in; auto.
apply BT_add_all_mon; apply BT_add_in; auto.
apply BT_add_all_mon; apply BT_add_mon; auto.
Qed.

End Map.

End Trees.

Arguments nought [T].
Arguments node [T] _ _ _.
Arguments BT_In [T] _ _.
Arguments BT_wf [T] _ _.
Arguments BT_add [T] _ _ _.
Arguments BT_split [T] _ _.
Arguments BT_remove [T] _ _ _.
Arguments BT_diff [T] _ _ _.
