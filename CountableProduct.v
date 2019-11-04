Require Export CountableTypes.
From Coq Require Import omega.Omega.
Close Scope Q.

Fixpoint repeat_digit (digit : bool) (n : nat) (base : positive) : positive :=
match n with
| O => base
| (S m) => (if digit then xI else xO) (repeat_digit digit m base)
end.

Fixpoint digit_count (digit : bool) (p : positive) : nat :=
match p with
| xO q => (if digit then id else S) (digit_count digit q)
| xI q => (if digit then S else id) (digit_count digit q)
| xH => O
end.

Lemma repeat_digit_count : forall digit n base, digit_count digit (repeat_digit digit n base) = n + digit_count digit base.
Proof.
  intros [|] n;
  induction n;
    intros;
    try (simpl; rewrite IHn);
    reflexivity.
Qed.

Lemma repeat_digit_count_negb : forall digit n base, digit_count digit (repeat_digit (negb digit) n base) = digit_count digit base.
Proof.
  intros [|] n;
  induction n;
    intros;
    try (simpl; rewrite IHn);
    reflexivity.
Qed.

Definition double_positive_inj (z : nat * nat) :=
  Pos.to_nat (repeat_digit true (fst z) (repeat_digit false (snd z) xH)).

Lemma double_positive_inj_injective : FunctionProperties.injective double_positive_inj.
Proof.
  intros [x1 x2] [y1 y2].
  unfold double_positive_inj.
  simpl.
  intro H.
  apply Pos2Nat.inj in H.
  pose H as H1.
  apply (f_equal (digit_count true)) in H1.
  rewrite repeat_digit_count,
          repeat_digit_count,
          repeat_digit_count_negb,
          repeat_digit_count_negb,
          Nat.add_cancel_r in H1.
  pose H as H2.
  apply (f_equal (digit_count false)) in H2.
  rewrite repeat_digit_count_negb,
          repeat_digit_count_negb,
          repeat_digit_count,
          repeat_digit_count,
          Nat.add_cancel_r in H2.
  auto.
Qed.

Lemma injective_cross_prod
  {X1 X2 Y1 Y2 : Type}
  (f : X1 -> Y1)
  (g : X2 -> Y2) :
  FunctionProperties.injective f ->
  FunctionProperties.injective g ->
  FunctionProperties.injective (fun x => (f (fst x), g (snd x))).
Proof.
  intros Hf Hg [x11 x12] [x21 x22] eq.
  injection eq as eq1 eq2.
  apply Hf in eq1.
  apply Hg in eq2.
  subst.
  reflexivity.
Qed.

Lemma countable_product
  {X Y : Type} :
  CountableT X -> CountableT Y -> CountableT (X * Y).
Proof.
  intros [f Hf] [g Hg].
  econstructor.
  eapply injective_composition.
  - apply (injective_cross_prod f g Hf Hg).
  - apply double_positive_inj_injective.
Qed.
