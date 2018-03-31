Lemma and_comm: forall P Q, P/\Q -> Q /\ P.
Proof.
intros.
destruct H.
split.
 * assumption.
 * assumption.
Qed.

Print and_comm.

Lemma or_comm: forall P Q, P \/ Q -> Q \/ P.
Proof.
intros.
destruct H.
 * right. 
   assumption.
 * left;assumption.
Qed.

Print False.

Lemma ZFalszu: False -> 2+2=5.
Proof.
intro.
destruct H.
Qed.

Print ex.


Lemma is: @ex nat (fun x:nat => x+1 = 2).

Lemma istnieje1: exists x, x+1=2.
Proof.
exists 1.
simpl.
trivial.
Qed.

Lemma istnieje2: forall m n, (exists x, x+n = m) -> (n=m) \/ (exists k, m = S k).
Proof.
intros.
destruct H.
(*destruct x.*)
destruct x eqn:?.
* left.
  simpl in H.
  assumption.
* right.
  simpl in H.
  exists (n0+n).
  symmetry.
  assumption.
Qed. 