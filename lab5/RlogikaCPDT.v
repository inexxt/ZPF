
(*
Prove these tautologies of propositional logic, 
using only the tactics apply, assumption, constructor, 
destruct, intro, intros, left, right, split, and unfold.
*)

Lemma P: (True \/ False) /\ (False \/ True).
Proof.
split.
left.
constructor.
right.
constructor.
Qed.

Lemma D: forall P:Prop, P -> ~ ~ P.
Proof.
unfold not.
intros.
apply H0.
assumption.
Qed.

Lemma Trzeci: forall P Q R: Prop, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
intros.
(*destruct H as[K L].*)
destruct H as[K [L|L]].
* left.
  split;assumption.
* right.
  split;assumption.
Qed.

Section FirstOrder.

Parameter T:Type.

Parameter p: T -> Prop.

Parameter q: T -> T -> Prop.

Parameter a: T.

Parameter f: T -> T.

Lemma C: (p a) -> (forall x, p x -> exists y, q x y) -> 
                (forall x y, q x y -> q y (f y)) -> exists z, q z (f z). 
Proof.
intros.
assert (exists z, q a z).
* apply H0.
  assumption.
* destruct H2.
  exists x.
  apply (H1 a x).
  assumption. 
(*  eapply H1.
  eassumption.
*)
Qed. 
