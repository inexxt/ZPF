
(*
Prove these tautologies of propositional logic, 
using only the tactics apply, assumption, constructor, 
destruct, intro, intros, left, right, split, and unfold.
*)

Lemma P: (True \/ False) /\ (False \/ True).
split.
* left.
constructor.
* right.
constructor.
Proof.
Qed.


Print "~".

Lemma D: forall P:Prop, P -> ~ ~ P.
intros.
intros H1.
destruct H1.
assumption.

Proof.

Qed.

Lemma Trzeci: forall P Q R: Prop, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
intros.
destruct H.
destruct H0.
* left.
  constructor; assumption.
* right.
  constructor; assumption.
Qed.

Section FirstOrder.

Parameter T:Type.

Parameter p: T -> Prop.

Parameter q: T -> T -> Prop.

Parameter a: T.

Parameter f: T -> T.

(*You may use assert*)
  
Lemma C: (p a) -> (forall x, p x -> exists y, q x y) -> 
                (forall x y, q x y -> q y (f y)) -> exists z, q z (f z). 
Proof.
intros.



apply H0 in H.
destruct H.
assert (q x (f x)).
apply (H1 a).
assumption.
exists x.
assumption.
Qed. 

End FirstOrder.  
