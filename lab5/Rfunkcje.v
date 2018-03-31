(** Consider the following definitions (which could be found in the standard 
   library *)

Section On_functions.
Variables (U V W : Type).

Variable g : V -> W.
Variable f : U -> V.

 Definition injective : Prop := forall x y:U, f x = f y -> x = y.
 Definition surjective : Prop := forall v : V, exists u:U, f u = v.

Lemma injective' : injective -> forall x y:U, x <> y -> f x <> f y.
Proof.
unfold not.
intros.
apply H0.
unfold injective in H.
apply H.
assumption.
Qed.

 Definition compose := fun u : U => g (f u).

End On_functions.

Arguments compose [U V W].
Arguments injective [U V].
Arguments surjective [U V].

Lemma injective_comp : forall U V W (f:U->V)(g : V -> W),
                       injective (compose g f) -> injective f.
Proof.
unfold compose.
unfold injective.
intros.
apply H.
rewrite H0.
reflexivity.
Qed.



Lemma surjective_comp : forall U V W (f:U->V)(g : V -> W),
                       surjective (compose g f) -> surjective g.
Proof.
unfold compose.
unfold surjective.
intros.
destruct (H v).
exists (f x).
assumption.
Qed.



Lemma comp_injective : forall U V W (f:U->V)(g : V -> W),
                       injective f -> injective g -> injective (compose g f).
Proof.
unfold compose.
unfold injective.
intros.
apply H.
apply H0.
assumption.
Qed.



Fixpoint iterate (A:Type)(f:A->A)(n:nat) {struct n} : A -> A :=
 match n with 0 => (fun a => a)
            | S p => fun a => f (iterate _ f p a) 
 end.

 Lemma iterate_inj : forall U (f:U->U) , 
                      injective f ->
                      forall n: nat, injective   (iterate _ f n).
Proof.
 induction n;simpl.
* unfold injective.
  intros.
  assumption.
* generalize IHn.
  unfold injective.
  intros.
  apply IHn0.
  unfold injective in H.
  apply H.
  assumption.
Qed.   
