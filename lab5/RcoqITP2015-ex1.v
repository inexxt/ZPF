(***********************************************************************)
(** An exercises file to be launch with coqide exercises1.v            *)
(** Revised version, 2015/8/29                                         *)
(***********************************************************************)

(** * Stating and proving simple propositions *)

(* Prove the following *)

Lemma composition : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
intros.
apply H0.
apply H.
exact H1.
(* use primitive tactics here *)
Qed.

Lemma tautology : forall (A:Type) (P:A -> Prop) (a:A), P a ->  P a.
Proof.
(* use primitive tactics here *)
intros.
exact H.
Qed.

(** * Looking at some examples of inductive definitions and 
      definitions defined in the automatically loaded prelude of Coq *)

(** * Some basic inductive propositions *)

(* Let us look (again) at how is the [True] proposition (inductively) defined *)
(* Observe that [True] is an inductive definition with one constructor *)
(* with no argument. Hence, it can always be proved (being inhabited). *)
Print True.

(* Let us look at how is the [False] proposition (inductively) defined *)
(* Observe that [False] is an inductive definition with no constructor at all *)
(* Hence, it can never be proved (being inhabited) *)
Print False.

(* Let us look at how is the conjunction of propositions is inductively defined *)
(* Observe that [and A B] is bound to a notation, "A /\ B" *)
(* Observe that [and A B] has a single constructor expecting two arguments: a proof of A and a proof of B *)
(* Observe that [and A B] comes with "implicit" arguments *)
Print and.

(* Since [and] is bound to the notation "\/", we can as well say *)
Print "/\".

(* Let us look at how is the disjunction of propositions is inductively defined *)
(* Observe that [or A B] is bound to a notation, "A \/ B" *)
(* Observe that [or A B] has two constructors expecting each one argument, *)
(* either a proof of A or a proof of B *)
(* Observe that [and] comes with "implicit" arguments *)
Print or.

(* Let us look as how the negation is defined in terms of [False] *)
Print not.

(* It happens that "not A" is bound to a notation "~ A" as witnessed by the
following *)
Print "~".

(* Let us look as how iff is defined in terms of [and] and [->] *)
Print iff.

(* It happens that "iff A B" is bound to a notation "A <-> B" as witnessed by the
following *)
Print "<->".

Print and.


(* Exercice: define inductively a ternary conjunction on the model of the binary one *)
Inductive and3 (A B C:Prop) : Prop := conj3: A -> B -> C -> and3 A B C. 


(* Show that this ternary conjunction is equivalent to two binary ones *)
Lemma and3_decomposition : forall A B C : Prop, and3 A B C <-> A /\ B /\ C.
(*
Proof.
intros.
split.
* intro.
  destruct H. 
  split; try split; assumption.
* intro.
  destruct H.
  destruct H0.
  constructor; assumption. 
Qed.
*)
Proof.
intros.
unfold iff.
apply conj.
intro.
elim H.
intros.
apply conj;try apply conj; assumption.
intro.
elim H.
intros.
elim H1.
intros.
apply conj3;assumption.
Qed.

(* Sections allow to introduce a local assumption which will later be discharged *)

Section Classical_reasoning.

(* We assert the classical principle of double negation elimination *)

Variable DNE : forall A:Prop, ~~A -> A.

Lemma excluded_middle : forall A:Prop, A \/ ~A.
Proof.
(* find a proof in Coq ... *)
(* Hint: use first DNE, then prove the right-hand side *)
intro.
apply DNE.
unfold not.
intro.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.


Lemma ef: forall (P: nat ->  Prop), (exists x:nat, ~ P x) -> ~(forall x:nat, P x).
Proof.
intros.
unfold not.
intro.
destruct H.
apply H.
apply H0.
Qed.


Lemma fe: forall (P: nat ->  Prop), ~(forall x:nat, P x) -> exists x:nat, ~ P x.
Proof.
intros.
apply DNE.
unfold not.
intros.
apply H.
intros.
assert (P x \/ ~P x) by apply excluded_middle.
destruct H1.
 * assumption.
 * exfalso.
   apply H0.
   exists x.
   exact H1.
Qed.


 

Lemma drinker_paradox :forall P:nat -> Prop, exists x:nat, forall y:nat, P x -> P y.
Proof.
(*
(* find a proof in Coq ... *)
intro P.
(* We give a proof directly using DNE *)
apply DNE. intro H. apply H.
exists 0.
intros y HP0.
apply DNE. intro H'. apply H'.
exfalso.
apply H.
exists y.
intros y' HPy.
exfalso.
apply H', HPy.
*)
intros.
cut ((exists x:nat, ~ P x)\/ ~(exists x:nat, ~ P x)).
* intros.
  destruct H.
  - destruct H.
    exists x.
    intros.
    absurd (P x); trivial.
  - exists 0.
    intros.
    cut ((P y) \/ ~(P y)).
    + intros.
      destruct H1.
      ++ trivial.
      ++ exfalso.
         apply H.  
         exists y.
         assumption.
    + apply excluded_middle.
* apply excluded_middle.
Qed.


(*intros.
cut ((exists x:nat, ~ P x)\/ ~(exists x:nat, ~ P x)).
* intros.
  elim H.
  - intro.
    destruct H0.
    exists x.
    intros.
    absurd (P x); trivial.
  - intro.
    exists 0.
    intros.
    cut ((P y) \/ ~(P y)).
    + intros.
      elim H2.
      ++ trivial.
      ++ intros.
         elim H0.
         exists y.
         assumption.
    + apply excluded_middle.
* apply excluded_middle.
Qed.
*)



(* This closes the section, discharging over DNE *)
End Classical_reasoning.

(* Check the statement of drinker_paradox out of the section *)
Check drinker_paradox.
