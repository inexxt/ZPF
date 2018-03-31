Set Implicit Arguments.
Set Asymmetric Patterns.



(* ================================================*)
(* 0. Functional Programming                       *)
(* ================================================*)

(*
    Functional programming (Coq's style)

    1. Types provide guidance for building and
       destructing data
    2. Programs are data

*)

(* ----------------------------------------------- *)

(*
    Programs are data

    There is no “return” keyword:
      expression = statement

    - The program that always returns 4 is:
        4
    - This program also returns (or better computes
      to) 4:
        if (false || true) then 2 + 2 else 7
        if true then 2 + 2 else 7
        2 + 2
        4
    - This program also computes to 4:
        2 + (if 7 == 2 then 4 else 2)
        2 + (if false then 4 else 2)
        2 + 2
        4
*)

(* ----------------------------------------------- *)

(*
    Programs are /really/ data

    This data is actually a program that doubles
    its input:

      (fun x => x + x)

    What does this evaluate to?

      (fun x => x + x) 3
    
    Recall:  f(x) is written (f x) in Coq

    This program takes in input a function f and
    uses it twice

      (fun f => f 3 + f 4)

    What does this evaluate to?

      (fun f => f 3 + f 4) (fun x => x + x)
*)

(* ================================================*)
(* 1. Build and destruct simple data               *)
(* ================================================*)

(* Booleans *)

Check bool : Type.
Check true : bool.
Check false.

(* Booleans are defined in the prelude as a data
   type with exactly the two constructors
   true and false:

   Inductive bool : Type := true | false.

   We can use this fact when we program with
   booleans via the "match .. with .. end"
   construct.
*)

(* Example: defining the negation *)
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Let's look at the type of the function we've just
   defined
*)
Check negb.

(* Given the type of negb, if we apply it to a
   boolean expression we obtain a boolean.
*)
Check (negb false).

(* Actually, the outermost parentheses can be
   omitted.  Like in:
   Check negb false.
*)

(* In this lecture we are not going to prove that
   our programs are correct, that is the topic of 
   the next lesson.  We are going to just test
   our programs.
*)
Eval compute in negb true.
Print compute.
Eval compute in negb false.

(* The system provides syntactic sugar for
   matching over a boolean.
*)
Definition another_negb (b : bool) : bool :=
  if b then false else true.

(* Note that Definition is just a convenient syntax
   to name an otherwise anonymous function *)
Definition yet_another_negb :=
  (fun b : bool =>
     if b then false else true). 

(* Definition of the boolean conjunction.

   Note: pattern matching over multiple values
   is just syntactic sugar.   
*)
Definition andb (b1 : bool) (b2 : bool) :=
  match b1, b2 with
  | true, true => true
  | _, _ => false
  end.
 (* actually, this is equivalent to:
    if b1 then b2 else false *)

(* Some more syntactic sugar *)
Notation "x && y" := (andb x y).

Eval compute in true && false.
Eval compute in true && true.


(* ----------------------------------------------- *)

(* Polymorphic data containers: the option type *)

(* The simplest generic container is the option type.
   Such container can either be empty, i.e. contain
   no value, or it can contain some value.
   Such container type is parametric over the
   type A of the values it contains.

   Inductive option (A : Type) : Type :=
   | None
   | Some (a : A).
*)

Check option.
Check option bool: Type.

Check bool.
Check bool: Type.
Check Some true. (* Implicit argument *)
About Some.
About Nat.

(* The @ locally disables the implicit arguments *)
Check @Some bool true.
Check @Some _ true.

(* We now define a function checking if an
   option holds a value or not.
 
   Note the A parameter needed in order to wirte
   the type of "box"
*)
Definition is_empty A (box : option A) : bool :=
  match box with
  | None => true
  | Some _ => false  (* Here _ means discard *)
  end.

(* Note the implicit argument (A not passed) *)
Eval compute in is_empty (Some true).

(* Note: the function is polymorphic! *)
Eval compute in is_empty (Some 4).

(* first example of match with a binder *)
Definition get_default A (box: option A) (a : A) : A :=
  match box with
  | None => a
  | Some x => x
  end.

Eval compute in get_default None 3.

(* Here x binds the contents of the Some container,
   the value 4, that is also the result. *)
Eval compute in get_default (Some 4) 3.



(* Pairs *)

(* There is only a way to build a pair, and any
   two values can be paired

   Inductive prod (A B : Type) : Type :=
   | pair (a : A) (b : B).

   Notation "A * B" := (prod A B).
   Notation "( x , y )" := (pair x y).
*)
 
Check (true, Some false).

Definition fst A B (p : A * B) :=
  match p with (x, _) => x end.

Eval compute in fst (true, None).




Definition snd A B (p : A * B) :=
  match p with (_, y) => y end.

(* Exercises<<<<<<<<<                              *)

(* 1.1 Write a comparison function for the bool
   data type.
   Such function must evaluate to true if and only if
   the two input booleans b1 and b2 have the same
   value
*)
Definition eq_bool (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

(* 1.2 Test the function you just wrote *)
Eval compute in eq_bool true false.

(* 1.3 Write a function that computes the exclusive
   or of the two booleans in input *)

Check true.
Definition xorb (b1 b2 : bool) : bool := 
match eq_bool b1 b2 with
| false => true
| true => false
end.


(* 1.4 Test the function you just wrote *)
Eval compute in xorb true false.

(* 1.5 Write and test a function that
   applies the fst projection over the option
   type.
	  
   Hint: if o had type option (A * B) and, after
   scrutiny o turns out to be "Some x", which is
   the type of x?	   
 *)
Definition ofst A B (o: option (A * B)) : option A :=
match o with
| Some (a, b) => Some a
| None => None 
end.
(* Exercises>>>>>>>>>                              *)

(* ================================================*)
(* Recursive data and fixpoints *)
(* ================================================*)

(* Datatypes can be recursive

   Inductive nat : Type :=
   | O
   | S (n : nat).
*)

Check S (S O).
Check 1.

(* Recursive types, recursive functions

*)   
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n1 => S (plus n1 m)
  end.

Infix "+" := plus.

Check 1 + 2.
Eval compute in 1 + 2.

Fixpoint fast_plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n1 => fast_plus n1 (S m)
  end.

Check fast_plus 1 2.


Eval simpl in
  (fun n => fast_plus (S n) 3).
Eval simpl in
  (fun n => plus (S n) 3).


(* Lists are pretty much like naturals 
   
  Inductive list (A : Type) : Type :=
  | nil
  | cons (x : A) (xs : list A).
  
*)
Infix "::" := cons.
Arguments nil {A}.
Arguments cons {A} x xs.

(* The type of lists imposes all the elements to
    be in the same type! *)
Check true :: false :: nil.
Fail Check 1 :: false :: nil.

(* A non recursive function on lists *)
Definition tl A (l : list A) : list A :=
  match l with
  | nil => nil
  | _ :: xs => xs
  end.

Eval compute in tl (6 :: 99 :: nil).

(* The most popular function on lists *)
Fixpoint len A (l : list A) : nat :=
  match l with
  | nil => O
  | x :: xs => 1 + (len xs)
  end.

Eval compute in len (1 :: 2 :: 3 :: nil).

(* Two other examples of function over lists:

   - from a list of pairs, to a pair of lists
   - from two lists, to a list of pairs

   Note the let construction to name an
   intermediate result used more than once.

*)
Fixpoint split A B (l : list (A * B)) : list A * list B :=
  match l with
  | nil => (nil, nil)
  | (x,y) :: rest =>
      let xs_ys := split rest in
      (x :: fst xs_ys, y :: snd xs_ys)
  end.

Eval compute in
  split ((1,2) :: (3,4) :: nil).

Fixpoint zip A B (la : list A) (lb : list B) : list (A * B) :=
  match la, lb with
  | nil, nil => nil
  | x::xs, y::ys => (x,y) :: zip xs ys
  | _, _ => nil
  end.

Eval compute in
  zip (1 :: 2 :: nil) (true :: false :: nil).

Eval compute in
  let xs_ys := split ((1,2) :: (3,4) :: nil) in
  zip (fst xs_ys) (snd xs_ys).

(* Exercises<<<<<<<<<                              *)

(* 2.1 Write a function to compare two natural
   numbers n1 and n2.
   It must evaluate to true if and only if the
   two numbers are equal *)
Fixpoint eq_nat n1 n2 :=

Eval compute in eq_nat 7 4.
Eval compute in eq_nat 7 7.
Eval compute in eq_nat 7 (3 + 4).

(* 2.2 Write a function that computes the product
   of two natural numbers. Hint: you can use
   (many times) the function that computes the
   addition of natural numbers *)
Fixpoint mult n1 n2 :=

Infix "*" := mult.

Eval compute in 3 * 4.
Eval compute in eq_nat (3 * 4) 12. 
Eval compute in eq_nat (3 * 0) 0.
Eval compute in eq_nat 0 (3 * 0).

(* 2.3 Write a function that appends two lists

   Example:
     append (1 :: 2 :: nil) (3 :: nil)
   must evaluate to
     (1 :: 2 :: 3 :: nil)

*)
Fixpoint
  append A (l1 : list A) (l2 : list A) : list A
:=

Eval compute in append (1 :: 2 :: nil) (3 :: nil).

(* 2.4 Write a function that reverses a list.
   Hint: use append. *)
Fixpoint rev1 A (l : list A) : list A :=

Eval compute in rev1 (1 :: 2 :: 3 :: nil).


(* 2.5 Again list reversal, but this time using
   an auxiliary function that uses an accumulator. *)
Fixpoint rev2_aux A (acc l : list A) : list A :=
  match l with
  | nil => acc
  end.

Definition rev2 A (l : list A) := rev2_aux nil l.

Eval compute in rev2 (1 :: 2 :: 3 :: nil). 

(* Exercises>>>>>>>>>                              *)

(* ================================================*)
(* Illegal data types and recursive functions *)
(* ================================================*)

Fail
Fixpoint wrong A (l : list A) {struct l} :=
  match l with
  | nil => 0
  | x :: xs => 1 + wrong (x :: nil)
  end.

(* RUN THAT IN A PATCHED (UNSOUND) COQ

   Recall:
   
     Inductive False : Prop := .
     
   i.e. There is no way to build a value
   of type False.

*)

(*
Fixpoint loop (n : nat) : False := loop n.

Check loop 3.
Fail Timeout 2 Eval compute in loop 3.

Inductive non_positive : Type :=
| Call (f : non_positive -> False)

Definition self (t : non_positive) : False :=
  match t with
  | Call f => f t
  end.

Definition loop2 : False := self (Call self).

Fail Timeout 2 Eval compute in loop2.
*)

(* 
   Note: for the experts in the room...
   Yes, there are ways to use a well founded order
   relation as the decreasing measure. See the
     
     Function ... {measure ...}

   and

     Function ... {wf ...}

   in the Reference Manual.
*)

(* ================================================*)
(* Higher order programming *)
(* ================================================*)

(* A function can be abstracted over another
   function.  It is a useful mechanism to write
   code that can be reused, especially in the context
   of polymorphic containers
*)
Fixpoint map A B (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | x :: xs => f x :: map f xs
  end.

Eval compute in
  map (fun x => x + 2) (3 :: 4 :: 7 :: nil).
Eval compute in
  map negb (true :: false :: nil).
  
(* fold f (x1 :: x2 :: .. xn :: nil) a
     =
	    (f xn (.. (f x2 (f x1 a))))
*)
Fixpoint fold A B (f : B -> A -> A) (l : list B) (a : A) : A :=
  match l with
  | nil => a
  | x :: xs => fold f xs (f x a)
  end.

Eval compute in fold plus (1 :: 2 :: 3 :: nil) 0.


(* Exercises<<<<<<<<<                              *)

(* 4.1 Write a function that reverses a list based on       fold.  Hint: use fold and cons.
*)
Definition rev A (l : list A) :=

Eval compute in rev (1 :: 2 :: 3 :: 4 :: nil).

(* 4.2 Write a function that appends two lists, this
   time using fold and rev *)
Definition another_append A (l1 l2 : list A) :=

Eval compute in
  another_append (1 :: 2 :: nil) (3 :: 4 :: nil).

(* 4.3 The higher order function iter takes a
   function f, an initial value a and a number n.
   The result is (f (f ... (f a))),
   where f is applied n times. *) 
Fixpoint iter A (f : A -> A) a n :=

(* 4.4 Write a function that computes the sum of
   two natural numbers using iter *)
Definition another_plus n1 n2 :=

Eval compute in another_plus 3 4.

(* 4.5 Write a function that computes the product of
   two natural numbers using iter and plus *)
Definition another_mult n1 n2 :=

Eval compute in another_mult 3 7.
Eval compute in another_mult 3 0.
Eval compute in another_mult 0 7.
Eval compute in another_mult 2 4.

(* Exercises>>>>>>>>>                              *)

(* ================================================*)
(* Code reuse: a taste of ad-hoc polymorphism *)
(* ================================================*)

Class Eq (A : Type) := cmp : A -> A -> bool.

Infix "==" := cmp (at level 70, no associativity).

Fixpoint mem A `{Eq A} (y : A) (l : list A) : bool :=
  match l with
  | nil => false
  | x :: xs => if x == y then true else mem y xs
  end.

Instance bool_Eq : Eq bool := eq_bool.

Check mem true (false :: false :: true :: nil).
Eval compute in
  mem true (false :: false :: true :: nil).

Instance pair_Eq A `{Eq A} B `{Eq B} : Eq (A * B) :=
  fun (x y : A * B) =>
    (fst x == fst y) && (snd x == snd y).

Eval compute in
  mem (true,false)
        ((false,false) :: (true,false) :: nil).
Eval compute in
  mem (true,false)
        ((false,false) :: (false,true) :: nil).

(* Exercises<<<<<<<<<                              *)

(* 5.1 Register eq_nat as the comparison function
   for the nat type *)
Instance nat_Eq : Eq nat :=

(* Example: an associative list mapping numbers to
   boolean values.
   1 is mapped to true, 2 to false. *)
Definition an_associative_list : list (nat * bool) :=
  (1,true) :: (2,false) :: nil.

(* 5.2 Write a function that finds the value
   associated to y in the associative list l.   *)
Fixpoint
  find A {e : Eq A} (y : A) B (l : list (A * B))
:
  option B
:=

Definition data := 1 :: 4 :: 7 :: nil.

(* 5.3 Define a list of pairs of natural numbers
   such that the first item is an element of the list
   data (the one just defined) and the second item
   is its square.
   I.e.  the list must be (1,1)::(4,16)::... but
   don't write it by hand.  Instead, use map. *)
Definition square_cache :=

Eval compute in find 3 square_cache.

(* 5.4 The function square takes a cache c (that is
   an associative list) and a number n.  It computes
   a pair: the first component is the square of the
   input n while the second component is
   an (eventually) updated cache. *)
Definition square cache n :=

Eval compute in square square_cache 3.

(* Exercises>>>>>>>>>                              *)

(* vim: set tw=50 *)

