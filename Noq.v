Require Import Arith.

Module Noq.

(*
Inductive int : Type :=
  | O : int
  | S n : forall n,
*)

Inductive noun : Type :=
  | atom : nat -> noun
  | cell : noun -> noun -> noun.


Notation "# x " := (atom x)
                   (at level 71, right associativity).
Notation "'[' x  y ']'" := (cell x y)
                        (at level 70, right associativity).

Check #1.
Check [#2 #4].
Check [#1 [#1 #1]].
Check [#2 [#6 [[#28 #29] [#30 [#62 #63]]]]].

(*
`$`   buc
`/`   fas
`+`   lus
`(`   pel
`)`   per
`[`   sel
`]`   ser
`*`   tar
`=`   tis
`?`   wut
 *)

Inductive superset : Type :=
  | nock : noun -> superset     (* ε *)
  | wut  : noun -> superset     (* ? *)
  | lus  : noun -> superset     (* + *)
  | tis  : noun -> superset     (* = *)
  | fas  : noun -> superset     (* / *)
  | tar  : noun -> superset     (* * *)
  | inf  : superset.            (* ∞ *)

Notation "</\> a" := (nock a)
                    (at level 60, right associativity).
Notation "'nock' a" := (nock a)
                    (at level 60, right associativity).
Notation "? a" := (wut a)
                    (at level 60, right associativity).
Notation "+ a" := (lus a)
                    (at level 60, right associativity).
Notation "= a" := (tis a)
                    (at level 60, right associativity).
Notation "* a" := (tar a)
                    (at level 60, right associativity).
Notation "// a" := (fas a)      (* TODO: How to overwrite notation? *)
                    (at level 60, right associativity).

Check (= [#1 #2]).
Check (// [#1 #2]).
(* Why doesn't this work?
Check (forall a, (// [#1 a])).
 *)

Reserved Notation "t1 '==>' t2" (at level 40).

(* TODO: Remove parentheses, i.e., ?([a b]) => ?[a b] *)
(* TODO: Manage to put cell as [ ]  *)
(* TODO: Replace // with / *)
(* TODO: Rule 39 does not work with * !! *)
(* Rule 6 is for aesthetics, to be covered soon  *)
Inductive reduce : (superset) -> (superset) -> Prop :=
(*| line1  : A noun is an atom or a cell.                *)
(*| line2  : An atom is a natural number.                *)
(*| line3  : A cell is an ordered pair of nouns.         *)
(*| line4  :                                             *)
  | line5  : forall a,   (nock a) ==> *a
(*| line6  : [a b c]     [a [b c]]                       *)
(*| line7  :                                             *)
  | line8  : forall a b, (? cell a b) ==> nock (#0)
  | line9  : forall a,   (?(#a)) ==> nock (#1)
  | line10 : forall a b, (+ cell a b) ==> (+cell a b)
  | line11 : forall a,   (+(#a)) ==> (nock #(a + 1))
  | line12 : forall a,   (=(cell a a)) ==> (nock #0)
  | line13 : forall a b, (=(cell a b)) ==> (nock #1)
  | line14 : forall a b, (=(cell a b)) ==> (inf)
(*| line15 :                                             *)
  | line16 : forall a,   (//(cell (#1) a)) ==> (nock a)
  | line17 : forall a b, (//(cell (#2) (cell a b))) ==> (nock a)
  | line18 : forall a b, (//(cell (#3) (cell a b))) ==> (nock b)
  (*
  | line19 : forall a b, (// (cell (#(a + a)) b)) ==> (// (cell (#2) (// (cell (#a) b))))
  | line20 : forall a b, (// (cell (#(a + a + 1)) b)) ==> (// (cell (#3) (// (cell (#a) b))))
 *)
  | line21 : forall a,   (//a)  ==> // a


(*| line38 :                                             *)
  | line39 : forall a,   tar a ==> (inf)

where "t1 '==>' t2" := (reduce t1 t2).


forall t1 t1' ,
       t1 ==> t1' ->
       (tmult t1 t2) ==> (tmult t1' t2)



Fixpoint eq (a1 a2 : atom) : atom :=
  match (a1, a2) with
    | (#a1', #a2') => if (beq_nat a1' a2') then #0 else #1
  end.

Fixpoint Equals (n:noun) : noun :=
  match n with
    | cell (#a) (#b) => atom (eq a b)
    | cell (#a) b => atom (eq a (Equals b))
    | cell a (#b) => atom (eq (Equals a) b)
    | cell a b => atom (eq (Equals a) (Equals b))
    | #a => atom 1
  end.

End Noq.
