module NegativeTests.Positivity

open FStar.All

(* basic test case for violation of positivity *)
[@ (fail [3])]
noeq type t1 =
  | C11: (t1 -> nat) -> t1

(* unfolding inductive case *)
(* t3 itself is positive *)
noeq type t3 (a:Type) =
  | C31: (a -> nat) -> t3 a

(* t4 is just an intermediate type to test two levels of unfolding, C42 checks that we don't loop *)
noeq type t4 (a:Type) =
  | C41: t3 a -> t4 a
  | C42: a -> t4 a -> t4 a

(* t5 is non-positive *)
[@ (fail [3])]
noeq type t5 (a:Type) =
  | C51: t4 (t5 a) -> t5 a

(* case where we need memoization for type parameters also, since they are flipped *)
(* t6 itself is positive *)
noeq type t6 (a:Type) (b:Type) =
  | C61: (a -> b) -> t6 b a -> t6 a b
  | C62: t6 a b

(* t7 is non-positive *)
[@ (fail [3])]
noeq type t7 =
  | C71: t6 t7 nat -> t7

(* and so is t8 *)
[@ (fail [3])]
noeq type t8 =
  | C81: t6 nat t8 -> t8

(* if we can't unfold a type abbreviation, too bad *)
assume new type t9: Type -> Type

(* t10 is non-positive since we can't prove that t9 uses it's parameters positively *)
[@ (fail [3])]
noeq type t10 =
  | C101: t9 t10 -> t10

(* t11 is non-positive because it cannot be a parameter to itself *)
[@ (fail [3])]
noeq type t11 (a:Type) =
  | C111: t11 (t11 a) -> t11 a
