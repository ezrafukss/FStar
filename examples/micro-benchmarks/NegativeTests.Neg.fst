module NegativeTests.Neg

irreducible val x:nat
[@(fail [19])]
let x = -1 //should fail reporting 1 error
irreducible val y:nat
[@(fail [19])]
let y = -1 //should also fail reporting only 1 error

[@(fail [19])]
let assert_0_eq_1 () = assert (0=1) //should fail

[@(fail [19])]
let hd_int_inexhaustive l = match l with
  | hd::_ -> hd //should fail

val test_label: x:int -> Pure int (requires (b2t (x > 0))) (ensures (fun y -> y > 0))
let test_label x = x

val test_precondition_label: x:int -> Tot int
[@(fail [19])]
let test_precondition_label x = test_label x //should fail

val test_postcondition_label: x:int -> Pure int (requires True) (ensures (fun y -> y > 0))
[@(fail [19])]
let test_postcondition_label x = x //should fail

val bad_projector: option 'a -> 'a
[@(fail [19])]
let bad_projector x = Some?.v x (* should fail *)

assume type t_pred : (result int -> Type) -> Type
[@(fail [19])]
assume val test: t_pred (fun ri -> b2t (V?.v ri = 0))//should fail: not (V? ri)

assume val f1: (x:int -> Tot unit) -> Tot unit
assume val g1: nat -> Tot unit
[@(fail [19])]
let h1 = f1 (fun x -> g1 x) //should fail; x is not nat
