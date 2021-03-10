import Gaea.Logic
import Gaea.Logic.Notation
import Gaea.Math.Syntax
import Gaea.Peano.Nat

open Gaea.Logic
open Gaea.Math.Shorthand (S)
open Gaea.Peano.Shorthand (nat)

namespace Gaea.Peano

class Eq {L : Logic} (N : Nat L) extends Logic.Eq L.prop N.form :=
  (nat_eq : (a b : N.form) -> 
    L.proof (nat b) -> L.proof (a = b) -> L.proof (nat a))
  (eq_nat_refl : (x : N.form) -> 
    L.proof (nat x) -> L.proof (x = x))
  (eq_nat_symm : (x y : N.form) -> 
    L.proof (nat x) -> L.proof (nat y) -> 
    L.proof (x = y) -> L.proof (y = x))
  (eq_nat_trans : (x y z : N.form) -> 
    L.proof (nat x) -> L.proof (nat y) -> L.proof (nat z) ->
    L.proof (x = y) -> L.proof (y = z) -> L.proof (x = z))

class Zero {L : Logic} (N : Nat L) extends Math.Zero N.form :=
  (nat_zero : L.proof (nat zero))

class Succ' {L : Logic} (N : Nat L) 
  [Logic.Eq L.prop N.form] [Math.Zero N.form] 
  extends Math.Succ N.form :=
  (nat_succ_nat : (n : N.form) ->
    L.proof (nat n) -> L.proof (nat (S n)))
  (nat_succ_subst : (m n : N.form) ->
    L.proof (nat n) -> L.proof (nat n) -> 
    L.proof (m = n) -> L.proof (S m = S n))
  (nat_succ_inj : (m n : N.form) ->
    L.proof (nat n) -> L.proof (nat n) -> 
    L.proof (S m = S n) -> L.proof (m = n))

class Succ {L : Logic} (N : Nat L) 
  [False L.prop] [Logic.Eq L.prop N.form] [Math.Zero N.form] 
  extends Succ' N :=
  (nat_succ_zero_false : (n : N.form) ->
    L.proof (nat n) -> L.proof (succ n = 0) -> L.proof false)

class Induction {L : Logic} (N : Nat L) 
  [If L.prop] [Math.Zero N.form] [Math.Succ N.form] :=
  (nat_induction := 
    (f : N.pred) -> L.proof (f 0) -> 
    ((n : N.form) -> L.proof (nat n) -> (L.proof (f n) -> L.proof (f (S n)))) ->
    ((n : N.form) -> L.proof (nat n) -> (L.proof (f n))))

class Add {L : Logic} (N : Nat L) 
  [Logic.Eq L.prop N.form] [Math.Zero N.form] [Math.Succ N.form] 
  extends _root_.Add N.form :=
  (add_nat_zero_eq_nat : (a b : N.form) ->
    L.proof (nat a) -> L.proof (nat b) -> L.proof (a + 0 = a))
  (add_nat_succ_eq_succ : (a b : N.form) ->
    L.proof (nat a) -> L.proof (nat b) -> L.proof (a + S b = S (a + b)))

end Gaea.Peano
