import FFC.Util.Nat
import FFC.Util.Ring

/-!
# Int

This module extends the functionality of the built in `Int` type.

## Yatima Standard Library

Parts of this file were migrated from the corresponding file in the Yatima Standard Library which is
no longer being maintained
-/
open Nat

namespace Int


/--
Return `(x, y, g)` where `g` is the greatest common divisor of `a` and `b`, and `x`, `y` satisfy

`x * a + y * b = g`
-/
def gcdExtNat (a : Nat) (b : Nat) : Int × Int × Nat :=
  match h : b with
    | 0 => (1, 0, a)
    | k + 1 =>
      let p := quotRem a b
      let q := p.1
      let r := p.2
      have : r < k.succ := by
        have h2 := k.succ_ne_zero
        rw [← h] at *
        apply mod_lt
        exact zero_lt_of_ne_zero h2
      let (s, t, g) := gcdExtNat b r
      (t, s - q * t, g)

def gcdExt (a : Int) (b : Int) : Int × Int × Nat :=
  gcdExtNat (Int.natAbs a) (Int.natAbs b)

def modInv (a : Int) (m : Int) : Int :=
  let (x, _, g) := Int.gcdExt a m
  if g == 1 then
    if a < 0 then -x else x
  else
    0

section bitwise

/-! Some bitwise arithmetics for `Int`s, assuming twos complement. -/

def bdiff a b := a && not b

def bitwise (f : Bool → Bool → Bool) (m' n' : Int) : Int :=
  let go f' m n :=
    if f' false false
      then .negSucc $ Nat.bitwise (fun x y => not $ f' x y) m n
      else .ofNat   $ Nat.bitwise f' m n
  match m', n' with
  | .ofNat m, .ofNat n     => go f m n
  | .ofNat m, .negSucc n   => go (fun x y => f x (not y)) m n
  | .negSucc m, .ofNat n   => go (fun x y => f (not x) y) m n
  | .negSucc m, .negSucc n => go (fun x y => f (not x) (not y)) m n

def lnot : Int → Int
  | .ofNat m   => .negSucc m
  | .negSucc m => .ofNat m

def land : Int → Int → Int
  | .ofNat m,   .ofNat n   => m &&& n
  | .ofNat m,   .negSucc n => .ofNat $ Nat.bitwise bdiff m n
  | .negSucc m, .ofNat n   => .ofNat $ Nat.bitwise bdiff n m
  | .negSucc m, .negSucc n => .negSucc $ m ||| n

def lor : Int → Int → Int
  | .ofNat m,   .ofNat n   => m ||| n
  | .ofNat m,   .negSucc n => .negSucc $ Nat.bitwise bdiff n m
  | .negSucc m, .ofNat n   => .negSucc $ Nat.bitwise bdiff m n
  | .negSucc m, .negSucc n => .negSucc $ m &&& n

def lxor : Int → Int → Int
  | .ofNat m,   .ofNat n   => m ^^^ n
  | .ofNat m,   .negSucc n => .negSucc $ m ^^^ n
  | .negSucc m, .ofNat n   => .negSucc $ m ^^^ n
  | .negSucc m, .negSucc n => m ^^^ n

def shiftLeft : Int → Int → Int
  | .ofNat m,   .ofNat n   => m <<< n
  | .ofNat m,   .negSucc n => m >>> (n+1)
  | .negSucc m, .ofNat n   => .negSucc $ Nat.shiftLeft1 m n
  | .negSucc m, .negSucc n => .negSucc $ m >>> (n+1)

instance : AndOp Int := ⟨land⟩
instance : OrOp Int := ⟨lor⟩
instance : Xor Int := ⟨lxor⟩
instance : ShiftLeft Int := ⟨shiftLeft⟩

/-- Turn a negative integer into a positive by taking its bit representation
and interpreting it as unsigned. `size` is the number of bits to assume. -/
def unsign (i : Int) (size : Nat := 64) : Int :=
  match i with
  | .ofNat m => m
  | .negSucc _ => i + ((2 : Int) ^ size)

end bitwise

instance : Ring Int where
  coe n := n
  zero := 0
  one := 1

end Int
