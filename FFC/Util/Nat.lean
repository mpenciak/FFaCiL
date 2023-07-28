import Std.Data.Nat.Basic

/-!
# Nat

This module extends the functionality of the built in `Nat` type.

## Yatima Standard Library

Parts of this file were migrated from the corresponding file in the Yatima Standard Library which is
no longer being maintained
-/

namespace Nat

-- Shifts `n` to the left by `m+1`, adding 1 on each shift.
def shiftLeft1 : Nat → Nat → Nat
  | n, 0   => n
  | n, m+1 => shiftLeft1 (2*n+1) m

/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
partial def xgcdAux : Nat → Int → Int → Nat → Int → Int → Nat × Int × Int
  | 0, _, _, r', s', t' => (r', s', t')
  | r, s, t, r', s', t' =>
    let q := r' / r
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t

/--
Use the extended GCD algorithm to generate the `a` and `b` values
satisfying `gcd x y = x * a + y * b`.
-/
def xgcd (x y : Nat) : Int × Int := (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : Nat) : Int := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : Nat) : Int := (xgcd x y).2

def quotRem (a : Nat) (b : Nat) : Nat × Nat :=
  (a / b, a % b)

theorem div2_lt (h : n ≠ 0) : n / 2 < n := by
  match n with
  | 1   => decide
  | 2   => decide
  | 3   => decide
  | n+4 =>
    rw [div_eq, if_pos]
    refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))
    exact @div2_lt (n + 2) (by simp_arith)
    simp_arith

/--
Evaluates `b^e mod m`
-/
def powMod (m b e : Nat) : Nat :=
  let rec go (b e r : Nat) : Nat :=
    if h : e = 0 then r
    else
      let e' := e / 2
      have : e' < e :=
      by exact Nat.div2_lt h
      if e % 2 = 0
      then go ((b*b) % m) e' r              -- TODO : Use Montgomery multiplication here to avoid
      else go ((b*b) % m) e' ((r*b) % m)    --        calculating `mod` at every step
  go b e 1

/-- A legendre symbol denotes the value of `a^((p - 1)/2) mod p` -/
def legendre (a : Nat) (p : Nat) : Nat :=  -- TODO : Use a pre-calculated `(p - 1) / 2 ` AddChain
  powMod p a ((p - 1) / 2)                 --        and AddChain `fastExp` here

/-- Returns `(s, d)` when `n = 2 ^ s * d` with `d` odd -/
def get2Adicity (n : Nat) : Nat × Nat :=
  let rec loop (m acc : Nat) :=
    match h : m with
    | 0 | 1 => (acc, 1)
    | _ + 1 => 
      have : m / 2 < m := Nat.bitwise_rec_lemma (h ▸ Nat.succ_ne_zero _)
      if m % 2 ==0 then loop (m / 2) (acc + 1) else (acc, m)
  loop n 0

/--
The Tonelli-Shanks algorithm solves the equation having the form
`x^2 = n mod p`, whenever it exists
Ported from this:
https://rosettacode.org/wiki/Tonelli-Shanks_algorithm#Python
-/
def tonelli (n : Nat) (p : Nat) : Option (Nat × Nat) :=
  if legendre n p != 1 then none else Id.run do
  let (s, q) := get2Adicity (p - 1)
  if s == 1 then
    let r := powMod p n ((p + 1) / 4)
    return some (r, p - r)
  let mut zMax := 2
  for z in [2 : p] do
    zMax := z
    if p - 1 == legendre z p then break
  let mut c := powMod p zMax q
  let mut r := powMod p n $ (q + 1) / 2  -- TODO : Group together these two exponetiations into a
  let mut t := powMod p n q              --        bached Exp to avoid re-calculating some powers
  let mut m := s
  while (t - 1) % p != 0 do
    let mut t2 := (t * t) % p
    let mut iMax := 1
    for i in [1:m] do
      iMax := i
      if (t2 - 1) % p == 0 then
        break
      t2 := (t2 * t2) % p
    let b := powMod p c (2^(m - iMax - 1))
    r := (r * b) % p
    c := (b * b) % p
    t := (t * c) % p
    m := iMax
  return some (r, p - r)

end Nat