import Std.Data.Nat.Basic

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

namespace Int

open Nat in
/--
Return `(x, y, g)` where `g` is the greatest common divisor of `a` and `b`, and `x`, `y` satisfy

`x * a + y * b = g`
-/
def gcdExtNat (a : Nat) (b : Nat) : Int × Int × Int :=
  match h : b with
    | 0 => (1, 0, a)
    | k + 1 =>
      let p := quotRem a b
      let q := p.1
      let r := p.2
      have : r < k.succ := by
        have h2 := k.succ_ne_zero
        rw [← h] at *
        apply Nat.mod_lt
        exact Nat.zero_lt_of_ne_zero h2
      let (s, t, g) := gcdExtNat b r
      (t, s - q * t, g)
  termination_by _ => b

def gcdExt (a : Int) (b : Int) : Int × Int × Int :=
  gcdExtNat (Int.natAbs a) (Int.natAbs b)

def modInv (a : Int) (m : Int) : Int :=
  let (i, _, g) := Int.gcdExt a m
  let mkPos (x : Int) := if x < 0 then x + m else x
  if g == 1 then mkPos i else 0

section bitwise

open Nat

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
  | .negSucc m, .ofNat n   => .negSucc $ shiftLeft1 m n
  | .negSucc m, .negSucc n => .negSucc $ m >>> (n+1)

def shiftRight m n := shiftLeft m (-n)

instance : AndOp Int := ⟨land⟩
instance : OrOp Int := ⟨lor⟩
instance : Xor Int := ⟨lxor⟩
instance : ShiftLeft  Int := ⟨shiftLeft⟩
instance : ShiftRight Int := ⟨shiftRight⟩

/-- Turn a negative integer into a positive by taking its bit representation
and interpreting it as unsigned. `size` is the number of bits to assume. -/
def unsign (i : Int) (size : Nat := 64) : Int :=
  match i with
  | .ofNat m => m
  | .negSucc _ => i + ((2 : Int) ^ size)

end bitwise

end Int