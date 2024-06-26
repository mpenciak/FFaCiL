/-!
# Ring

This module defines the `Ring` and `Field` typeclasses and some of their instances.

**Note**: This is not a lawful `Ring`, and is not intended to be one. It simply encodes the arithmetic
doable in a ring.

## Yatima Standard Library

Parts of this file were migrated from the corresponding file in the Yatima Standard Library which is
no longer being maintained
-/
class Ring (R : Type) extends Add R, Mul R, Sub R, HPow R Nat R, BEq R, Coe Nat R where
  zero : R
  one : R

namespace Ring

instance {R : Type _} [Add R] [Mul R] [Sub R] [OfNat R (nat_lit 0)] [OfNat R (nat_lit 1)]
  [HPow R Nat R] [BEq R] [Coe Nat R] : Ring R where
  zero := 0
  one := 1

instance : Ring Nat where
  zero := 0
  one := 1
  coe := id

instance [Ring R] : OfNat R (nat_lit 0) where
  ofNat := zero

instance [Ring R] : OfNat R (nat_lit 1) where
  ofNat := one

instance [Ring R] : Neg R where
  neg x := 0 - x

instance [Ring R] : Inhabited R where
  default := 0

end Ring

class Field (K : Type) extends Ring K where
  inv : K → K

namespace Field

instance [Field K] : Div K where
  div a b := a * Field.inv b

postfix:max "⁻¹" => inv

end Field
