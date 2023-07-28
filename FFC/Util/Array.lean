import Std.Data.Array.Basic

/-!
# Array Utilities

This module defines additional functionality for `Array` not present in std4

## Yatima Standard Library

Parts of this file were migrated from the corresponding file in the Yatima Standard Library which is
no longer being maintained
-/
namespace Array

def last (ar : Array α) : Array α := ar.toSubarray.popFront.toArray

/-- Generates the array of nats from 0,...,n by a given n -/
def iota (n : Nat) : Array Nat :=
  Array.mk (List.range n) |>.push n

end Array