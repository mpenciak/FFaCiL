import Std.Data.Array.Basic

namespace Array

def last (ar : Array α) : Array α := ar.toSubarray.popFront.toArray

/-- Generates the array of nats from 0,...,n by a given n -/
def iota (n : Nat) : Array Nat :=
  Array.mk (List.range n) |>.push n

end Array