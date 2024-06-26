import FFC.MSM
import FFC.Pasta
import LSpec.Benchmark

open Benchmark

instance : FixedSize (Array $ Nat × Pallas.Point) where
  random size := do
    let mut answer := #[]
    let g ← get
    let mut g := g.down
    let mut n := 0
    let mut p := .infinity
    for _ in [:size] do
      (n, g) := randNat g 0 Vesta.q
      (p, g) := Random.random g
      answer := answer.push (n, p)

    return answer
  size ps := ps.size

-- def f : Array (Nat × Pallas.Point) → Pallas.Point := naiveMSM

def g : Array (Nat × Pallas.Point) → Pallas.Point := pippengerMSM

instance {α : Type _} : Ord $ Array α where
  compare as bs := compare as.size bs.size

def naiveBench : FunctionAsymptotics g where
  inputSizes := #[2^17]

set_option compiler.extract_closed false in
def main (args : List String) : IO UInt32 := do
  benchMain args naiveBench.benchmark
