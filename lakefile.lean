import Lake
open Lake DSL

package ffc

@[default_target]
lean_lib FFC

require LSpec from git
  "https://github.com/mpenciak/LSpec" @ "main"

lean_exe Tests.EllipticCurve
lean_exe Tests.GLV
lean_exe Tests.MSM
lean_exe Tests.Hash

lean_exe Benchmarks.GLV
lean_exe Benchmarks.MSM

