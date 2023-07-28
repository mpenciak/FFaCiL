import Lake
open Lake DSL

package ffc

@[default_target]
lean_lib FFC

require YatimaStdLib from git
  "https://github.com/mpenciak/YatimaStdLib.lean" @ "df30d88d06e22d7c418fb8eee2996dd44cd1c547"

require LSpec from git
  "https://github.com/mpenciak/LSpec" @ "main"

lean_exe Tests.EllipticCurve
lean_exe Tests.GLV
lean_exe Tests.MSM
lean_exe Tests.Hash

lean_exe Benchmarks.GLV
lean_exe Benchmarks.MSM

