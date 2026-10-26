import Jenga

/-!
Checks that the smooth-numbers lemma `Nat.mem_smoothNumbers'` is the *only* route by which
the Mathlib Erdős proof and Dirichlet reach Euclid's theorem: with it blocked, the walk
never arrives at `Nat.exists_infinite_primes`. Run with `lake env lean scripts/OnlyRoute.lean`.
-/
open Lean Meta

/-- closure that refuses to look inside `stop` -/
partial def reach (env : Environment) (root target : Name) (stop : NameSet) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if n == target then return true
    if seen.contains n || stop.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do stack := stack.push m
  return false

#eval show MetaM Unit from do
  let env ← getEnv
  let stop : NameSet := ({} : NameSet).insert ``Nat.mem_smoothNumbers' |>.insert ``Nat.mem_factoredNumbers'
  for p in [``Jenga.erdos, ``Jenga.dirichlet] do
    IO.println s!"{p}: reaches Euclid with smooth-number iff blocked? {reach env p ``Nat.exists_infinite_primes stop}"
  let stop2 : NameSet := ({} : NameSet).insert ``Nat.mem_smoothNumbers'
  for p in [``Jenga.erdos, ``Jenga.dirichlet] do
    IO.println s!"{p}: reaches Euclid with only mem_smoothNumbers' blocked? {reach env p ``Nat.exists_infinite_primes stop2}"
