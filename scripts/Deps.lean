import Jenga

/-!
Computes what each proof *really* depends on, by walking the kernel terms.

For every proof we collect the transitive closure of constants its proof term
mentions (through the bodies of the theorems and definitions it uses), then report
which of the "blocks" (named ideas from Mathlib) are inside that closure, which axioms
it rests on, and how big the closure is. Run with:

    lake env lean scripts/Deps.lean > docs/data.json
-/

open Lean Meta

/-- All constants reachable from `root` through types and values. -/
partial def depClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      for m in ci.getUsedConstantsAsSet do
        unless seen.contains m do stack := stack.push m
  return seen

def proofs : List Name :=
  [``Jenga.euclid, ``Jenga.fermat, ``Jenga.bertrand, ``Jenga.erdos, ``Jenga.erdosRebuilt, ``Jenga.dirichlet]

def blocks : List Name :=
  [ ``Nat.exists_infinite_primes
  , ``Nat.minFac_prime
  , ``Nat.factorial
  , ``Nat.coprime_fermatNumber_fermatNumber
  , ``Nat.centralBinom
  , ``Nat.exists_prime_lt_and_le_two_mul
  , ``Nat.smoothNumbers
  , ``Real
  , ``Real.log
  , ``Complex
  , ``Summable
  , ``ZMod
  , ``DirichletCharacter
  , ``LSeries
  , ``Classical.choice ]

/-- Breadth-first search from `root`, remembering who first mentioned each constant,
so we can show *why* a proof depends on a block (a shortest chain of uses). -/
def parents (env : Environment) (root : Name) : Std.HashMap Name Name := Id.run do
  let mut par : Std.HashMap Name Name := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut frontier : Array Name := #[root]
  while frontier.size > 0 do
    let mut next : Array Name := #[]
    for n in frontier do
      if let some ci := env.find? n then
        -- sort for a deterministic choice of chain
        let used := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
        for m in used do
          unless seen.contains m do
            seen := seen.insert m
            par := par.insert m n
            next := next.push m
    frontier := next
  return par

def chain (par : Std.HashMap Name Name) (root target : Name) : List Name := Id.run do
  let mut out : List Name := [target]
  let mut cur := target
  for _ in [0:1000] do
    if cur == root then break
    match par.get? cur with
    | some p => out := p :: out; cur := p
    | none => break
  return out

def axiomsOf (s : NameSet) : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].filter s.contains

def jsonStr (n : Name) : String := (Json.str n.toString).compress

#eval show MetaM Unit from do
  let env ← getEnv
  for b in blocks do
    unless env.contains b do throwError "unknown block {b}"
  let mut rows : Array String := #[]
  for p in proofs do
    let s := depClosure env p
    let used := blocks.filter s.contains
    let ax := axiomsOf s
    let par := parents env p
    let why := used.map fun b =>
      "\"" ++ b.toString ++ "\":[" ++ ",".intercalate ((chain par p b).map jsonStr) ++ "]"
    rows := rows.push <|
      "{\"proof\":" ++ jsonStr p ++
      ",\"closureSize\":" ++ toString s.size ++
      ",\"blocks\":[" ++ ",".intercalate (used.map jsonStr) ++ "]" ++
      ",\"axioms\":[" ++ ",".intercalate (ax.map jsonStr) ++ "]" ++
      ",\"why\":{" ++ ",".intercalate why ++ "}}"
  IO.println ("{\"blocks\":[" ++ ",".intercalate (blocks.map jsonStr) ++ "],\"proofs\":[\n" ++
    ",\n".intercalate rows.toList ++ "\n]}")
