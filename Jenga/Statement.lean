import Mathlib

/-!
# The theorem we play Jenga with

"There are infinitely many primes", stated as: past any number `n` there is a prime.
Every proof in `Jenga/Proofs/` proves exactly this statement, and none of them may
use Mathlib's own `Nat.exists_infinite_primes` directly (a proof that just cites the
theorem is not a proof of it). Whether a proof uses it *indirectly*, through some
bigger theorem it relies on, is one of the things the Jenga game reveals.
-/

namespace Jenga

/-- Past any natural number there is a prime. -/
def InfinitelyManyPrimes : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ p.Prime

end Jenga
