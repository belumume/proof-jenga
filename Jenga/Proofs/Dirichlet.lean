import Jenga.Statement

/-!
# Dirichlet (1837): primes in arithmetic progressions

Dirichlet proved that every progression `a, a + q, a + 2q, …` with `gcd(a, q) = 1`
contains infinitely many primes. Taking `q = 1` (the progression of all numbers)
gives our theorem. A sledgehammer: its proof uses L-functions and characters.
-/

namespace Jenga

theorem dirichlet : InfinitelyManyPrimes := by
  intro n
  have h := Nat.infinite_setOfPred_prime_and_eq_mod (q := 1) (a := 0) (isUnit_of_subsingleton _)
  obtain ⟨p, hp, hlt⟩ := h.exists_gt n
  exact ⟨p, hlt.le, hp.1⟩

end Jenga
