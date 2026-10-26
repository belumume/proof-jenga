import Jenga.Statement

/-!
# Euclid (c. 300 BC): multiply everything together and add one

Take `n! + 1`. Its smallest prime factor `p` cannot be `≤ n`: every number up to `n`
divides `n!`, so it would divide `(n! + 1) - n! = 1`, which no prime does.
So `p > n`. Ingredients: factorials, and "every number above 1 has a prime factor".
-/

namespace Jenga

theorem euclid : InfinitelyManyPrimes := by
  intro n
  -- `n! + 1 ≠ 1` because `n! > 0`, so its smallest factor is a prime.
  have hne : n.factorial + 1 ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  refine ⟨(n.factorial + 1).minFac, ?_, Nat.minFac_prime hne⟩
  by_contra hlt
  push Not at hlt
  have hp : (n.factorial + 1).minFac.Prime := Nat.minFac_prime hne
  -- `p ≤ n`, so `p ∣ n!`; also `p ∣ n! + 1`; hence `p ∣ 1`.
  have h1 : (n.factorial + 1).minFac ∣ n.factorial :=
    Nat.dvd_factorial hp.pos hlt.le
  have h2 : (n.factorial + 1).minFac ∣ 1 :=
    (Nat.dvd_add_right h1).mp (Nat.minFac_dvd _)
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

end Jenga
