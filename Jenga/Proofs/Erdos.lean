import Jenga.Statement

/-!
# Euler (1737), in Erdős's form: the sum of 1/p diverges

`1/2 + 1/3 + 1/5 + 1/7 + 1/11 + …` grows without bound. A finite list of primes would
give a finite sum, so there must be infinitely many. This routes a statement about
whole numbers through real numbers and infinite series.
-/

namespace Jenga

theorem erdos : InfinitelyManyPrimes := by
  intro n
  by_contra h
  push Not at h
  -- every prime is below `n`, so the terms `1/p` are zero from `n` on …
  have hfin : Set.Finite (Function.support
      (Set.indicator {p | p.Prime} (fun k : ℕ ↦ (1 : ℝ) / k))) := by
    refine (Set.finite_Iio n).subset fun k hk => ?_
    have hk' : k.Prime := by
      by_contra hnot
      exact hk (Set.indicator_of_notMem hnot _)
    by_contra hge
    exact h k (not_lt.mp hge) hk'
  -- … so the sum is finite, contradicting divergence
  exact not_summable_one_div_on_primes (summable_of_hasFiniteSupport hfin)

end Jenga
