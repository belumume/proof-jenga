import Jenga.Statement

/-!
# Bertrand's postulate (Chebyshev 1852, Erdős 1932)

For every `n ≥ 1` there is a prime `p` with `n < p ≤ 2n`. Infinitely many primes is an
immediate corollary: it even tells you *where* the next prime is. A much stronger
theorem doing a small job; its proof estimates central binomial coefficients.
-/

namespace Jenga

theorem bertrand : InfinitelyManyPrimes := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨2, Nat.zero_le _, Nat.prime_two⟩
  · obtain ⟨p, hp, hlt, -⟩ := Nat.exists_prime_lt_and_le_two_mul n hn.ne'
    exact ⟨p, hlt.le, hp⟩

end Jenga
