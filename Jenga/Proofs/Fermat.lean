import Jenga.Statement

/-!
# Goldbach (1730): Fermat numbers share no factors

The Fermat numbers `Fₖ = 2^(2^k) + 1` (3, 5, 17, 257, 65537, …) are pairwise coprime:
no prime divides two of them. So picking one prime factor from each gives infinitely
many *different* primes. No factorials anywhere; the key ingredient is coprimality.
-/

namespace Jenga

theorem fermat : InfinitelyManyPrimes := by
  intro n
  -- the smallest prime factor of the k-th Fermat number
  let f : ℕ → ℕ := fun k => (Nat.fermatNumber k).minFac
  have hprime : ∀ k, (f k).Prime := fun k =>
    Nat.minFac_prime (Nat.fermatNumber_ne_one k)
  -- different Fermat numbers give different primes, because they are coprime
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hcop := Nat.coprime_fermatNumber_fermatNumber hne
    have hi : f i ∣ Nat.fermatNumber i := Nat.minFac_dvd _
    have hj : f i ∣ Nat.fermatNumber j := hij ▸ Nat.minFac_dvd _
    exact (hprime i).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hi hj)
  -- infinitely many distinct primes, so one of them is past `n`
  obtain ⟨p, ⟨k, rfl⟩, hp⟩ := (Set.infinite_range_of_injective hinj).exists_gt n
  exact ⟨f k, hp.le, hprime k⟩

end Jenga
