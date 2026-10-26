import Jenga.Statement

/-!
# Erdős, rebuilt without Euclid

The Jenga game shows that `Jenga.erdos` falls when you pull out Euclid's theorem
(`Nat.exists_infinite_primes`). That is a fact about the library, not about the idea:
Erdős's argument never needs Euclid. The dependency comes from one Mathlib lemma,
`Nat.mem_smoothNumbers'`, an "if and only if" whose *backward* direction needs a prime
outside any finite set (that is, infinitely many primes). The divergence proof only ever
uses the *forward* direction, which is elementary.

This file replays Mathlib's proof of the divergence of `∑ 1/p` (Michael Stoll's
formalization of the proof in *Proofs from THE BOOK*, `Mathlib/NumberTheory/SmoothNumbers.lean`
and `Mathlib/NumberTheory/SumPrimeReciprocals.lean`, Apache 2.0) with that one step
replaced by a forward-only lemma. `scripts/Deps.lean` then confirms that the result no
longer depends on `Nat.exists_infinite_primes`.

This is the "Jenga" move from Tao's talk: pull a block, and find another route.
-/

open Set Nat
open scoped Topology Finset

namespace Jenga.Rebuilt

/-- Forward direction of `Nat.mem_smoothNumbers'`, proved without infinitely many primes:
a prime dividing an `n`-smooth number is below `n`. -/
lemma lt_of_mem_smoothNumbers {n m p : ℕ} (h : m ∈ smoothNumbers n) (hp : p.Prime)
    (hd : p ∣ m) : p < n :=
  h.2 p ((mem_primeFactorsList h.1).mpr ⟨hp, hd⟩)

/-- `Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers`, using the forward-only lemma. -/
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : ℕ} (h : n ∈ smoothNumbers k) :
    ∃ s ∈ k.primesBelow.powerset, ∃ m, n = m ^ 2 * (s.prod id) := by
  obtain ⟨m, l, H₁, H₂⟩ := exists_sq_mul_squarefree n
  have hl : l ∈ smoothNumbers k := mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁)
  refine ⟨l.primeFactorsList.toFinset, ?_, m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp ↦ mem_primesBelow.mpr ⟨?_, (mem_primeFactors.mp hp).1⟩
    rw [mem_primeFactors] at hp
    exact lt_of_mem_smoothNumbers hl hp.1 hp.2.1
  rw [← H₁]
  congr
  simp only [toFinset_factors]
  exact (prod_primeFactors_of_squarefree H₂).symm

/-- `Nat.smoothNumbersUpTo_subset_image`, unchanged apart from the lemma above. -/
lemma smoothNumbersUpTo_subset_image (N k : ℕ) :
    smoothNumbersUpTo N k ⊆ Finset.image (fun (s, m) ↦ m ^ 2 * (s.prod id))
      (k.primesBelow.powerset ×ˢ (Finset.range (N.sqrt + 1)).erase 0) := by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem_powerset.mp hs, ?_, ?_⟩, hm.symm⟩
  · have := hm ▸ ne_zero_of_mem_smoothNumbers hn₂
    simp only [ne_eq, _root_.mul_eq_zero, sq_eq_zero_iff, not_or] at this
    exact this.1
  · rw [Nat.lt_succ_iff, le_sqrt']
    refine LE.le.trans ?_ (hm ▸ hn₁)
    nth_rw 1 [← mul_one (m ^ 2)]
    gcongr
    exact Finset.one_le_prod fun p hp ↦
      (prime_of_mem_primesBelow <| Finset.mem_powerset.mp hs hp).one_le

/-- `Nat.smoothNumbersUpTo_card_le`. -/
lemma smoothNumbersUpTo_card_le (N k : ℕ) :
    #(smoothNumbersUpTo N k) ≤ 2 ^ #k.primesBelow * N.sqrt := by
  convert (Finset.card_le_card <| smoothNumbersUpTo_subset_image N k).trans Finset.card_image_le
  simp only [Finset.card_product, Finset.card_powerset, Finset.mem_range, zero_lt_succ,
    Finset.card_erase_of_mem, Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

/-- `one_half_le_sum_primes_ge_one_div`. -/
lemma one_half_le_sum_primes_ge_one_div (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ (4 ^ (#k.primesBelow + 1)).succ.primesBelow \ k.primesBelow,
      (1 / p : ℝ) := by
  set m : ℕ := 2 ^ #k.primesBelow
  set N₀ : ℕ := 2 * m ^ 2 with hN₀
  let S : ℝ := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 / p : ℝ))
  suffices 1 / 2 ≤ S by
    convert this using 5
    rw [show 4 = 2 ^ 2 by simp, pow_right_comm]
    ring
  suffices 2 * N₀ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S by
    rwa [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add',
      cast_mul, cast_mul, cast_pow, cast_two,
      show (2 * (2 * m ^ 2) - m * (2 * m) : ℝ) = 2 * (2 * m ^ 2) * (1 / 2) by ring,
      mul_le_mul_iff_right₀ <| by positivity] at this
  calc (2 * N₀ : ℝ)
    _ = #((2 * N₀).smoothNumbersUpTo k) + #((2 * N₀).roughNumbersUpTo k) := by
        exact_mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ ≤ m * (2 * N₀).sqrt + #((2 * N₀).roughNumbersUpTo k) := by
        exact_mod_cast Nat.add_le_add_right (smoothNumbersUpTo_card_le (2 * N₀) k) _
    _ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S := by grw [roughNumbersUpTo_card_le']; norm_cast

/-- `not_summable_one_div_on_primes`: the sum of `1/p` over primes diverges. -/
theorem not_summable_one_div_on_primes :
    ¬ Summable (indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) := by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ 𝓝 0)
  specialize hk ({p | Nat.Prime p} ∩ {p | k ≤ p}) inter_subset_right
  rw [tsum_subtype, indicator_indicator, inter_eq_left.mpr fun n hn ↦ hn.1, mem_Iio] at hk
  have h' : Summable (indicator ({p | Nat.Prime p} ∩ {p | k ≤ p}) fun n ↦ (1 : ℝ) / n) := by
    convert h.indicator {n : ℕ | k ≤ n} using 1
    simp only [indicator_indicator, inter_comm]
  refine ((one_half_le_sum_primes_ge_one_div k).trans_lt <| LE.le.trans_lt ?_ hk).false
  convert!
    Summable.sum_le_tsum (primesBelow ((4 ^ (#k.primesBelow + 1)).succ) \ primesBelow k)
      (fun n _ ↦ indicator_nonneg (fun p _ ↦ by positivity) _) h' using
    2 with p hp
  obtain ⟨hp₁, hp₂⟩ := mem_ofPred_eq ▸ Finset.mem_sdiff.mp hp
  have hpp := prime_of_mem_primesBelow hp₁
  refine (indicator_of_mem ?_ fun n : ℕ ↦ (1 / n : ℝ)).symm
  exact ⟨hpp, by simpa [primesBelow, hpp] using hp₂⟩

end Jenga.Rebuilt

namespace Jenga

/-- Erdős's proof again, now standing on the rebuilt divergence result. -/
theorem erdosRebuilt : InfinitelyManyPrimes := by
  intro n
  by_contra h
  push Not at h
  have hfin : Set.Finite (Function.support
      (Set.indicator {p | p.Prime} (fun k : ℕ ↦ (1 : ℝ) / k))) := by
    refine (Set.finite_Iio n).subset fun k hk => ?_
    have hk' : k.Prime := by
      by_contra hnot
      exact hk (Set.indicator_of_notMem hnot _)
    by_contra hge
    exact h k (not_lt.mp hge) hk'
  exact Rebuilt.not_summable_one_div_on_primes (summable_of_hasFiniteSupport hfin)

end Jenga
