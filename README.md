# Proof Jenga

An interactive page that treats Mathlib as a Jenga tower. Six Lean proofs that there are
infinitely many primes stand on it. Pull a block (an idea such as Euclid's theorem,
factorials, the real numbers or the axiom of choice) and the page shows which proofs fall.

**Play it:** https://belumume.github.io/proof-jenga/

Nothing on the page is hand-labelled. Every "this proof uses that idea" fact, and every
"why?" chain, is computed from the kernel terms of the compiled proofs.

The idea comes from Terence Tao's *Math 2.0* talk (Caltech, 2026), which argues
that once proofs are cheap to produce and check, the interesting work moves to exploring
how results depend on one another.

## The six proofs

All prove the same statement, `Jenga.InfinitelyManyPrimes` (`∀ n, ∃ p, n ≤ p ∧ p.Prime`),
in `Jenga/Proofs/`:

| Proof | Idea | Kernel closure |
|---|---|---|
| `euclid` | a prime factor of `n! + 1` | 3,231 constants |
| `fermat` | Fermat numbers are pairwise coprime | 6,404 |
| `erdos` | `∑ 1/p` diverges (Mathlib) | 15,812 |
| `erdosRebuilt` | the same argument, rebuilt without Euclid | 16,076 |
| `bertrand` | a prime between `n` and `2n` | 31,226 |
| `dirichlet` | primes in arithmetic progressions | 67,435 |

None uses `sorry`.

## The finding

Mathlib's divergence of `∑ 1/p` (`not_summable_one_div_on_primes`) and Dirichlet's
theorem both depend on Euclid's `Nat.exists_infinite_primes`, though neither argument
needs it. The only route is `Nat.mem_smoothNumbers'`, an iff whose backward direction
uses infinitely many primes, while the proofs only use the forward direction
(`scripts/OnlyRoute.lean` checks that blocking that lemma cuts every path).
`Jenga/Proofs/ErdosRebuilt.lean` replays the divergence proof with a forward-only lemma,
and the dependency script confirms it no longer reaches Euclid or factorials.

## Build

```sh
lake exe cache get        # Mathlib build cache
lake build                # checks all six proofs
lake env lean scripts/Deps.lean > docs/data.json
python3 scripts/build_site.py   # writes docs/index.html
```

`docs/index.html` is one self-contained file. Open it in a browser.

## Limits

The closure walks every constant a proof term mentions, through the bodies of the
definitions and theorems it uses. That over-approximates what an argument *needs*:
it counts what this particular library happens to route through. That gap is the point
of the game, and the reason a rebuilt proof can stand where the original falls.

## Credits

Mathlib (Apache 2.0) and its authors; the rebuilt divergence proof follows Michael
Stoll's formalization. Not affiliated with Terence Tao, Caltech or Mathlib. Built with
AI assistance and checked by the Lean kernel.
