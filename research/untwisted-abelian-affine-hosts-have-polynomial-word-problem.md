---
rg: 2
id: untwisted-abelian-affine-hosts-have-polynomial-word-problem
kind: claim
title: Finitely generated subgroups of untwisted affine hosts over any abelian base have polynomial word problem, in every characteristic
distinct_from:
  char-p-untwisted-affine-hosts-have-polynomial-word-problem: that is the case where A is an elementary abelian p-group, where linearization lands in GL_N(F_p[[t]]); this allows any abelian A (exponent p^m, mixed or characteristic zero, torsion-free), where no field linearization is available.
  commutative-algebra-affine-groups-have-polynomial-word-problem: that treats modules over finitely generated commutative algebras over finite fields and divides by an ordinary Gröbner basis; this needs finitely generated commutative Z-algebras, divides by a strong Gröbner basis over Z, and bounds coefficient growth.
  char-p-untwisted-self-similar-affine-groups-are-linear: that linearizes elementary abelian bases over F_p[[t]]; this uses the pro-e module over Z_e-hat[[t]] sketched in artifact §9.2 and never produces a field linearization.
artifacts:
  - research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md
---

**ESTABLISHED** by `untwisted-abelian-affine-hosts-polynomial-wp-proof`. No novelty
is claimed for the bare complexity bound. The new content is closing gap §9.2 of the
artifact, which named exactly this bound as missing. Not independently reviewed.

## Statement

**Setting (L_Z).**
- `A` is an abelian group, with no exponent or torsion assumption.
- `ν: A -> A` is an injective endomorphism, with `A/νA` finite and `∩_k ν^k A = 0`.
- `Γ <= Aut(A)` has a finite-index subgroup `Γ_0` that commutes with `ν`.

**Conclusions.**
1. Every finitely generated `H <= A x| Γ`, with finite generating set `B`, has word
   problem over `B` decidable in time `C*l^C + C`. The constant `C` depends on `H` and
   `B`. The algorithm is only claimed to exist; it is not claimed computable from
   `(A, ν, Γ)`.
2. All these word problems lie in the single class `F(g)`, `g(n) = 2^n`, of `(UWB1)`
   in `uniform-wp-bound-excludes-bh-universal-targets`. This conclusion has a second,
   independent proof through Aschenbrenner's degree bound for ideal membership over
   `Z`. That proof gives time `C*2^(C*l) + C` and does not use strong Gröbner bases.

## What it covers

- **Zaremsky's Example 4.7 in every characteristic.** Let `R` be a unital ring,
  commutative or not, with `x in R` not a zero divisor, `R/Rx` finite and
  `∩_k R x^k = 0`. Take any `Γ <= GL_n(R)`. Then `R^n x| Γ` satisfies (L_Z) with
  `ν = right multiplication by x` and `Γ_0 = Γ`. These are the hypotheses of
  `principal-ideal-affine-groups-are-self-similar`. Examples: `R = Z` with `x = 2`
  (the Brunner--Sidki affine groups `Z^n x| GL_n(Z)`); `R = (Z/p^m)[t]` with `x = t`;
  `R = Z_p` with `x = p`; and non-commutative orders such as `M_k(Z)` with `x = 2`.
- **Proposition 6.1 twists over any abelian base.** Its proof (artifact §6) uses no
  exponent assumption. So every Corollary 4.5 host `A x| Γ` with abelian `A` whose twist
  satisfies `σ^m(γ) = δγδ^(-1)` on a finite-index `Γ_0`, with `δ` preserving the
  filtration, satisfies (L_Z) with `ν = μ^m δ`.
- **Twists by a power.** If `Γ_0` commutes only with `ν^m`, replace `ν` by `ν^m`.

## Meaning for `fp-self-similar-groups-with-arbitrarily-hard-word-problem`

- No finitely generated subgroup of any (L_Z) host beats `T(n) = 2^n`. As a family,
  Zaremsky's untwisted affine hosts cannot witness the hole in any characteristic.
  By `complexity-bounded-host-classes-are-not-universal`, they are not universal hosts
  for groups with solvable word problem either.
- Attempt 2 of the hole dismissed these hosts by appeal to linearity. The dismissal is
  now proved in every characteristic, for every ring `R` in Example 4.7, and for every
  Proposition 6.1 twist.
- **What survives** among self-similar affine hosts:
  - genuinely twisted `σ` (artifact §6), where the linear parts act by infinite-state
    linear transducers and `Γ_0` commutes with no power of any `ν`;
  - non-abelian `A` in Corollary 4.5;
  - self-similar groups not of the form `A x| Γ`.

## Paradigm check

- **Why this succeeds where §9.2 stopped.** The linearization sketch of §9.2 was
  complete; only the word-problem bound over finitely generated commutative rings of
  mixed or zero characteristic was missing. The division method of
  `commutative-algebra-affine-groups-polynomial-word-problem-proof` transfers to `Z`
  once ordinary Gröbner bases are replaced by strong Gröbner bases, and the only new
  estimate is the coefficient growth of the reduction.
- **First falsifiable step.** The estimate that every strong-Gröbner reduction chain
  has at most `(D+1)^(m+N)` steps and multiplies the coefficient bound by at most
  `1 + K` per step. This is Step 5 of the proof.
- **Calibration.**
  - With `A` elementary abelian it recovers `char-p-untwisted-affine-hosts-have-polynomial-word-problem`.
  - For `Z^n x| GL_n(Z)` it agrees with the known logspace bound for linear groups over
    `Q` (Lipton--Zalcstein).
  - It says nothing about genuinely twisted hosts, which is where hard examples
    could still hide.
