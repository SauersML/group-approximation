---
rg: 2
id: kourovka-21-119-answers-need-infinite-vcd
kind: claim
title: Any group answering Kourovka 21.119 is of type F_∞ with no torsion-free finite-index subgroup of finite cohomological dimension; for groups all of whose proper quotients are abelian the finite-index subgroups add nothing, so F and every F_{n,∞} fail
distinct_from:
  zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1: that is Kourovka 21.146 (embedding F_{n-1} groups in F_n groups); this is Schesler's 21.119 on kernels of characters of finite-index subgroups.
artifacts:
  - research/artifacts/gq-bh-kourovka-scout-candidates-2026-09-19.md
---

**ESTABLISHED** (lane proof, elementary; referee PASS by bh-ref-f, e733763d78, repairs applied). Kourovka 21.119 itself
stays **OPEN**; this node records what any answer must look like.

## The problem

Kourovka Notebook arXiv:1401.0300v46, p. 185, Problem 21.119 (E. Schesler), verbatim:

> Does there exist a group G that contains a family (G_n)_{n∈ℕ} of finite-index subgroups
> such that for every n there is a homomorphism f_n : G_n → ℤ whose kernel is of type F_n,
> but not of type F_{n+1}?

Main has no other node on 21.119.

## Claim

Let `G` answer 21.119. Then:

1. `G` is of type `F_∞`, and every `f_n` is nonzero.
2. No finite-index subgroup of `G` is torsion-free of finite cohomological dimension.
3. `G` is not commensurable with Thompson's group `F`.
4. **Reduction for groups with only abelian proper quotients.** Let `G_0` be an infinite
   group in which every proper quotient is abelian and `[G_0, G_0]` is nonabelian. Then a group
   commensurable with `G_0` answers 21.119 iff the characters `G_0 → ℤ` alone have kernels of
   every finite finiteness length. The finite-index subgroups contribute nothing new.
5. `G` is not commensurable with any generalized Thompson group `F_{n,∞}` (`n ≥ 2`).

**Groups excluded by item 2.** Item 2 excludes every virtually torsion-free group of finite
vcd. Examples:

- lattices in linear Lie groups, S-arithmetic groups in characteristic 0 and their
  subgroups, all virtually torsion-free by Selberg's lemma. Lattices in non-linear Lie groups
  are not covered: Deligne's non-residually-finite lattices in covers of `Sp_{2n}(ℝ)` need
  not be virtually torsion-free;
- virtually torsion-free hyperbolic groups;
- virtually special groups, and right-angled Artin and Coxeter groups;
- mapping class groups, Out(F_n) and Aut(F_n);
- solvable groups of type `F_∞`. By Kropholler's theorem these are constructible, hence
  virtually torsion-free of finite vcd.

**Groups excluded by other means.** Simple groups, such as Thompson's `T` and `V` and the
Brin–Thompson groups `nV`, have no proper finite-index subgroups. Item 3 excludes `F`.

## Proof

**Item 1.**
- Finiteness properties `F_m` are commensurability invariants: a group is `F_m` iff some
  finite-index subgroup is.
- If `f_n = 0`, then `G_n = ker f_n` is `F_n` but not `F_{n+1}`, and so is `G`. That can hold
  for at most one `n`.
- For every other `n`, `G_n` is an extension of the `F_n` group `ker f_n` by `ℤ`, so `G_n`,
  and hence `G`, is `F_n`. So `G` is `F_n` for infinitely many `n`, hence `F_∞`.
- In particular `G` is `F_{n+1}` for every `n`, so no `f_n` is zero.

**Item 2.**
- Let `G' ≤ G` be torsion-free of finite index with `cd G' = d < ∞`. Fix `n ≥ max(d, 2)`.
- `K = ker f_n ∩ G'` has finite index in `ker f_n`. So `K` is `F_n` but not `F_{n+1}`, and
  `cd K ≤ d ≤ n`.
- A group of type `FP_n` with `cd ≤ n` is of type `FP`. In a partial resolution of `ℤ` by
  finitely generated free modules of length `n − 1`, the next kernel is finitely generated
  (by `FP_n`) and projective (by `cd ≤ n` and Schanuel's lemma). See Brown, *Cohomology of
  Groups*, VIII.6.
- So `K` is `FP_∞`. It is also finitely presented, since it is `F_n` with `n ≥ 2`.
- Finitely presented and `FP_{n+1}` means `F_{n+1}` (Brown VIII.7), a contradiction.

**Item 3.**
- Let `H ≤ F` have finite index.
  - `[F,F]` is infinite and simple, so it has no proper finite-index subgroups, and
    `[F,F] ≤ H`.
  - `[F,F]` is perfect, so `[H,H] = [F,F]` and `H^{ab} ≅ H/[F,F]`, a finite-index subgroup
    of `F^{ab} ≅ ℤ²`.
- So every homomorphism `H → ℤ` is the restriction `χ|_H` of some `χ : F → ℚ` with
  `χ(H) ⊆ ℤ`. Its kernel `ker χ ∩ H` has finite index in `ker χ`.
- By Bieri–Geoghegan–Kochloukova, *The Sigma invariants of Thompson's group F*,
  arXiv:0807.5138 (Groups Geom. Dyn. 2010), Theorem A (read through the arXiv HTML):
  > Σ¹(F) consists of all points of S(F) except [χ₀] and [χ₁]. The points of S(F) lying in
  > the open convex hull of [χ₀] and [χ₁], i.e. in the shorter interval, are in Σ¹(F) but
  > are not in Σ²(F). The other (longer) open interval between [χ₀] and [χ₁] is the set
  > Σ^∞(F).
- By Bieri–Renz, `ker χ` is `F_m` iff `±[χ] ∈ Σ^m(F)`. So a nonzero `χ` has kernel:
  - not finitely generated, if `[χ] = ±[χ₀]` or `±[χ₁]`;
  - `F_1` but not `F_2`, if `±[χ]` meets the shorter interval;
  - `F_∞`, otherwise.
- So only the finiteness lengths `0`, `1` and `∞` occur for characters of finite-index
  subgroups of `F`.
- Now suppose `A ≤ G` has finite index and is isomorphic to a finite-index subgroup of `F`.
  - For `n ≥ 2`, the restriction of `f_n` to `G_n ∩ A` is nonzero.
  - Its kernel `ker f_n ∩ A` has finite index in `ker f_n`, so it is `F_n` but not `F_{n+1}`.
  - This contradicts the previous bullet, since `G_n ∩ A` is isomorphic to a finite-index
    subgroup of `F`.

**Item 4.** Put `D = [G_0, G_0]`.
- **`D` is perfect.**
  - `[D, D]` is characteristic in `D`, hence normal in `G_0`.
  - If `[D, D] ≠ 1`, then `G_0/[D,D]` is a proper quotient, hence abelian, so
    `D ≤ [D, D]`.
  - `[D, D] = 1` is impossible, since `D` is nonabelian.
- **Every finite-index `H ≤ G_0` contains `D`.** The normal core of `H` is a nontrivial
  normal subgroup (as `G_0` is infinite), so `G_0/core` is abelian and `D ≤ core ≤ H`.
- **So characters of `H` come from `G_0`.**
  - `D = [D, D] ≤ [H, H] ≤ D`, so `H^{ab} = H/D`, a finite-index subgroup of `G_0/D`.
  - So every nonzero `f : H → ℤ` is `χ|_H` for a unique `χ : G_0 → ℚ` with `χ(H) ⊆ ℤ`.
  - Its kernel `ker χ ∩ H` has finite index in `ker χ`, so both kernels have the same
    finiteness properties. Rescaling `χ` to a map `G_0 → ℤ` does not change its kernel.
- **Passing to commensurable groups.** This is the argument of item 3 with `F` replaced by
  `G_0`.
- **Both directions.** The converse direction takes `G_n = G_0` for every `n`. ∎

**Item 5.** Zaremsky, *On the Σ-invariants of generalized Thompson groups and Houghton
groups*, arXiv:1502.02620v1, read at source (p. 2), records two facts:
- "every proper quotient of F_n is abelian [Bro87a, BG98]", where `F_n = F_{n,∞}`;
- **Theorem A:** "For any n, m ≥ 2, we have Σ^m(F_n) = Σ^2(F_n)."

So every kernel of a character of `F_{n,∞}` is either `F_∞` or not finitely presented.
Item 4 then excludes the commensurability class. For `n = 2` this is item 3 again. ∎

## What an answer needs

**The two regimes.** Item 4 splits the search into two regimes, and each points to one
precise question.

- **Thompson-like groups**, whose proper quotients are all abelian. Here the question is
  whether one `F_∞` group has infinitely many distinct finite levels
  `Σ^m ⊋ Σ^{m+1}` on its own character sphere, each witnessed by rational points.
  - Every computed case stabilizes at `m = 2`: `F` (BGK) and `F_{n,∞}` (Zaremsky).
  - So a candidate needs a character sphere whose Σ^m do not stabilize.
- **Profinitely rich groups.** These need infinitely many finite-index subgroups with new
  characters.
  - By item 2 they need infinite vcd, or torsion without a torsion-free finite-index
    subgroup.
  - `F_∞` groups of infinite vcd in Kropholler's class `H𝔉` are not expected to exist.
    Kropholler asked whether `FP_∞` groups in `H𝔉` have finite vcd; not rechecked here.
  - So candidates lie outside `H𝔉`, which is the territory of Kourovka 21.140.

**Further notes.**

- An `F_∞` group of infinite vcd, or one that is not virtually torsion-free, in which
  finite-index subgroups carry characters of every finite finiteness length.
- BGK Theorem B gives subgroups of `F` of type `F_{m−1}` and not `FP_m` for every `m`,
  through infinite-index subgroups such as copies of `F^m`. 21.119 asks for the same
  phenomenon at finite index.
- A candidate would be an `F_∞` group commensurable with arbitrarily large direct powers of
  a Thompson-like group. Characters that are generic on each factor would then have kernel
  lengths growing with the number of factors, by the product formula wherever it holds.
  None is known to the lane.
