---
rg: 2
id: aleph-one-eg-is-equivalent-to-relative-countable-eg
kind: claim
title: The Eilenberg--Ganea conjecture for groups of cardinality at most aleph_1 is equivalent to the relative countable statement REG_omega, and an aleph_1-sized counterexample can be taken to be an aleph_1-fold amalgam of one countable pair
distinct_from:
  relative-countable-eg-gives-eg-for-aleph-one-groups: that proves one direction (REG_omega implies EG up to aleph_1) and records that no converse was known; this supplies the converse, making the reduction two-directional.
  relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two: that is the per-pair engine (realizability of H <= G iff gd of the aleph_1-fold amalgam is 2); this is the global equivalence and the resulting form of a minimal counterexample.
  eilenberg-ganea-conjecture: that is the conjecture for all cardinalities; this concerns only cardinality at most aleph_1 and states an equivalence, not a proof.
artifacts: []
---

**ESTABLISHED** through `aleph-one-eg-is-equivalent-to-relative-countable-eg-proof`. Unreviewed. Both directions are proved.

## Statement

Recall **REG_ω**: for all countable `H ≤ G` with `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`, every 2-dimensional `K(H,1)` is a subcomplex of a 2-dimensional `K(G,1)`, inducing `H ≤ G`.

The following are equivalent.

- **(i)** REG_ω.
- **(ii)** Every group of cardinality `≤ ℵ_1` with `cd = 2` has a 2-dimensional `K(·,1)`.
- **(iii)** For every countable pair `H ≤ G` with `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`, the amalgam `Γ_{ℵ_1}(H,G) = ⁎_H {G_ξ : ξ < ω_1}` has `gd ≤ 2`.

## Minimal-counterexample biography (inverter reading)

Suppose the Eilenberg--Ganea conjecture fails for some group of size `≤ ℵ_1`. Then it fails for some `Γ = Γ_{ℵ_1}(H,G)` with `(H,G)` a countable pair such that:

1. `cd G ≤ 2`, `pd I_{G/H} ≤ 1` and `cd Γ = 2`;
2. `H` is not a vertex group of any splitting of `G` with free edge groups whose other vertex groups have `gd ≤ 2` (Lemma 2 of `continuous-free-chain-unions-have-gd-two-proof`). In particular `H` is not free;
3. no 2-dimensional `K(G,1)` has a `π_1`-injective subcomplex carrying `H`.

**If countable EG holds as well**, every countable subgroup `Γ_δ ≅ Γ_{ℵ_0}(H,G)` (for `ω ≤ δ < ω_1`) has `gd = 2`. So the counterexample is "almost of geometric dimension 2", like an `ℵ_1`-free non-free abelian group.

## The question left open, now in sharp form

"Countable EG implies EG for groups of size `ℵ_1`" is equivalent to "countable EG implies REG_ω". So the question of whether REG_ω is equivalent to countable EG is exactly the question whether `gd ≤ 2` transfers from the countable amalgam `Γ_{ℵ_0}(H,G)` to `Γ_{ℵ_1}(H,G)`. This is not decided here.

## Remarks

- **The swap question has answer yes.** Extending a 2-dimensional `K(H,1)` depends only on the pair, not on the chosen complex. This is Lemma (a)⇒(b) of the engine, an adjunction along a homotopy equivalence. But this alone does not reduce `ℵ_1` to countable EG: the relative realization is a genuine extra property of the pair.
- **Absoluteness (proof sketch, not part of the ESTABLISHED claim).** For countable objects coded by reals:
  - `cd G ≤ 2`, `pd I_{G/H} ≤ 1` and `gd ≤ 2` are `Σ^1_1`: each says a countable projective resolution or a countable aspherical 2-complex exists, with arithmetical checks, since van Kampen diagrams and `H_2` of the universal cover are arithmetical in the complex.
  - REG_ω is therefore `Π^1_2`, so by Shoenfield absoluteness it has the same truth value in `V`, in `L` and in every forcing extension.
  - By the equivalence, so does "EG for groups of size `≤ ℵ_1`". Unlike the Whitehead problem for `ℵ_1`-free abelian groups, the `ℵ_1` case of Eilenberg--Ganea cannot be settled by forcing or by `V = L`.
- **Higher cardinals (sketch).** For `κ ≥ ℵ_0`, let REG_κ be REG for pairs of size `≤ κ`. The same two proofs, with elementary submodels of size `κ` containing `κ` as a subset, give REG_κ ⇔ EG for groups of size `≤ κ^+`.

## Attempts

- **w4-048, 2026-09-17: obstruction mining on admissible pairs.** Landed `relative-eg-pair-base-meets-its-conjugates-in-free-groups`: `pd I_{G/H} ≤ 1` alone forces `H ∩ gHg^{-1}` free for all `g ∉ H` and `H_2(H) ↪ H_2(G)`. Profile items added: the base of a minimal counterexample is self-commensurating and malnormal modulo free. Dead candidate families: normal bases (Bestvina–Brady kernels in 2-dimensional RAAGs, fibres), proper finite-index bases, all non-free pairs in `BS(1,n)`, HNN vertex groups over non-free edge groups. Detection via doubles `G *_H G` or any countable tree of copies of `G` over `H` cannot succeed without refuting countable EG outright, since those groups are countable with `cd ≤ 2`.
