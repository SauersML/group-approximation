---
rg: 2
id: self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale
kind: claim
title: A Z^2 subshift of finite type with an injective constant-size block substitution mapping it into itself is quantum rigid iff it is rigid at one small fixed scale; non-commuting operator tilings at small scale substitute up to every scale
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that proves finite presentation of the crossed product iff D-quantum rigidity for some D; this shows that for self-similar SFTs the scale D can be taken to be one fixed small value, because non-rigidity at scale D' substitutes up to scale N(D'-2).
  periodic-quantum-tilings-refute-quantum-rigidity: that refutes rigidity at the scale of a given periodic operator tiling; this propagates any non-commuting family, periodic or not, from one scale to all larger scales along the substitution.
  deterministic-time-lifts-inherit-quantum-rigidity: that transfers rigidity along a deterministic product factor; this transfers non-rigidity along a self-similarity, in the opposite direction of scale.
artifacts:
  - research/artifacts/gq-bh-synthesis-master-route.md
---

**ESTABLISHED (2026-09-18)** through `self-similar-sft-rigidity-scale-collapse-proof`. Lane proof (bh-free-12),
elementary, not independently reviewed. No priority is claimed; a bounded search of the quantum-rigidity nodes on
main found no statement about substitutions or scales.

## Setting

- `Ω ⊆ A^(Z^2)` is an SFT with forbidden patterns of radius `r`.
- **Quantum rigidity** is as in `sft-crossed-product-fp-iff-quantum-rigid`, with conditions (Q1)–(Q3) and the word
  (`ℓ¹`) metric of `Z^2`. A family on `W` satisfying them at scale `D` is a **`D`-family**. `Ω` is `D`-rigid if every
  `D`-family commutes.
- `N >= 2`, and `σ : A → A^([0,N)^2)` is an **injective block substitution with `σ(Ω) ⊆ Ω`**. Here `σ(x)` places
  the block `σ(x_Z)` on `NZ + [0,N)^2`.

## Statement

Put `D_0 = max(r, ⌊2N/(N−1)⌋ + 1)`. This is at most `max(r, 5)`, and equals `max(r, 3)` for `N >= 4`.

1. **Substitution of families.** If `(M_c(Z))` is a `D'`-family for `Ω` on `W`, then
   `E_a(z) := Σ_{c : σ(c)_{z − NZ} = a} M_c(Z)`, with `Z = ⌊z/N⌋`, is an `N(D'−2)`-family for `Ω` on the same `W`.
   It commutes only if `(M_c)` commutes. The period lattice `Λ` of a periodic family becomes `NΛ`.
2. **Scale collapse.** `Ω` is quantum rigid, i.e. `D`-rigid for some `D >= r`, iff it is `D_0`-rigid. Equivalently,
   one non-commuting `D_0`-family yields non-commuting families at every scale, and then `LC(Ω, k) ⋊ Z^2` is not
   finitely presented over `k`.
3. **Examples.** Fixed-point (self-simulating) tile sets of Durand–Romashchenko–Shen satisfy the hypothesis, with
   `r = 1` (Wang tiles). Here `σ(c)` is the macrotile of colour `c`: it is injective, and `σ(Ω) ⊆ Ω` is the
   self-simulation property (cited, not re-read). So they are quantum rigid iff they are `3`-rigid for zoom
   `N >= 4`, and `D_0 <= 5` in general.

## Scope

Constant-size block substitutions only. Labbé's self-similarity of `Ω_U` has letter-dependent rectangular shapes,
so the block containing a site depends on other letters. The substitution of families in item 1 then needs
operator-valued positions, and it is not claimed.

## Lesson for general BH

For the master route's crux G2 (`free-minimal-z2-sft-is-quantum-rigid`, `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`),
self-similarity gives **no scale advantage**. The main source of aperiodic minimal SFTs, fixed-point tilings, is
quantum rigid only if it is rigid with commutation radius at most `2D_0 <= 10`, since non-rigidity at small scale
substitutes up to every scale.

Consequences:
- **For proofs** (Conjecture G2-fp, "induction on levels"): the induction has to run at a fixed small commutation
  radius. A proof that uses commutation at the scale of level-`k` supertiles cannot close.
- **For kills**: one narrow wall, or one non-commuting family at scale `D_0`, kills a self-similar candidate at
  every scale. For constant-size substitutions this is the uniform version of
  `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`.
- **Structurally**: for self-similar SFTs, finite presentation of the crossed product is decided by the one natural
  local presentation at scale `D_0`.
