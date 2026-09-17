---
rg: 2
id: brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination
kind: claim
title: "nV has the Haagerup property iff some cnd functions dominate the sup-norm of the exponent cocycle, the depth of its pattern, and the depth of elements of the locally finite kernel"
distinct_from:
  haagerup-splits-as-coset-plus-subgroup-properness: that is the abstract split along any subgroup; this applies it to H = ker c and identifies the coset space with the set of values of the exponent cocycle, which then splits further into a magnitude part and a pattern part
  brin-thompson-nv-cnd-proper-on-triangular-subgroup: that is the fibre half of the split along the triangular subgroup T_n, which contains infinite-order elements; this splits along the kernel K of the exponent cocycle, a locally finite union of finite symmetric groups, and moves all infinite-order content into two statements about the cocycle alone
  brothier-problem-b-reduces-to-value-range-domination: that splits properness on C(C,Γ) into value range and position for Problem B; this is the analogous three-way split for nV itself, where the positional half is not automatic
---

**ESTABLISHED** by `brin-thompson-nv-haagerup-iff-cocycle-kernel-domination-proof`.

## Setting

- `C = {0,1}^ω`, `n ≥ 1`. A *brick* is `[u_1] × ... × [u_n] ⊆ C^n`, with `[u]` the cylinder of
  the finite word `u`; it is a *level-`m` cube* when every `|u_i| = m`. A *prefix replacement*
  `[u_1]×...×[u_n] → [v_1]×...×[v_n]` is `(u_1 x_1, ..., u_n x_n) ↦ (v_1 x_1, ..., v_n x_n)`.
  Every `g ∈ nV` is a prefix replacement on each brick of some finite brick partition.
- **Exponent cocycle.** `c(g) ∈ C(C^n, Z^n)`, `c(g)(x) = (|v_i| − |u_i|)_i` for any prefix
  replacement of `g` on a brick containing `x`. It is well defined (refining a brick does not change
  the length differences) and satisfies `c(gh) = c(g)∘h + c(h)`.
- **Scale.** `‖c(g)‖ = max_{x,i} |c(g)(x)_i|`.
- **Pattern depth.** `pd(g)` is the least `m ≥ 0` such that `c(g)` is constant on every level-`m` cube.
- **Kernel.** `K = {g : c(g) = 0}`, a subgroup by the cocycle identity. `K_m` is the set of
  `g` that permute the level-`m` cubes by prefix replacements, so `K_m ≅ Sym(2^{nm})`. The
  *kernel depth* of `k ∈ K` is the least `m` with `k ∈ K_m`.

## Statement

Say a function `φ: nV → [0,∞)` *dominates* a function `d: S → N` on a subset `S ⊆ nV` if there
is `F: N → R` with `F(t) → ∞` and `φ(g) ≥ F(d(g))` for all `g ∈ S`. The following are equivalent.

1. `nV` has the Haagerup property.
2. There are cnd functions `ψ_1, ψ_2, ψ_3` on `nV` such that
   - **(P1, scale)** `ψ_1` dominates `‖c(·)‖` on `nV`;
   - **(P2, pattern)** `ψ_2` dominates `pd(·)` on `nV`;
   - **(P3, kernel)** `ψ_3` dominates the kernel depth on `K`, i.e. `ψ_3|_K` is proper.

Moreover `ψ_1 + ψ_2 + ψ_3` is then proper.

**Supplements.**

- (a) `K = ⋃_m K_m` is locally finite, and `gK ↦ c(g^{-1})` is a bijection from `nV/K` onto
  the set of values of the cocycle. So `P1 ∧ P2` is exactly "some cnd function is proper modulo `K`".
- (b) Each of P1, P2, P3 for `mV` implies the same statement for `nV` when `n ≤ m`, through
  `g ↦ g × id`.
- (c) P1 for `2V` implies `cantor-integer-maps-sup-norm-is-cnd-dominated`, hence (by
  `brothier-problem-b-reduces-to-value-range-domination`) `cantor-integer-maps-by-v-have-haagerup-property`.
- (d) For `n ≥ 2` no commensurating action (wall count `ℓ(g) = |gA Δ A|`) satisfies P1 or P2.
  The witness is `z = id × x_0 ∈ V × V ≤ 2V ≤ nV`, which is elliptic in every commensurating action
  by `brin-thompson-nv-fibre-elements-are-cubically-elliptic`, while `‖c(z^M)‖ = M` and `pd(z^M) ≥ M`.
- (e) The analogous statement for `n = 1` holds with all three functions equal to Farley's wall
  count (`thompson-v-has-haagerup-property`), so the break from `V` to `2V` sits in P1, P2 or P3.

## What this changes

- **Groupoid part and finite part are separated.** P1 and P2 only see the continuous cocycle
  `c: G_2^n → Z^n` on the germ groupoid, through the values `c(g)`. P3 only sees the finite
  symmetric groups `K_m ≅ Sym(2^{nm})` and how the rest of `nV` weighs them.
- **All infinite-order content sits in P1 ∧ P2.** `K` is torsion, so the Callard–Salo element
  `f` and every infinite-order element leave all finite unions of `K`-cosets. Their growth is
  forced through P1 or P2, which are non-cubical by (d). P3 concerns torsion only, and none of the
  recorded kills applies to it: no known elliptic family inside `K` has unbounded kernel depth.
- **P1 is at least as hard as Problem B for `Z`**, by (c). P2 is the `nV` analogue of the
  positional half of Problem B, which was free there
  (`brothier-problem-b-reduces-to-value-range-domination`) because of congruence quotients into `V`.
  `nV` has no such quotients, so here P2 is a separate prerequisite.
- **Where the groupoid class-kill lands.** The Kazhdan host `(M ⋊ Γ) × G_2` of
  `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan` carries the `Z`-cocycle of its
  `G_2` factor, and every `γ ∈ Γ` acts with cocycle `0`. So the kernel contains `Γ`, and properness
  on the kernel is impossible there. A P1 or P2 argument that uses only the cocycle is not reached by
  that class-kill, since `Γ` is invisible to both `‖c‖` and `pd`. A groupoid-generic argument for P3
  dies unless it uses that `K` is locally finite (the kernel groupoid of `c` is AF).

## Imports

- `haagerup-splits-as-coset-plus-subgroup-properness` (the split lemma).
- `cantor-maps-by-v-embed-in-next-brin-thompson-group` and
  `brothier-problem-b-reduces-to-value-range-domination` (supplement (c) only).
- `brin-thompson-nv-fibre-elements-are-cubically-elliptic` (supplement (d) only).
- `thompson-v-has-haagerup-property` (supplement (e) only).
