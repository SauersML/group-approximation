---
rg: 2
id: quotient-permuting-and-ambient-inner-mapping-tori-are-lef
kind: claim
title: A mapping torus is LEF when the automorphism permutes a convergent family of finite quotients of a mother group, or has a power that is inner in a LEF overgroup, so neither kind of automorphism can give an exact MF radical
distinct_from:
  exact-kazhdan-radical-kernel-cannot-be-lef: that is (EKL1) for an arbitrary automorphism, still open; this proves (EKL1) for two explicit classes of automorphisms, with no use of property (T).
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that records the periodization attempt dying at the wrap; this shows the wrap never occurs for automorphisms permuting a quotient sequence, because their orbits on finite-index normal subgroups are finite.
  subshift-diagonal-automorphisms-need-infinite-spatial-class: that kills diagonal-preserving ring automorphisms for centralizer compression (G2); this kills the induced group automorphisms of the elementary group for the radical equation (LK3), by the same finite-spatial-class input.
  torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical: that is the open existence claim; this kills its suggested first test case and every standard automorphism of the known LEF quotientless Kazhdan groups.
artifacts:
  - research/quotient-permuting-and-ambient-inner-mapping-tori-are-lef-proof.md
  - research/lef-implies-operator-mf.md
  - research/subshift-diagonal-automorphisms-need-infinite-spatial-class.md
  - research/torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical.md
---

**ESTABLISHED.** Proof: `quotient-permuting-and-ambient-inner-mapping-tori-are-lef-proof`.

Throughout, `K` is a finitely generated group, `φ ∈ Aut(K)` and `G = K ⋊_φ Z`. Put
`t = (1, 1) ∈ G`. By `lef-implies-operator-mf`, a LEF group `G` is MF, so
`Rad_MF(G) = 1`. For `K != 1`, that is the failure of (LK3).

**(A) Invariant quotient families.** Let `M` be finitely generated, `α ∈ Aut(M)`, and let
`L_i ⊴ M` have finite index with `α(L_i) = L_i`. Suppose `L_i -> L` in the Chabauty
topology, meaning that each `m ∈ M` lies either in all but finitely many `L_i` or in only
finitely many. Then `α(L) = L` and `(M/L) ⋊_α Z` is LEF. It is a marked limit of the
finite groups `(M/L_i) ⋊ Z/c_i Z`, where `c_i` is a multiple of the order of `α` on `M/L_i`
and `c_i -> ∞`.

**(B) Permuted quotient sequences have finite orbits.** Let `N_n ⊴ M` (`n ≥ 0`) be pairwise
distinct finite-index normal subgroups with `N_n -> N` (Chabauty), and let `α ∈ Aut(M)`
permute the set `{N_n}`. Then:
- every `α`-orbit on `{N_n}` is finite, because `M` has only finitely many normal subgroups
  with quotient isomorphic to a given finite group;
- `α(N) = N`, and `L_O = ⋂_{n ∈ O} N_n` over the orbits `O`, enumerated by increasing
  minimum, satisfy (A) with limit `N`.

So `(M/N) ⋊_α Z` is LEF. The same holds when `α` only permutes a cofinite subset of
`{N_n}`: apply (B) to that subsequence, which has the same limit.

**(C) Ambient virtual innerness.** Let `K ≤ H` with `H` LEF. Suppose there are `m ≥ 1` and
`h ∈ H` with `h K h^-1 = K` and `φ^m = Ad(h)|_K`. Then `G` is LEF. The index-`m` subgroup
`K ⋊ mZ` embeds in `H × Z` by `(k, mn) -> (k h^n, n)`, and a group containing a LEF subgroup
of finite index is LEF.

## What dies

- **The suggested first test case of `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`.**
  Let `K` be a marked limit of finite quotients `M/N_n` of a mother `M`, for example a
  torsion-free alternating-mother limit, and let `φ` be induced by an automorphism of `M`
  permuting the quotient sequence. Then `G` is LEF by (B), and (LK3) fails. No hypothesis on
  `K` beyond finite generation is used.
- **Standard automorphisms of `EL_n(R)`, `n ≥ 3`, for a unital ring `R` with an injective
  unital ring map into an ultraproduct `prod_ω M_(N_k)(A)`, where `A` is `Z` or a finite
  field.** This covers `R = LC(X,F_q) ⋊ Z` of `lef-kazhdan-group-without-finite-quotients-exists`
  and its integer form `R_0 = LC(X,Z) ⋊ Z`, via the periodic models. By (C), `G` is LEF for:
  - conjugation by any `g ∈ GL_n(R)` normalizing `EL_n(R)`, e.g. every diagonal matrix of
    units, such as `diag(u, 1, 1)` or `diag(w, 1, 1)` with `w` a topological-full-group unit;
  - `EL_n(σ)` composed with such a conjugation, whenever `σ ∈ Aut(R)` has a power `Ad(v)`,
    `v ∈ R^x`.
    Examples of such `σ`:
    - every ring automorphism induced by `ψ ∈ Aut(X,T)` with `ψ^r = T^s`. Then `σ^r = Ad(u^s)`;
    - every diagonal-preserving `σ` of `LC(X,F_q) ⋊ Z` whose spatial class has finite order,
      by `subshift-diagonal-automorphisms-need-infinite-spatial-class`.

**Invariant.** Existence of a finite `φ`-invariant quotient family converging to `K`
(A, B), or a power of `φ` that is inner in a LEF overgroup (C). Every member dies at the
same step: `t` acts as an honest automorphism of an honest finite (or LEF) model of `K`.
The torus is then modelled exactly, so it is LEF.

**What survives.** A solution of (L2) needs `φ` such that:
- no power of `φ` is inner in any LEF group containing `K`;
- no mother presentation of `K` has an `α`-invariant approximating family.

By (B), the family cannot come from a permuted quotient sequence. The "shift" picture
`N_(n+1) = α(N_n)`, which periodization attempts need, is impossible for finite-index
subgroups. So the wrap cannot be avoided by choosing the mother automorphism. For
elementary-group kernels, a survivor must be:
- a nonstandard automorphism of `EL_n(R)`; or
- `EL_n(σ)` with `σ` of infinite order in `Out(R)` and no inner power, e.g. `σ` induced by
  `ψ ∈ Aut(X,T)` of infinite order modulo `<T>`, on subshifts where such `ψ` exist.
