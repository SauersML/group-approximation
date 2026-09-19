---
rg: 2
id: atlas-steinberg-context-absorption
kind: claim
title: Steinberg relations absorb their own ring-relation contexts, which is where the rank-four threshold lives
distinct_from:
  atlas-relator-central-sufficiency: that characterizes usable relator lists for the atlas criterion; this is a general lemma about Steinberg-type presentations that removes the apparent infinitude of ring-relation contexts from any completeness argument.
  atlas-steinberg-rank-five-translation: that is the usable-list program; this is the piece of its completeness gap that is already a theorem, isolated because it is reusable and because it explains a threshold the repo previously imported as a black box.
artifacts:
  - research/artifacts/atlas-rank5-dictionary-2026-08-15.md
---

Let `G₀` be a group with elements `x_ij(c)` indexed by `1 ≤ i ≠ j ≤ n`
and ring elements `c`, satisfying the Steinberg commutator relation
`[x_ij(a), x_jk(b)] = x_ik(ab)` (`i ≠ k`) and additivity in the
coefficient (each root subgroup abelian, `x_ij(a)x_ij(b) = x_ij(a+b)`).

**Theorem (context absorption).**  Suppose `n ≥ 4`.  If a ring element
`ρ` satisfies `x_kl(ρ) = 1` for every root `(k,l)`, then

```text
x_ij(u ρ v) = 1     for all monomials u, v and every root (i,j):
```

nesting through spare indices,

```text
x_ij(uρv) = [x_ik(u), x_kj(ρv)],      x_kj(ρv) = [x_kl(ρ), x_lj(v)],
```

with `i, j, k, l` pairwise distinct, and the inner bracket dies because
its first entry does.  *(Dependency made explicit 2026-08-15, late: for
`ρ` a sum of monomials the argument first splits `x_kl` over the sum,
which uses bilinearity of the bracket in a root-subgroup argument —
`[X, PQ] = [X,P][X,Q]` for `P, Q` in one root subgroup — itself a
consequence of an emitted (St2) instance; Lemma 2.1 of the completeness
derivation artifact.)*  The defining relations of a presented ring
therefore need to be imposed at a single root each — their monomial
contexts come for free — and the index budget of the nesting is exactly
four.

**Why this matters.**

1. It removes the apparent infinitude from completeness arguments for
   Steinberg groups over presented rings: only the context-free ring
   relations must be emitted, which for the binary Leavitt ring are
   precisely the five Cuntz–Krieger relations, all present in the
   emitted `T_St` of `atlas-steinberg-rank-five-translation`.
2. It locates the `n ≥ 4` threshold of [KrM, Theorem 3] (Krstić–McCool,
   JPAA 141 (1999) 175–183, pinned verbatim in the artifact): four
   pairwise distinct indices are what the nesting consumes, and the
   sharp failure of finite presentability at `n = 3` ([KrM, Corollary
   2]) sits exactly below the budget.  A threshold the repo previously
   imported as a black box is now a mechanism.  At `n = 5` there is an
   index to spare.
