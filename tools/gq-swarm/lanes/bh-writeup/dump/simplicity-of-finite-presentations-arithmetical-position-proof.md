---
rg: 2
id: simplicity-of-finite-presentations-arithmetical-position-proof
kind: route
title: Count quantifiers in the definition of simplicity, reduce triviality to it through V × G, and bound Kuznetsov's searches
target: simplicity-of-finite-presentations-arithmetical-position
requires: []
---

Write `P = <X | R>`, `X` finite. "`u = 1` in `G_P`" is `Σ^0_1`: enumerate
products of conjugates of relators. "`y ∈ <<w>>`" is `Σ^0_1`: enumerate products
of conjugates of `w^(±1)` and test equality to `y` by the previous search.

**1. Upper bound.** `G_P` is simple iff both of the following hold:
- **nontrivial:** some generator `x ∈ X` has `x != 1`. This is a finite
  disjunction of `Π^0_1` statements, so it is `Π^0_1`;
- **every element is trivial or normally generates:** for every word `w`, either
  `w = 1`, or every `y ∈ X` lies in `<<w>>`. The inner part is a finite
  combination of `Σ^0_1` statements, so this is `Π^0_2`.

**2. Lower bound.** Fix Cannon--Floyd--Parry's finite presentation of Thompson's
group `V`, which is infinite and simple (classical). From `P` compute the finite
presentation of `V × G_P`: generators of both, relators of both, and the
commutators of each `V`-generator with each `x ∈ X`.
- If `G_P = 1`, the group is `V`, which is simple.
- If `G_P != 1`, then `1 × G_P` is a proper nontrivial normal subgroup.

So `P ∈ TRIV_fp` iff `(V × G_P) ∈ SIMPLE_fp`. `TRIV_fp` is `Σ^0_1`-complete
(Adian--Rabin; the "trivial" row of `arithmetical-complexity-table-of-group-properties`).
Hence `SIMPLE_fp` is `Σ^0_1`-hard, and not `Π^0_1`, since a `Σ^0_1`-complete set is
not co-r.e. The group `V × G_P` is infinite, so the same reduction serves the
infinite simple ones.

**3. Collapse under uniform profile bounds.** Assume a recursive `F` as in the claim, replaced if necessary by `n ↦ n + max_{k<=n} F(k)`, so it is non-decreasing and at least `n`; this only changes constants. For a presentation `P`, consider:

```text
∃ C ∃ x ∈ X :  x != 1                                                 (Π^0_1)
             ∧ each y ∈ X lies in <<x>>                               (Σ^0_1)
             ∧ ∀ w : [ a van Kampen diagram for w of area <= C F(C|w|) exists ]
                    ∨ [ x = Π_{i<=k} u_i w^(±1) u_i^-1 with k, |u_i| <= C F(C|w|)
                        and the resulting relator of area <= C F(C|w|) ]      (Π^0_1)
```

For each `w` the bracket is a bounded search, hence decidable. So the formula is
`Σ^0_2`.
- *Simple implies the formula.* Take any generator `x != 1`. Every generator lies
  in `<<x>>`. For `C` large the profile bound makes the bracket true for every `w`,
  by the definitions of `δ_S` and `ν_S`, after adjusting `C` for the choice of `x`.
- *The formula implies simple.* Each certificate is genuine. So every `w` is
  trivial or has `x ∈ <<w>>`, and then all of `X` lies in `<<w>>`. With `x != 1`,
  `G_P` is nontrivial and simple.

So `SIMPLE_fp ∈ Σ^0_2`. Together with item 1, `SIMPLE_fp ∈ Δ^0_2`. `∎`
