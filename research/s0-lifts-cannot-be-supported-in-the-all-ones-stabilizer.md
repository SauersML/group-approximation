---
rg: 2
id: s0-lifts-cannot-be-supported-in-the-all-ones-stabilizer
kind: claim
title: No lift of s_0 to F_2[R^x] is supported on units fixing the all-ones function, in particular on Thompson's V
distinct_from:
  subgroup-supported-one-sided-inverse-rigidity: that kills supports generating a subgroup whose group algebra is directly finite, and needs that finiteness as input; this kills supports inside one fixed subgroup by an evaluation invariant with no finiteness input, and covers Thompson's V, whose soficity is open.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the open existence question for a left-invertible lift of s_0; this is a necessary condition on the support of every lift of s_0, left-invertible or not.
artifacts:
  - research/artifacts/kaplansky-df-sat-search-2026-09-12.md
---

**ESTABLISHED.** Setting:
- `R = L_(F_2)(1,2)`, `G = R^x`, and `pi : F_2[G] -> R` is the evaluation map;
- `eps` is the augmentation;
- `F` is the space of all functions `Omega -> F_2`, where `Omega` is the set of infinite binary sequences.

A monomial acts on `F` by

```text
(S[a]T[b] f)(a eta) = f(b eta),        (S[a]T[b] f) = 0 off the cylinder [a].
```

This makes `F` a left `R`-module. Write `1` for the constant function, and put

```text
H_1 = { u in G : u 1 = 1 },        H^1 = { u in G : u^* 1 = 1 },
```

where `x -> x^*` is the involution `S[a]T[b] -> S[b]T[a]`.

1. `H_1` and `H^1` are subgroups of `G`. Both contain Thompson's group `V`, the units
   `sum_i S[r_i]T[d_i]` over pairs of complete prefix codes.
2. If `supp beta` lies in `H_1`, then `pi(beta) 1 = eps(beta) 1`. Since `s_0 1` is
   the indicator of `[0]`, and so is not constant, `pi(beta) != s_0`.
3. If `supp alpha` lies in `H^1`, then `pi(alpha) != t_0`.

## Consequences

- **The sharp lift.** In `left-invertible-lift-of-s0-in-leavitt-group-algebra` the
  support of `a` must leave `H_1`. Every support inside `V`, or inside any subgroup of
  `V` such as `F` or `T`, is excluded at every radius. This needs no knowledge of
  whether `F_2[V]` is directly finite, and that question remains open.
- **The SAT search.** Lane `kdf-sat` found by exact Gaussian elimination that `s_0` lies
  outside the span of `pi(B_r(V))` for `r <= 6`. These are instances of item 2.
- **What it does not do.** It says nothing about supports that only partly meet
  `H_1`. It gives nothing for strict pairs without an evaluation target, because the
  root question `leavitt-unit-group-algebra-not-directly-finite` fixes no value of
  `pi`. The atlas charts leave `H_1`: a chart unit `sum M_ij S[d_i]T[d_j]` fixes `1`
  iff every row of `M` has odd weight.

Proof: `s0-lifts-all-ones-stabilizer-proof`.
