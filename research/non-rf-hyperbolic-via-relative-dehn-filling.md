---
rg: 2
id: non-rf-hyperbolic-via-relative-dehn-filling
kind: route
title: Fill a relatively hyperbolic counterexample to an ordinary hyperbolic one
target: non-residually-finite-hyperbolic-group
requires:
  - non-rf-relatively-hyperbolic-with-rf-peripherals
  - relatively-hyperbolic-dehn-filling
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Let `G` be hyperbolic relative to finitely generated residually finite
`P_1, …, P_m`, and not residually finite.  Choose

```text
1 != w in R_f(G) = intersection of the kernels of all G -> finite.
```

Apply `relatively-hyperbolic-dehn-filling` to the finite set `F = {w}`: it
returns finite sets `B_i ⊂ P_i ∖ {1}` such that any `N_i ⊴ P_i` avoiding `B_i`
fills to a quotient `π : G → G_bar` that is hyperbolic relative to `{P_i/N_i}`
and injective on `{w}`.

**Choose the fillings finite-index.**  For each `b ∈ B_i` residual finiteness
of `P_i` gives a finite-index normal subgroup of `P_i` missing `b`;
intersecting the finitely many of them gives `N_i ⊴_f P_i` with
`N_i ∩ B_i = ∅`.  So the filling can be simultaneously long enough and finite,
which is the one place the peripheral hypothesis is used.

Then `G_bar` is hyperbolic relative to the **finite** groups `P_i/N_i`, hence
word-hyperbolic.

**The witness survives, and stays invisible.**  `π(w) ≠ 1` by the filling
theorem.  And for any homomorphism `ψ : G_bar → F` with `F` finite, the
composite `ψ ∘ π : G → F` is a finite quotient of `G`, so `ψ(π(w)) = 1` because
`w ∈ R_f(G)`.  Hence

```text
1 != π(w) in R_f(G_bar),
```

and `G_bar` is a word-hyperbolic group that is not residually finite.

**What the reduction actually buys.**  Nothing, if read as progress — it says
the relative problem with residually finite peripherals is *already* the
hyperbolic problem.  Its value is as a filter: it explains why constructions
of non-approximable relatively hyperbolic groups do not settle the hyperbolic
question, namely that their peripheral subgroups carry the pathology and
cannot be replaced by finite groups without destroying the witness.
