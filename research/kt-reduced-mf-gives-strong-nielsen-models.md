---
rg: 2
id: kt-reduced-mf-gives-strong-nielsen-models
kind: route
title: Restrict faithful trace-selected reduced MF coordinates to the Nielsen pair
target: kt-strong-nielsen-covariant-microstates
requires:
  - kt-double-reduced-cstar-is-mf
  - kt-double-is-nielsen-semidirect-product
  - kt-q2-reduced-cstar-has-unique-trace
  - monotracial-mf-algebra-has-mf-trace
  - faithful-mf-models-realize-all-mf-traces
---

Put `A=C*_r(D)`.  The first prerequisite makes `A` MF.  Its unique trace is
the canonical regular trace by `kt-q2-reduced-cstar-has-unique-trace`, and
`monotracial-mf-algebra-has-mf-trace` makes that trace an MF trace.
`faithful-mf-models-realize-all-mf-traces` therefore supplies
asymptotically isometric MF coordinates

```text
Phi_n:A->M_(d_n)
```

whose normalized traces converge pointwise to the regular trace.

Use `(KNS2)` to regard `g in G` and `b_x in N` as group elements of `D`.
Approximate multiplicativity and the star law show that
`Phi_n(lambda_g)` and `Phi_n(lambda_(b_x))` are asymptotically unitary.
After one diagonal subsequence, replace them by their unitary polar parts and
call the results `U_n(g)` and `V_n(x)`; set `V_n(o)=1`.  Polar replacement is
pointwise `o(1)` in operator norm, so it preserves all limits below.

The group law in `G` gives `(SNM2)`.  Applying `Phi_n` to the exact identity

```text
lambda_g lambda_(b_x) lambda_g^*
  =lambda_(b_(gx)) lambda_(b_(go))^*
```

from `(KNS1)` gives `(SNM3)`.  Telescoping over each fixed free word shows
that `(SNM4)` differs by `o(1)` from `Phi_n(lambda_(a,g))`.  Asymptotic
linearity and isometry of `Phi_n` then give `(SNM5)`, while the selected
trace gives `(SNM6)`.  Hence the concrete strong Nielsen package exists.
