---
rg: 2
id: bc-kun-thom-gap-labels-bc-subgroup-proof
kind: route
title: Spectral permanence in the subgroup algebra, then Lück's trace theorem for the subgroup
target: bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test
requires:
  - kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p
artifacts:
  - research/artifacts/bc-gap-label-subgroup-support-2026-09-12.md
---

Imports (I1) and (I2) are quoted verbatim from Lück--Reich, arXiv:math/0402405, in the artifact.
Their content is the trace theorem 3.22 (Lück, Invent. Math. 149 (2002), Thm 0.3) and Theorem 5.1
(Higson--Kasparov).

1. **`C*_r H` is a unital C*-subalgebra of `C*_r G`.** Write `l^2(G) = ⊕_(t ∈ H\G) l^2(Ht)`. Each
   summand is invariant under `lambda_G(H)` and unitarily equivalent to `lambda_H`. So
   `||lambda_G(x)|| = ||lambda_H(x)||` for `x ∈ M_n(C[H])`, and the closure of `lambda_G(M_n(C[H]))`
   is `M_n(C*_r H)` with the same unit.
2. **The projection lies in `M_n(C*_r H)`.** Spectra in a unital C*-subalgebra agree with those
   in the ambient algebra. So `c` is in a gap of the spectrum of `lambda(a)` in `M_n(C*_r H)`.
   Pick `f` continuous with `f = 1` on `spec ∩ (-inf,c)` and `f = 0` on `spec ∩ (c,inf)`. Then
   `chi = f(lambda(a))` is a projection in `M_n(C*_r H)`.
3. **The traces agree.** On `M_n(C*_r H)` the canonical traces of `G` and `H` coincide: both are
   `x ↦ sum_i <x_ii delta_e, delta_e>`.
4. **Lück's theorem.** Surjectivity gives `[chi] = A_FIN(y)` for some `y ∈ K_0^H(E_FIN H)`. Then
   `tau(chi) = tr(A_FIN(y)) = tr((A_FIN ⊗ id)(y ⊗ 1))`, which lies in `Lambda^H` by (I1). For
   a-T-menable `H`, surjectivity holds by (I2): the Conjecture with Coefficients contains
   Baum--Connes as a special case.
5. **The ring shrinks.** Every finite subgroup of `H` is a finite subgroup of `G`, so
   `Lambda^H` is contained in `Lambda^G`. By `kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p`,
   `Lambda^G = Z[1/P]`. QED

**The listed supports are a-T-menable.** Everything is inside `G`; see the artifact, Section 3.
- **Borel subgroup.** The Borel subgroup of `EL_r(R)` is solvable, since the diagonal part is
  abelian and the unipotent part is nilpotent. So it is amenable.
- **Lamplighters.** `F_q wr Z^k` is amenable. It arises from `e_12(F_q[x^(+-2)])` together with
  the Whitehead torus elements.
- **One-variable `E_2`.** `E_2(F_q[x_1^(+-1)])` is a subgroup of `SL_2(F_q[x_1^(+-1)])`. That group
  is discrete in `SL_2(F_q((x_1))) × SL_2(F_q((x_1^(-1))))`, because `F_q[x_1^(+-1)]` is discrete
  in the product of the two completions. So it acts on the product of the two Bruhat--Tits trees
  with finite stabilizers, hence properly.
- **`SL_2(Z)`.** It acts properly on a tree.
- **Products.** (I2) gives closure under subgroups and finite products.
