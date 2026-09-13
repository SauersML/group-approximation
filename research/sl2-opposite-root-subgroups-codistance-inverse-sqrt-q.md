---
rg: 2
id: sl2-opposite-root-subgroups-codistance-inverse-sqrt-q
kind: claim
title: In SL_2(q) the coset graph of the two opposite root subgroups has girth 6 and second singular value q^(-1/2)
---

Let `q >= 3` be a prime power, `k = F_q` and `G = SL_2(k)`. Put `U_+ = {u(x) = [[1,x],[0,1]]}` and
`U_- = {v(y) = [[1,0],[y,1]]}`, and let `Γ = Γ_G(U_+, U_-)` be their coset graph (vertices
`G/U_+ ⊔ G/U_-`, one edge per group element).

**ESTABLISHED.**
- (a) `Γ` is `q`-regular, with `q^2 - 1` vertices on each side, connected, and of girth `6`.
- (b) The singular values of `M/q`, for the biadjacency matrix `M`, are:
  - `1`, with multiplicity 1;
  - `q^{-1/2}`, with multiplicity `q^2 - q - 2`;
  - `q^{-1}`, with multiplicity `q`.
- (c) Hence `σ_2(Γ) = q^{-1/2}`. By `coset-graph-singular-values-bound-fixed-space-angles`, every unitary
  representation `V` of any group receiving `G` satisfies `cos ∢(V^{U_+}, V^{U_-}) <= q^{-1/2}`.

For `q = 2^f >= 4`, `G` is simple. The value `q^{-1/2}` is the classical angle between opposite root
subgroups used by Dymara–Januszkiewicz and Ershov–Jaikin-Zapirain; the explicit spectrum is recorded here
for use in `kazhdan-hyperbolic-sl2-root-triangles`.

**Calibration (computed).** `experiments/sl2-root-triangle-kazhdan/run1.out` builds `Γ` independently
for `q = 8` and `q = 16`. It returns girth `6`, and top singular values `0.353553 = 8^{-1/2}` and
`0.250000 = 16^{-1/2}`, each with multiplicity at least 5.

Proof: `sl2-opposite-root-subgroups-codistance-inverse-sqrt-q-proof`.
