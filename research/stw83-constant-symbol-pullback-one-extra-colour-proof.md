---
rg: 2
id: stw83-constant-symbol-pullback-one-extra-colour-proof
kind: route
title: Constant band, exact outer colours in the orthogonal corner, and one band colour
target: stw83-constant-symbol-pullback-one-extra-colour
requires: []
artifacts:
  - research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md
---

The full proof is Sections 1--4 of the artifact.  Its imported facts are
listed there as (F1)--(F5), with their verification status:
* quotient and hereditary-subalgebra permanence, `dim_nuc(C(X))=dim X`, and
  stable-isomorphism invariance (Winter--Zacharias);
* order-zero lifting from finite-dimensional algebras (Winter);
* Choi--Effros lifting.

The steps are as follows.

1. **Well-definedness.**  `C(X,K)` is an ideal of `C(X,B(H))`, so `A_X(D)` is
   a C\*-algebra.  `pi(c+x tensor 1)=q(x)` is a well-defined surjection with
   kernel `C(X,K)`.  Permanence and stable invariance give the lower bound.
2. **Nested quasicentral units.**  By Mazur's lemma applied to the weakly null
   commutators `[P_j,x]`, there are finite-rank convex combinations `e_i` of
   basis projections and finite-rank projections `Q_i` with
   `Q_ie_i=e_i`, `e_(i+1)Q_i=Q_i`, `e_i->1` strictly on `K`, and
   `[e_i,x]->0` on `D`.  Then `h_i=e_i tensor 1` is a quasicentral
   approximate unit for `C(X,K)` in `A_X(D)`.
3. **Three pieces.**  With a cpc lift `sigma` of `q|D` and `mu=sigma tensor 1`:
   * `alpha_i(a)=h_i^(1/2)ah_i^(1/2)` lies in `E_i=C(X,Q_iB(H)Q_i)=M_(R_i)(C(X))`;
   * `beta_i(b)=(h_(i+1)-h_i)^(1/2)mu(b)(...)^(1/2)` lies in the
     finite-dimensional algebra `M_(R_(i+1)) tensor 1`, which is where the
     constant symbol is used;
   * `gamma_i(b)=(1-h_(i+1))^(1/2)mu(b)(...)^(1/2)` lies in the hereditary
     subalgebra `C_i` of elements killed by `Q_i tensor 1` on both sides, so
     `C_iE_i=0`.

   Their sum approximates `a`.
4. **Exact outer colours.**  Let `eta:F->B` be cpc order zero with lift
   `hat(eta)`.  The maps
   `theta_i=(1-h_(i+1))^(1/2)(hat(eta) tensor 1)(1-h_(i+1))^(1/2)` are
   asymptotically order zero, by quasicentrality.  Lifting the induced
   order-zero map `F->prod C_i / sum C_i` gives exactly order-zero
   `tilde(theta)_i:F->C_i` with `||tilde(theta)_i-theta_i||->0`.
5. **Assembly.**  For each `k<=max(n,d)`, colour `k` is
   `zeta^(k)+tilde(theta)^(k)_i`.  Here `zeta^(k)` are the colours of an
   `(n+1)`-coloured approximation of `E_i`, and `tilde(theta)^(k)_i` those of
   a `(d+1)`-coloured approximation of `B`.  Their ranges are orthogonal, so
   the sum is cpc order zero.  One further colour is the *-homomorphism
   `M_(R_(i+1))->A`, `z |-> z tensor 1`, carrying `beta_i`.  The total error is
   at most `5 eps`.  This gives `max(n,d)+2` colours, so
   `dim_nuc<=max(n,d)+1`.
