---
rg: 2
id: kl-cyclic-orbit-perfect-kernel
kind: claim
title: The cyclic-orbit kernel is perfect and has no nontrivial finite quotient
invalidates: [simple-kl-via-finite-quotient-certificate]
distinct_from:
  degree-kernel-abelianization-is-infinite-cyclic: that computes the abelianization of the index-m subgroup before the orbit relators are imposed; this computes the quotient by all orbit relators and proves both perfectness and finite-quotient invisibility.
  leavitt-degree-kernel-quotient-tests-are-procyclic: that controls finite and solvable images for the particular Leavitt coefficient group, which is not known here to be simple; this works for every infinite nonabelian simple coefficient group and identifies the exact Kervaire--Laudenbach core quotient.
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Let `S` be an infinite nonabelian simple group, let

    F = S * <t>,

fix `m >= 1`, and let `pi_m : F -> C_m` kill `S` and send `t` to the standard
generator.  Put `N_m = ker(pi_m)`.  For `w in F` with `deg_t(w) = m`, define

    z = t^m,                         S_i = t^i S t^(-i)  (0 <= i < m),
    alpha = Ad(t)|_(N_m),            w_i = alpha^i(w),
    Q_w = N_m/<<w_0, ..., w_(m-1)>>_(N_m),
    H_w = F/<<w>>_F.

Then:

1. `N_m = S_0 * ... * S_(m-1) * <z>`;
2. `alpha(S_i)=S_(i+1)` for `i<m-1`,
   `alpha(S_(m-1))=z S_0 z^(-1)`, `alpha(z)=z`, and
   `alpha^m=Ad(z)`;
3. the ambient normal closure is exactly the finite orbit closure

       <<w>>_F = <<w_0, ..., w_(m-1)>>_(N_m);

4. there is an exact sequence

       1 -> Q_w -> H_w -> C_m -> 1;

5. `Q_w^ab=1`;
6. the coefficient map `S -> H_w` is injective if and only if `Q_w != 1`;
7. every homomorphism from `Q_w` to a finite group is trivial.

Consequently, on the two-generator simple reduction,
`kl-holds-over-two-generator-simple-groups` is exactly the assertion
`Q_w != 1` for every `S`, `m` and `w` above.  No assertion of that
nontriviality is part of this theorem.

If `S` is finitely generated, then so is `Q_w`.  Malcev residual finiteness
for finitely generated linear groups then strengthens clause 7: every
finite-dimensional linear representation of `Q_w` over any field is
trivial.  Thus a nontrivial `Q_w`, if proved to exist, is necessarily an
infinite perfect group invisible to finite quotients and exact
finite-dimensional linear separation.
