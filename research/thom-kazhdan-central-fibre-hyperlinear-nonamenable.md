---
rg: 2
id: thom-kazhdan-central-fibre-hyperlinear-nonamenable
kind: claim
title: An exact locally reflexive property-T central fibre has a faithful hyperlinear nonamenable trace and no finite-dimensional representations
distinct_from:
  deligne-twisted-fibres-have-no-amenable-trace: That rules out amenable traces in Deligne's nontrivial fibres but does not know that their canonical traces are hyperlinear; Thom's LEF example makes the marked fibre Connes embeddable and also exact.
  exact-fd-invisibility-has-no-general-hs-robustification: That uses a finitely presented sofic solution group to refute normalized-HS robustification; this gives a central finite-order mark in an exact LEF property-T group and records the operator-algebraic central fibre.
  exact-local-reflexivity-does-not-promote-hyperlinear-traces: That separates hyperlinear from MF traces using the repository witness; this separates hyperlinear from amenable/quasidiagonal traces while adding property T and complete finite-dimensional invisibility.
artifacts:
  - research/artifacts/cstar-regularity-trace-promotion-audit-2026-08-23.md
  - research/artifacts/thom-0810-2180-verified.md
---

**ESTABLISHED.**  There are a finitely generated exact LEF property-`(T)`
group `G`, a nontrivial central element `j` of prime order, and a nontrivial
central-character summand

```text
B_chi = p_chi C*_r(G)
```

such that:

1. every finite-dimensional unitary representation of `G` kills `j`, even
   though every finite window containing `j` has an exact finite-group model
   retaining it;
2. `B_chi` is separable, unital, exact, locally reflexive, and has C-star
   property `(T)`;
3. its normalized canonical trace is faithful and hyperlinear;
4. `B_chi` has no nonzero finite-dimensional representation, no amenable
   trace, and is not quasidiagonal.

Take Thom's first group

```text
G=G_0(F_p[t,t^{-1}]) / direct_sum_(n>=0) F_p t^n
```

and `j=e_15(t^{-1})`.  Conjugation by `diag(t,1,1,1,1)` induces a surjective
endomorphism with central kernel containing `j`.  Its whole kernel lies in
the finite residual: for a finite quotient `q`, repetition among the
equal-index kernels of `q alpha^n`, followed by cancellation using
surjectivity, gives `ker(alpha)<=ker(q)`.  Malcev residual finiteness of
finitely generated linear groups upgrades this to invisibility in every
finite-dimensional unitary representation.  Thom proves property `(T)` and
the exact LEF-window statement.

The group is exact because it is an extension of the exact linear group
`SL_3(F_p[t,t^{-1}])` by its amenable upper-unipotent radical modulo the
central subgroup.  For a nontrivial character `chi` of `<j>`, a
finite-dimensional representation of `B_chi` would pull back to one of `G`
with `j` acting by `chi(j)`, impossible.  Hyperlinearity follows by cutting
the Connes-embeddable algebra `L(G)` by `p_chi`.  Brown's property-`(T)`
amenable-trace theorem then excludes every amenable trace; quasidiagonality is
excluded with it.

This is the precise firewall against promoting the Leavitt marked trace by
exactness, local reflexivity, property `(T)`, or exact local finite models.
The missing hypothesis must lift/repair the tracial-ultraproduct model; LLP or
normalized-HS stability does, while these properties do not.
