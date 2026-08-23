---
rg: 2
id: llp-regular-dominating-completion-forces-nonhyperlinear
kind: claim
title: LLP of a nonamenable representation completion dominating the regular representation forces non-hyperlinearity
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that consumes LLP of the FULL group C-star algebra together with Kazhdan and non-residual-finiteness; this consumes LLP of one possibly proper representation quotient and needs neither property (T) nor non-residual-finiteness.
  nonce-factor-in-group-factor-corner-forces-nonhyperlinear: that embeds a prescribed non-CE tracial algebra into a canonical group-factor corner; this uses an LLP contradiction at an intermediate representation C-star algebra and constructs no corner.
---

**THEOREM (Paulsen--Rahaman--Samei, arXiv:2606.18369v1, Theorem
4.6, contraposed).**  Let `G` be a discrete group and let
`pi : G -> U(H)` be a unitary representation.  Assume

```text
lambda_G is weakly contained in pi,
pi is not an amenable representation, and
C^*_pi(G) has Kirchberg's local lifting property.              (IRL1)
```

Then `G` is not hyperlinear.

Indeed, Theorem 4.6 states that if `G` is hyperlinear, `pi` is
nonamenable, and `lambda_G prec pi`, then `C^*_pi(G)` does **not** have
LLP.  Its proof uses the quotient

```text
C^*_pi(G) -> C^*_lambda(G)
```

and the canonical-trace embedding of the reduced algebra into `R^omega`
supplied by hyperlinearity; their Corollary 4.2 then contradicts LLP
because `C^*_pi(G)` has no amenable trace.

This is a genuine enlargement of Cairn's LLP search space.  The algebra
whose LLP is needed may be a proper quotient of `C^*(G)`.  In particular,
no finite-dimensional residual argument, Kazhdan hypothesis, or
non-residual-finiteness hypothesis occurs in `(IRL1)`.

The hypothesis that `pi` is nonamenable is load-bearing.  Likewise
`lambda_G prec pi` is what produces the quotient onto the reduced group
C-star algebra.  LLP of an arbitrary representation completion does not
give the conclusion.

Paulsen--Rahaman--Samei Theorem 4.9 supplies the most concrete
specialization.  If `G` is nonamenable and `D` is an algebraic ideal in
`ell^infinity(G)` containing `c_00(G)` such that the canonical completion
is proper,

```text
C^*(G) != C^*_D(G),                                   (IRL2)
```

then `C^*_D(G)` has no amenable trace; if `G` were hyperlinear, it could
not have LLP.  Thus LLP of one such proper Brown--Guentner completion is
already a non-hyperlinearity certificate.  The theorem does not require
that `C^*_D(G)` be distinct from the reduced completion, so calling every
instance "strict exotic" would overstate its hypothesis.
