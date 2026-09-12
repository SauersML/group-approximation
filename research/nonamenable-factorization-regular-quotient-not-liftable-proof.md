---
rg: 2
id: nonamenable-factorization-regular-quotient-not-liftable-proof
kind: route
title: Descent would turn a reduced hypertrace into an invariant mean
target: nonamenable-factorization-regular-quotient-not-liftable
requires:
  - amenable-trace-descends-through-locally-liftable-quotient
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `tau_f` and `tau_r` denote the canonical traces on the full and reduced
group algebras.  They satisfy `tau_f=tau_r o q`.  Brown's Theorem 4.1.9 says
that factorization of `G` is equivalent to amenability of `tau_f`.

Suppose (1) were locally liftable.  The prerequisite descent theorem would
make `tau_r` amenable.  In the regular representation on `ell^2(G)`, an
amenable trace extends to a `C*_r(G)`-central state on `B(ell^2(G))`.
Restricting this state to the diagonal algebra `ell^infinity(G)`, centrality
under the regular group unitaries gives a left-translation-invariant mean.
Thus `G` would be amenable, contrary to the hypothesis.  Hence `q` is not
locally liftable.

For `F_2`, choose a descending sequence of finite-index normal subgroups with
trivial intersection.  The regular representations of the finite quotients
are honest finite-dimensional representations whose normalized characters
converge pointwise to the canonical character.  They make `tau_f`
quasidiagonal, hence amenable, and in particular prove the factorization
property needed above.  Since `F_2` is nonamenable, the conclusion applies.

The GNS representation of `tau_f` is the regular representation, so its image
is exactly `C*_r(G)`.  This proves the GNS statement.

**Trust boundary.**  Brown's factorization equivalence and the amenable-trace
hypertrace characterization are imported.  The invariant-mean restriction
and the residual-finiteness approximation for `F_2` are explicit.  No
conditional literal-group premise is used.
