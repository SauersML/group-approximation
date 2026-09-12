---
rg: 2
id: leavitt-rfd-entry-packets-satisfy-kl
kind: claim
title: Leavitt equations whose coefficient entries generate a residually finite-dimensional algebra inject
invalidates: [leavitt-kl-violation-from-pure-chart-packets]
distinct_from:
  three-root-asymmetric-kl-word-has-finite-core-pushout: that treats coefficients generating one finite subgroup; this covers the infinite matrix groups over every residually finite-dimensional entry algebra, including both free coefficient charts.
  inverse-packet-conjugator-must-mix-s-and-t-charts: that is the parallel chart obstruction in the direct-finiteness corner equation; this is the Kervaire--Laudenbach version, proved by local residual finiteness.
  length-five-kl-fence-for-leavitt-equations: that fences by variable length for arbitrary coefficients; this fences by coefficient algebra for arbitrary length.
---

Let `L = L_(F_2)(1,2)`, fix `n >= 1` and a complete prefix code identifying
`L` with `M_n(L)`, and let `A <= L` be a unital subalgebra that is residually
finite-dimensional: its finite-dimensional representations separate its
elements.  If every coefficient of a nonsingular `w in R^x * <t>` lies in the
image of `GL_n(A)`, then the coefficient map `R^x -> (R^x * <t>)/<<w>>` is
injective.

Instances:

- the pure `s`-chart `A_s = F_2<s_0, s_1>` and the pure `t`-chart
  `A_t = F_2<t_0, t_1>`, which are free algebras inside `L`;
- every finitely generated commutative subalgebra;
- every finite subalgebra, which recovers the finite constant packets of
  `three-root-asymmetric-kl-word-has-finite-core-pushout`.

Contrapositive, as a search rule: a violating packet must have entries that
generate a subalgebra of `L` which is not residually finite-dimensional.  A
sufficient reason for that is a one-sided inverse pair `x y = 1 != y x` among
the entries, as with `t_0 s_0 = 1 != s_0 t_0`.  The Leavitt compression defect
is therefore not a heuristic ingredient of a candidate.  Some
non-residually-finite-dimensional entry behaviour is forced.
