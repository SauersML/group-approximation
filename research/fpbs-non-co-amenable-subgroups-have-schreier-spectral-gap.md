---
rg: 2
id: fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap
kind: claim
title: Non-co-amenable subgroups have Schreier spectral radius below one, so a nonamenable group in which every infinite subgroup is co-amenable is periodic with no infinite amenable subgroup
distinct_from:
  fpbs-no-amenable-wq-normal-class-nonuniqueness: that class excludes infinite amenable wq-normal subgroups only; this shows that the smaller residual class, where every infinite subgroup is co-amenable, excludes every infinite amenable subgroup, and in particular every element of infinite order.
  fpbs-central-amenable-relative-threshold-is-pu: that computes a relative threshold along amenable subgroups when there is an infinite centre; this is a group-theoretic spectral statement about Schreier graphs, with no percolation content.
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `S` a finite symmetric
generating set with `|S| = D`, and `I <= Gamma` a subgroup. Let
`X = Sch(I\Gamma, S)` be the Schreier graph on right cosets, `P` its simple
random walk operator on `ℓ^2(I\Gamma)`, and
`rho_I = limsup_m P^m(I,I)^(1/m)`. Call `I` **co-amenable** if there is a
`Gamma`-invariant mean on `ℓ^∞(I\Gamma)`.

(a) If `I` is not co-amenable, then `X` has edge-isoperimetric constant
`h = inf_F |∂F|/|F| > 0` over finite nonempty `F`, where `∂F` is the set of
arcs `(x,s)` with `x in F` and `xs ∉ F`. Moreover

```text
rho_I <= ||P|| <= 1 - h^2/(2 D^2) < 1 .
```

(b) If `Gamma` is nonamenable and `I` is amenable, then `I` is not co-amenable,
and so `rho_I < 1`.

(c) Suppose `Gamma` is nonamenable and every infinite subgroup of `Gamma` is
co-amenable. Then:
- `Gamma` has no infinite amenable subgroup;
- in particular `Gamma` is periodic, and every infinite subgroup of `Gamma` is
  nonamenable;
- every infinite normal subgroup `N` has amenable quotient `Gamma/N`, since for
  normal `N` an invariant mean on `N\Gamma` is exactly an invariant mean on the
  group `Gamma/N`.

Members of the class in (c): any nonamenable group whose infinite subgroups all
have finite index, for example Ol'shanskii's nonamenable Tarski monsters.

Non-members: every nonamenable group with an element of infinite order. That
includes:
- all torsion-free groups;
- all finitely generated linear groups, since finitely generated periodic
  linear groups are finite (Burnside–Schur);
- acylindrically hyperbolic groups;
- higher-rank lattices;
- Burger–Mozes groups.

Every product `T x T'` of infinite groups with `T'` nonamenable is also a
non-member: the factor `T` is infinite and its quotient `T'` is nonamenable.

(a) and (b) are textbook facts: Følner implies an invariant mean; Eymard's
induction of means; the Cheeger inequality; `P^m(x,x) <= ||P||^m`. They are
proved in full in the route, so no import is needed.

**Proof.** `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap-proof`.
