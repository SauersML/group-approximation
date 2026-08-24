---
rg: 2
id: finite-reservoir-compactness-lifts-ucp-repairs
kind: claim
title: Packetwise ucp repairs inside one finite-dimensional ideal reservoir compactify to a genuine ucp lift
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  fd-representation-packets-never-obstruct-ucp-sections: that says a repair always exists for each finite packet separately, with no control on where it lives; this says a single finite-dimensional reservoir serving all packets upgrades those repairs to one exact ucp lift, and is vacuous without that uniformity.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that identifies LLP of a colimit with local ucp splitting of one relator extension; this is a general compactness lemma about a single finite-dimensional operator system over an arbitrary RFD algebra, and mentions no group, no colimit and no relator.
  chordal-partial-positive-operator-matrices-lift: that completes a partially specified positive operator matrix along a chordal pattern; this converts finite-dimensional-representation-tested repairs into a norm-exact completely positive map and performs no matrix completion.
---

**ESTABLISHED.**  Let `A` be a unital **RFD** C-star algebra, `I` a closed
two-sided ideal, `q:A->>Q=A/I`.  Let `E subset Q` be a finite-dimensional
operator system, let

```text
t:E->A     unital, self-adjoint, linear,   q t = id_E,     (FR1)
```

and let `L subset I` be a **finite-dimensional** linear subspace.  Suppose
that for every finite collection `R` of finite-dimensional representations of
`A` there exists a linear map

```text
d_R:E->L    with   q(t+d_R)=id_E   and
rho o (t+d_R) ucp for every rho in R.                      (FR2)
```

Then there is a single `d in L(E,L)` for which

```text
s:=t+d : E -> A   is ucp and   q s = id_E.                 (FR3)
```

In particular `E` has an exact ucp lift into `A`.

Proof: `finite-reservoir-compactness-lifts-ucp-repairs-proof`.

**What carries the weight.**  `q(t+d_R)=id_E` is automatic from `L subset I`;
the content of `(FR2)` is only the ucp condition, and the content of the lemma
is only that ONE finite-dimensional `L` serves every packet.  Dropping that
uniformity makes the hypothesis vacuously true and the conclusion false in
general: by `fd-representation-packets-never-obstruct-ucp-sections`, for every
finite packet `R` there is always *some* repair, taken from a subspace of `I`
that may grow with `R`.  So this lemma is exactly a bounded-reservoir
statement, and everything it can ever buy is bought by the uniform bound.

**RFD is used twice and cannot be dropped.**  Once to produce finitely many
finite-dimensional representations that uniformly norm the finite-dimensional
space `L` (this is what makes the family of admissible `d_R` bounded, hence
precompact); once at the end, where `rho o s` ucp for *all* finite-dimensional
`rho` upgrades to `s` completely positive only because the finite-dimensional
representations are jointly faithful on `A`.  Without RFD the second step
fails outright: `rho o s` ucp for every finite-dimensional `rho` says nothing
about matrices over `A` that no finite-dimensional representation sees.

**Scope.**  Nothing here is specific to group algebras, and nothing here makes
the lifting problem finite: `(FR2)` still quantifies over all finite packets of
finite-dimensional representations.  What it removes is the infinite
bookkeeping -- one no longer has to construct a map compatible with infinitely
many representations at once, only to bound the depth of the corrections.
Instantiated at the triangle relator extension this is
`local-ucp-sections-from-finite-relator-reservoir`.
