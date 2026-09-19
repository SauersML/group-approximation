---
rg: 2
id: sl3-homogeneous-ce-is-common-cocycle-spatialization
kind: claim
title: Homogeneous-quotient embeddability is common cocycle spatialization of the noncompact lattice returns
artifacts:
  - research/sl3-homogeneous-cocycle-spatialization-proof.md
distinct_from:
  free-lattice-ce-is-joint-ultrapower-spatialization: that treats the rank-one free lattice, where chosen generator returns define an honest action and have no relator holonomy; this treats the higher-rank lattice and retains the compression cocycle and all lattice relations.
  dense-s-arithmetic-translation-algebra-is-amplified-profinite: that identifies the stable profinite base and its right-lattice action; this gives the exact finite-corner ultrapower condition equivalent to embeddability of the crossed product.
  homogeneous-quotient-has-a-quantized-hecke-dent: that proves stabilization does not dilute the spherical leak; this identifies the simultaneous noncompact-return spatialization which stabilization still leaves open.
---

Put

```text
G=SL_3(Q_p), A=SL_3(Z[1/p]),
Q=L^infinity(G) rtimes A=N tensor B(ell^2),
```

and let the torsion-free cocompact lattice `Lambda'<G` act on `Q` by the
right-translation action `alpha` from `(DT2)`.  Choose a nonzero finite
projection `q in Q`.  For every `g in Lambda'`, choose a partial isometry
`v_g in Q`, with `v_e=q`, such that

```text
v_g^*v_g=alpha_g(q),       v_gv_g^*=q.
```

On `B=qQq` define

```text
beta_g(x)=v_g alpha_g(x)v_g^*,
c(g,h)=v_g alpha_g(v_h)v_(gh)^*.                       (HCS1)
```

Then `(beta,c)` is a trace-preserving cocycle action of `Lambda'` on the
Connes-embeddable finite factor `B`, and

```text
L^infinity(G/Lambda') rtimes A is Connes embeddable     (HCS2)
```

if and only if there exist one trace-preserving embedding
`pi:B->R^omega` and unitaries `U_g in R^omega`, `g in Lambda'`, with
`U_e=1`, satisfying simultaneously

```text
U_g pi(x) U_g^*=pi(beta_g(x))                  (x in B),
U_gU_h=pi(c(g,h))U_(gh)                        (g,h in Lambda').       (HCS3)
```

Since `Lambda'` is finitely presented, `(HCS3)` may equivalently be imposed
on a finite symmetric generating set together with its finitely many
twisted relator equations.  Thus the open content is one common embedding
of the profinite corner and a simultaneous solution of a finite return
holonomy system, not Connes embeddability of the base or implementation of
one return.

Every cyclic subsystem is separately solvable.  For each fixed nontrivial
`g`, amenable crossed-product permanence makes
`q(Q rtimes_alpha <g>)q` Connes embeddable and hence supplies some
`(pi_g,U_g)`.  These separate embeddings do not imply `(HCS3)`.  Even if
individual return implementers are placed over one common `pi`, covariance
only shows that

```text
Z_(g,h)=(pi(c(g,h))U_(gh))^* U_gU_h
```

lies in `pi(B)' cap R^omega`; it does not show `Z_(g,h)=1`.  Killing this
relative-commutant two-cocycle, coherently across the lattice relators, is
exactly the remaining joint-spatialization problem.

DERIVATION
sl3-homogeneous-cocycle-spatialization-proof
