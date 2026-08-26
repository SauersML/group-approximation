---
rg: 2
id: higman-four-cycle-intrinsic-mf-seed
kind: claim
title: Higman's four-cycle is the concrete intrinsic torsion-free MF-seed test
root: true
distinct_from:
  torsion-free-fp-ah-mf-radical-seed: that asks for any intrinsic seed; this fixes Higman's four-generator presentation and identifies the exact marked point-operator-norm statement still missing.
  map-matricial-stability-non-mf: that assumes full matricial stability of an arbitrary minimally almost periodic group; this candidate needs only collapse of one marked Higman generator and does not assume correction to exact representations.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that is a normalized-Hilbert--Schmidt reduction; this asks for operator-norm collapse and cannot consume HS-nearness of the four occurrences.
artifacts:
  - research/artifacts/higman-cycle-bs-stability-gate-2026-08-21.md
---

**OPEN.**  Let

```text
Hig=<g_0,g_1,g_2,g_3 |
     g_i g_(i+1) g_i^(-1)=g_(i+1)^2, i in Z/4Z>.       (HMF1)
```

Prove, without Property `(T)` or any Kazhdan input, that for every sequence
of finite-dimensional unitary tuples `(U_(0,n),...,U_(3,n))` satisfying

```text
max_i ||U_(i,n) U_(i+1,n) U_(i,n)^* - U_(i+1,n)^2|| -> 0
                                                               (HMF2)
```

in operator norm, one has

```text
||U_(0,n)-1|| -> 0.                                    (HMF3)
```

This is the exact marked point-operator-norm collapse needed for the
intrinsic seed.  Cyclic symmetry then gives `(HMF3)` for every generator;
finite presentation converts `(HMF2)--(HMF3)` into triviality of every
homomorphism from `Hig` to a norm matrix corona.  Hence

```text
Rad_MF(Hig)=Hig,                                       (HMF4)
```

and any nonidentity generator is a valid marked radical element.

## Why this is the narrow torsion-free candidate

The following are literature/background facts, not premises of a completed
no-literature endpoint in this repository:

- `Hig` is finitely presented, infinite, and torsion-free;
- `Hig` is acylindrically hyperbolic (Minasyan--Osin, Corollary 4.26; also
  recoverable from Martin's cubical action);
- Higman's no-finite-quotient theorem and Malcev residual finiteness for
  finitely generated linear groups imply that every exact finite-dimensional
  unitary representation of `Hig` is trivial.

Thus the group-theoretic shape required by
`torsion-free-fp-ah-mf-radical-seed` is already known for this one explicit
presentation.  But those facts, including torsion-freeness, nontriviality,
and acylindrical hyperbolicity, must be internalized before this node can be
a premise of the requested unconditional no-literature Lean endpoint.
Exact finite-dimensional sterility is only a calibration and does not imply
`(HMF3)`.

## The four-seam gate

The established HS theorem
`higman-hs-microstates-are-near-glued-exact-bs-cycles` replaces each of the
four relations by an exact `BS(1,2)` packet and leaves four repeated-generator
seams.  It does not prove `(HMF3)`: normalized-HS closeness does not control
operator norm, and the known split clocks retain a four-matcher product
holonomy.

An operator-norm packet proof would have to establish both of the following
new statements, with dimension-independent moduli:

1. same-dimension operator-norm correction of an approximate `BS(1,2)` pair
   to an exact pair;
2. collapse of every cyclic family of four exact pairs whose four incoming
   and outgoing generator occurrences converge to one another in operator
   norm.

Even the first local statement is not available: Eilers--Shulman--Sorensen
explicitly leave operator-norm matricial stability of the metabelian groups
`BS(1,m)`, `m>1`, open.  Bypassing local correction is allowed, but it must
still prove the direct four-relation implication `(HMF2)=>(HMF3)`.

Consequently this node records a concrete candidate and an exact analytic
seam, not a solution.  Establishing it, together with internal proofs of the
background group facts, would provide the no-`(T)` input for the torsion-free
routing saturation theorem.
