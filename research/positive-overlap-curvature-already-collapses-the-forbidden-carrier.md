---
rg: 2
id: positive-overlap-curvature-already-collapses-the-forbidden-carrier
kind: claim
title: Positive source-specific overlap and disjoint tag covariance already collapse the forbidden carrier
distinct_from:
  localized-non-ce-leakage-forces-cross-gram-overlap: that lower-bounds cross-Gram overlap from capacity and localized non-CE energy; this combines it with a representation-theoretic upper bound and eliminates the need for near-full polar alignment.
  disjoint-tag-covariance-controls-cross-gram: that upper-bounds arbitrary cross-Gram overlap between disjoint tag types; this closes the two-sided curvature ledger for the source-specific leakage packet.
  shared-bcs-eight-slice-full-overlap-actuator: that asks for overlap arbitrarily close to the whole source carrier; this proves that no such amplification is needed for mark collapse.
---

Work in a finite matrix algebra with normalized trace.  Let `T_1,T_2` be the
two exit partial isometries of
`localized-non-ce-leakage-forces-cross-gram-overlap`, with total source mass

```text
s=tau(T_1^*T_1)+tau(T_2^*T_2),
```

packet capacity `c=tau(C)`, leakage functional `Lambda`, and

```text
Theta=||T_1^*T_2||_2^2.
```

Assume the two sources carry disjoint exact types `pi_1,pi_2` of one fixed
finite tag group `H`, the ambient exit representation is `rho`, and put

```text
E_tag=sum_(i=1,2) sum_(h in S_H)
      ||rho(h)T_i-T_i pi_i(h)||_2^2.                    (POC1)
```

Then

```text
s-c <= 2 Lambda/beta_B^corner + 4 E_tag/kappa(H,S_H).  (POC2)
```

In particular, if the packet construction supplies constants `a>0` and
`K<infinity` such that a forbidden carrier `P` satisfies

```text
s-c >= a tau(P)-o(1),                                  (POC3)
Lambda <= K E_rel+o(1),                                (POC4)
```

and the tag covariance defects in `(POC1)` are defining-word defects, then

```text
tau(P)
 <= (2K/(a beta_B^corner)) E_rel
    +(4/(a kappa(H,S_H))) E_tag+o(1).                  (POC5)
```

Thus every canonical matrix microstate with vanishing relator defect kills
the forbidden carrier.  No near-full cross-Gram estimate, polar-gauge
amplification, or recursive return is required.

## Proof

The source-specific matrix-only inequality gives

```text
Theta >= (s-c)/2-Lambda/beta_B^corner.                 (POC6)
```

The finite-group intertwiner gap for two disjoint tag types gives

```text
2 Theta
 =sum_(i!=j)||T_i^*T_j||_2^2
 <=(4/kappa(H,S_H)) E_tag,                             (POC7)
```

so `Theta<=2 E_tag/kappa(H,S_H)`.  Substitute this in `(POC6)` and
rearrange to obtain `(POC2)`.  Equations `(POC3)--(POC4)` then give
`(POC5)`.

## Why this is finite-dimensional-only

The lower bound `(POC6)` consumes the corner-localized non-CE matrix
compactness gap.  It is not valid in the exact non-CE tracial witness, where
a nonzero leakage corner may satisfy every BCS relation.  Consequently the
combined inequality does not collapse the regular or HALT-side exact
representation.  The exact witness may use the orthogonal-coordinate escape;
matrices cannot use it while keeping `Lambda` small.

## Remaining construction boundary

The analytic ledger is now closed.  A group compiler still has to realize,
on the *same selected Fanizza carrier*:

1. the surplus `(POC3)`;
2. localized reduction `(POC4)` for the actual leakage projections; and
3. two disjoint tag covariances `(POC1)` without imposing a universal
   finite-packet selector which would destroy exact completeness.

Items 2 and 3 must be mixed, mark-relative relations.  Independent context
packets, source-only moments, and a finite central sign do not imply them.
The important reduction is that their success immediately yields carrier
collapse; the stronger full-overlap actuator is unnecessary.
