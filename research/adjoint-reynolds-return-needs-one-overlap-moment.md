---
rg: 2
id: adjoint-reynolds-return-needs-one-overlap-moment
kind: claim
title: One scalar overlap moment certifies the entire Schur Reynolds return
distinct_from:
  adjoint-reynolds-rank-gap-pays-every-return: that lower-bounds the full HS distance between a Reynolds projection and a returned copy; this shows that only one scalar overlap, expressible through ordinary group-word moments, has to be forced.
  compressor-covariant-packet-reynolds-return: that asks for a group gadget transporting a positive-density Reynolds core; this removes every operator-level clause not needed for the final finite-rank contradiction.
  trace-cyclic-rank-mismatch-checksum: that is the general two-product matrix lemma; this computes its canonical scalar for nested Schur packet Reynolds projections.
artifacts:
  - research/artifacts/crispr-self-hash-compiler-2026-08-20.md
---

Let `R_A,R_B` be the orthogonal Reynolds projections on the adjoint Hilbert
space of an exactified Schur packet, with `R_B<=R_A`, and let `T=Ad_(U(t))`
be any unitary adjoint actuator.  Put

```text
Theta(U)=tr_ad(R_A T^* R_B T R_A).                     (SOM1)
```

Then

```text
Theta(U)<=tr_ad(R_B),                                  (SOM2)

tr_ad(R_A)-Theta(U)
  =||(I-R_B) T R_A||_(HS,ad)^2.                        (SOM3)
```

Consequently, if one finite group-word cell forces only

```text
Theta(U)>=tr_ad(R_A)-K eta,                            (SOM4)
```

where `eta` is its named relator-error scale, then the Schur rank-gap theorem
immediately gives

```text
c_f q^2
 <=tr_ad(R_A)-tr_ad(R_B)
 <=K eta.                                              (SOM5)
```

Here `q` is forbidden selector mass and one may take
`c_f=3/(4D^2K_f)` in the general predicate packet, or `3/16` for the fixed
support packet.

Moreover, for exact packet operators

```text
R_A=|A|^-1 sum_(a in A) Ad_(U(a)),
R_B=|B|^-1 sum_(b in B) Ad_(U(b)),                     (SOM6)
```

the overlap has the finite ordinary-word moment expansion

```text
Theta(U)=1/(|A|^2|B|) sum_(a_1,a_2,b)
 |tr_d(U(a_1)U(t)^*U(b)U(t)U(a_2))|^2.                (SOM7)
```

Thus the missing return theorem may target one finite scalar moment list,
not a pointwise conjugacy of packet tables or reconstruction of a whole
multiplicity space.  The theorem does not assert `(SOM4)`; constructing a
group actuator which forces it while retaining the exact infinite witness is
the separate open claim `schur-reynolds-one-overlap-actuator`.
