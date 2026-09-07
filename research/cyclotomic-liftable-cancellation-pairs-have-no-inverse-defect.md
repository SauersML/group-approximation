---
rg: 2
id: cyclotomic-liftable-cancellation-pairs-have-no-inverse-defect
kind: claim
title: A cancellation pairing without an odd integral dependence lifts cyclotomically and forces the reverse inverse
distinct_from:
  dykema-heister-juschenko-bounded-rank-direct-finiteness: that imports exhaustive exclusions at bounded support sizes; this gives an exact lattice certificate excluding individual cancellation templates at every support size.
  lifted-trace-detects-finite-subgroup-projectives: that lifts projective traces and detects finite-subgroup classes; this lifts the entire prescribed product identity using roots of unity and requires no finite support subgroup.
artifacts:
  - research/artifacts/cancellation-phase-lift-literature-audit-2026-09-07.md
  - research/artifacts/c4-cancellation-needs-eighth-root-phases-2026-09-07.md
---

Let G be any group, B=sum_i [t_i] and A=sum_j [s_j] in F_2[G], with
distinct support labels on each side and BA=1. Choose one product cell
(i_0,j_0) with t_(i_0)s_(j_0)=1. Pair every other cell with an equal
product cell. Such a pairing exists because the identity fiber is odd
and every other product fiber is even.

For each oriented pair e=((i,j),(k,l)), put

    v_e=e_i+f_j-e_k-f_l in Z^(m+n),

where e_i and f_j are the separate row and column basis vectors. Let
V:Z^E->Z^(m+n) have these columns. If

    V a=0  =>  sum_e a_e is even, for every a in Z^E,    (CPL1)

then AB=1 as well. Equivalently, a strict one-sided inverse requires
an integral relation

    sum_e a_e v_e=0,       sum_e a_e odd                (CPL2)

for EVERY choice of pairing and pivot as above. Orientation choices
do not affect this criterion.

The proof constructs row and column coefficients among roots of unity
of order a power of two, so each prescribed pair cancels in characteristic
zero. After normalizing the pivot, the forward product is exactly one.
Direct finiteness in characteristic zero forces the reverse identity,
which reduces back to F_2 because every such phase reduces to one.

The criterion has an exact finite alternative. Either (CPL2) exists,
or for some N>=1 there are row/column phase exponents q in
(Z/2^N)^(m+n) with

    V^T q = 2^(N-1) 1 mod 2^N.                         (CPL3)

Writing r=rank_Q V and d_r for its largest nonzero Smith invariant,
one may take N<=1+v_2(d_r)<=r+1<=m+n-1. The sharper bound only uses
Smith directions carrying a negative character value. The trivial
empty-pair case needs no phase calculation.

This is stronger than testing real signs, which only checks (CPL3) at
N=1. The attached C_4 example has no real signing but has an eighth-root
phase solution; its integer column lattice has no nonzero dependence.
Thus an odd incidence circuit modulo two is not enough to satisfy the
necessary obstruction (CPL2).

This implements a finite closed verification circuit in an exact form:
the obstruction must balance integer row and column incidences while
retaining odd total multiplicity. It is a necessary condition, not a
construction of a counterexample. Failure of (CPL1) gives no assertion
that the reversed product has a surviving term, or that distinct formal
support labels remain distinct in a presented group. No statement of
novelty is made for the signature method or characteristic-zero input.

`central-sign-survival-forces-reverse-cancellation` strengthens this
filter further by allowing noncommuting coefficients. Its necessary
obstruction is an odd identity among the actual matching relators,
before abelianization. The present lattice test remains useful because
Smith normal form gives a terminating finite decision procedure for
this scalar subclass; central-sign survival in an arbitrary presented
group has no such decision procedure supplied here.
