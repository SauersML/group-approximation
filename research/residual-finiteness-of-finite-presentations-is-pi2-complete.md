---
rg: 2
id: residual-finiteness-of-finite-presentations-is-pi2-complete
kind: claim
title: Residual finiteness of finitely presented groups is Pi-zero-two complete
distinct_from:
  rf-fp-completeness-reduces-to-subgroup-separability-hardness: that reduces this cell to separability of finitely generated subgroups of F x F; this is the completeness statement itself, attacked by a machine-built family that uses no separability input.
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that classifies recursive and enumerated presentations at level three and supplies the Pi-zero-two upper bound on finite presentations; this asks for the matching lower bound on finite presentations.
  kms-arbitrarily-hard-fp-rf-groups: that imports hard decidable word problems inside finitely presented residually finite groups; this is about recognizing residual finiteness among finite presentations.
---

OPEN.  For the recursive coding of finite group presentations,

```text
RF_fp     is Pi^0_2-complete,
NONRF_fp  is Sigma^0_2-complete.                                   (RFC1)
```

Since a finitely presented group is LEF iff it is residually finite
(Vershik--Gordon), (RFC1) is the same statement for `LEF_fp`.  This is cell 3
of [[open-cells-arithmetical-complexity-of-group-properties]] (the
"residually finite Higman problem" cell of
[[arithmetical-complexity-table-of-group-properties]]).

Membership is the finite-presentation clause of
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]]: every
word is trivial (r.e.) or separated by a finite quotient (r.e.).  Only
hardness is missing.

## Attempts

1. **Subgroup separability in `F x F`**
   ([[rf-fp-completeness-reduces-to-subgroup-separability-hardness]]).  No new
   leverage: a finitely generated subgroup of `F x F` is a fibre product over a
   finitely presented quotient `Q`, and it is profinitely closed iff `Q` is
   residually finite (Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506v5,
   Lemma 5.2 and Remark 5.4).  Hardness there is hardness here.
2. **Higman compilers.**  Die for a structural reason: the positive branch of a
   reduction must consist of finitely presented residually finite groups,
   which have decidable word problems, while the existing rope is not even LEF
   ([[mikhailova-positive-rope-is-not-lef]]).
3. **Pumped Minsky-machine groups (in progress, lane `ex-complexity-sofic`,
   2026-09-12).**  KMS build, for every Minsky machine `M`, a finitely
   presented group `G(M)` in `A_p^2 A cap ZN_(K+1) A` that simulates `M`
   (Theorem 4.3) and is residually finite when `M` is sym-universally halting
   (Theorem 4.17); for depth functions they pump `M` into a machine `M_n` with
   two extra glasses (proof of Theorem 3.9).  The plan:
   - (a) a uniform clocked search machine `M_e` which is sym-universally
     halting when `e in INF` and has a divergent, predecessor-free input when
     `e in FIN`;
   - (b) `G(M_n)` residually finite for sym-universally halting `M`, via
     residual finiteness of the semigroup `S(M_n)` and a transfer from `S(M)`
     to `G(M)` through the basis of Lemma 4.14;
   - (c) on `FIN`, the divergent input lies in the profinite kernel of
     `G(M_n)`: in a finite quotient the operator of `*a_(K+1)` on the image of
     the abelian normal subgroup `T` satisfies `P^D = P^(2D)`, so pumping to
     `(2D, D)`, collapsing to `(D, D)`, unpumping and stopping identifies the
     input word with the accepted word.

   Where it may die: KMS display the group relations only for the three basic
   command forms, while `M_n` uses combined commands; and finiteness of
   divisors (their Lemma 3.5(a)) has to be rechecked with a clock glass that
   is never emptied.  Any group of this family is solvable, hence amenable and
   sofic, so the route says nothing about soficity.
