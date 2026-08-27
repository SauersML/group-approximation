---
rg: 2
id: periodic-conductor-plateaux-pay-a-shared-root-seam
kind: claim
title: Periodic dyadic conductor plateaux pay a constant shared-root seam
distinct_from:
  periodic-dyadic-root-clocks-keep-weyl-overlap: that gives one fixed abelian clock with exact dyadic transport and identifies the adjacent-root relation it misses; this gives clocks of unbounded period with vanishing local transport defect and proves the missed relation retains constant normalized-HS cost.
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that closes one common finite Chevalley reservoir; this audits six separate exact reservoirs of growing period and locates the constant cost at their literal cross-chamber root identifications.
  actual-parahoric-triangle-kills-abelian-correctors: that eliminates abelian gauges on the actual forty-two-point parahoric atlas; this eliminates dilution of the remaining cross-chart seam by block-diagonal periodic conductor plateaux.
---

A periodic dyadic clock can make every fixed collection of Baumslag--Solitar
scaling tests arbitrarily accurate in normalized Hilbert--Schmidt norm.  It
cannot simultaneously dilute the first Steinberg multiplication triangle.

Let `L` be even, let `U_L` be the cyclic shift of the standard basis of
`C^L`, and let `S_L` be the permutation which lists the even positions and
then the odd positions:

```text
f(0),...,f(L-1)=0,2,...,L-2,1,3,...,L-1,
S_L e_j=e_(f(j)).                                      (PCS1)
```

The permutations `S_L U_L S_L^-1` and `U_L^2` disagree on exactly two
columns.  Therefore

```text
||S_L U_L S_L^-1-U_L^2||_2^2=4/L.                     (PCS2)
```

Bi-invariance and telescoping powers give, for every fixed `r>=1`,

```text
||S_L^r U_L S_L^-r-U_L^(2^r)||_2
 <=2(2^r-1)/sqrt(L).                                  (PCS3)
```

Hence six independent copies, one for each `A_2` root, pass every fixed
radius dyadic root-depth window with squared defect `O(C_N/L)`.  Coweight
addition and Weyl permutation of the six copies can be imposed exactly, and
an independent finite lamp packet retains

```text
tr(P)=tr(Q)=1/2,       tr(PQ)=1/4.                     (PCS4)
```

But the independent root clocks commute.  Thus the first adjacent-root
triangle has

```text
[U_12,U_23]=I,
||[U_12,U_23]-U_13||_2^2=||I-U_13||_2^2=2.             (PCS5)
```

The last equality uses `tr(U_13)=0`.  The cost is independent of `L`.
Consequently truncating a dyadic clock does not produce a plateau on which
all actual Steinberg word defects vanish.

## Exact local Heisenberg upgrade still pays at the seam

The local defect in `(PCS5)` can be repaired without changing the verdict.
Put

```text
q_L=2^L-1,       R_L=Z/q_L Z.                          (PCS6)
```

The unit `2 in R_L` has order exactly `L`: if `2^r=1 mod q_L` with `r<L`,
then `q_L` would divide the strictly smaller positive integer `2^r-1`.
For each of the six chambers take an independent finite Chevalley packet

```text
F_w=E_3(R_L)                                             (PCS7)
```

(`UT_3(R_L)` suffices for its local multiplication triangle).  The
coweight clock `(Z/L)^2` acts on each packet by the exact diagonal scaling
automorphism, and `S_3` permutes chamber factors.  Thus the resulting finite
semidirect product has, occurrence by occurrence,

- exact local Heisenberg multiplication;
- exact dyadic root scaling in every direction;
- exact Weyl transport of chamber roles; and
- exact coweight triangle and Coxeter relations.

It is not a model of the actual common `SL_3` root packet.  A root which is
literally the same arithmetic group word in two adjacent chambers lies in
two different direct factors.  In the left regular representation, for
example,

```text
||(x_13(t))_(123)-(x_13(t))_(213)||_2^2=2.              (PCS8)
```

The same constant cost occurs at every unglued wall.  Gluing these literal
occurrences identifies the chamber reservoirs and returns to the common
finite-clock situation of
`six-chamber-a2-holonomy-closes-fixed-clock-sector`, where the dyadic actor
has one common commutant corrector and the signed triangle collapses it.

There is an equivalent one-word description of the seam.  The separated
atlas moves chamber labels by an external permutation `w_12`, while the
actual arithmetic group uses the internal root word

```text
n_12=x_12(1)x_21(-1)x_12(1)                            (PCS8a)
```

(and similarly for `23`).  In the finite atlas `w_12` and `n_12` are
distinct regular group elements, so `||w_12-n_12||_2^2=2`.  Imposing their
literal equality is exactly what glues the external chamber gauge to the
common root reservoir; around the gallery it gives the internal Coxeter
word `(n_12 n_23)^3=1`.

## Block-plateau quantitative floor

The preceding calculation is stable under arbitrary block-diagonal mixtures
of fully glued and chamber-separated regular packets.  Let `g` be the total
normalized mass of the glued blocks.  On a glued block the actor fixes the
lamp and the overlap is `1/2`; on a separated block it is `1/4`.  Hence

```text
a=tr(PQ)=1/4+g/4.                                      (PCS9)
```

Every separated block breaks at least one of the six literal wall/root
identities, and a broken regular identity has squared defect `2`.  Therefore

```text
sum_(six walls) seamDefect_w^2 >=2(1-g)
                                  =2(1-4(a-1/4)).       (PCS10)
```

In particular, at the target overlap `a=1/4`, some wall has squared defect
at least `1/3`.  No choice of conductor period can reduce this floor.

This rules out abelian clocks, exact chamberwise Heisenberg clocks, and
their block-diagonal conductor plateaux as countermodels to the arithmetic
hexagon decoder.  The unrefuted escape is genuinely non-block-diagonal:
rectangular `2`-adic transport may enlarge the recovered root-label factor
while shrinking multiplicity, so that no block carries one common finite
Chevalley reservoir.  That is precisely the same-carrier/conductor-leakage
clause still open in `arithmetic-hexagon-decoding-or-conductor-leakage`.
