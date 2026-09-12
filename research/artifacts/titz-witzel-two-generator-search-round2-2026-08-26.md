# Titz--Witzel two-generator search, round 2 (2026-08-26)

This artifact reports exact finite enumeration and heuristic annealing for the
gate in `titz-witzel-sofic-gate-two-generators-four-approximate-relators`.
The accompanying program is
`research/artifacts/titz_witzel_two_generator_search.cpp`.

The finite data below is **not** used to prove an asymptotic lower bound.
The two rigorous consequences extracted from the search are written and
proved separately in:

* `titz-witzel-cyclic-normalizer-ansatz-collapses-mark`;
* `titz-witzel-central-square-lifts-collapse-mark`.

Their dependency-free checks are respectively
`titz-witzel-cyclic-normalizer-check.py` and the extended
`titz-witzel-involution-sandwich-check.py`.

## Reproduction

From the repository root:

```text
c++ -O3 -std=c++17 \
  research/artifacts/titz_witzel_two_generator_search.cpp -o /tmp/tw2
python3 research/artifacts/titz-witzel-cyclic-normalizer-check.py
python3 research/artifacts/titz-witzel-involution-sandwich-check.py
```

The program uses image-table permutations and right-to-left word action.  It
reconstructs `h,a,x,c,f,d,s,rho,b` from `(TW2G1)`.  The four reported defects
are, in order,

```text
c^2,
rho^2 e^(-1)u^(-1),
b x u^(-1)d^(-1),
a c d b.
```

Every searched `e` is an exact involution.

## Exhaustive single-cycle search

In `exhaust-cycle` mode, `u` is the standard `n`-cycle.  Simultaneous
conjugacy makes this representative exhaustive for pairs in which `u` is an
`n`-cycle.  A recursion enumerates every involution `e`; its `count` column is
the corresponding telephone number.  Run:

```text
for n in 3 4 5 6 7 8 9 10 11 12 13 14; do
  /tmp/tw2 "$n" 0 0 exhaust-cycle 2>/dev/null | head -1
done
```

Output:

| `n` | involutions | minimum total defect | four defects | `supp(u^8)` |
|---:|---:|---:|:---|---:|
| 3 | 4 | 4 | `0,2,0,2` | 3 |
| 4 | 10 | 8 | `0,4,0,4` | 0 |
| 5 | 26 | 13 | `0,4,5,4` | 5 |
| 6 | 76 | 8 | `0,4,0,4` | 6 |
| 7 | 232 | 18 | `3,5,5,5` | 7 |
| 8 | 764 | 16 | `0,8,0,8` | 0 |
| 9 | 2,620 | 19 | `0,8,3,8` | 9 |
| 10 | 9,496 | 25 | `0,10,5,10` | 10 |
| 11 | 35,696 | 29 | `5,7,10,7` | 11 |
| 12 | 140,152 | 24 | `0,12,0,12` | 12 |
| 13 | 568,504 | 35 | `7,6,13,9` | 13 |
| 14 | 2,390,480 | 31 | `0,12,7,12` | 14 |

This is an exact enumeration by the program, not a proof about dimensions
larger than 14.  In particular, the table must not be extrapolated to a
positive asymptotic defect floor.

## Unconstrained annealing

With no mode argument, both `e` and `u` vary.  Moves conjugate or change the
cycle type of `e` while preserving `e^2=1`, or transpose two images of `u`.
The energy is total relator support plus a penalty until `u^8` moves at least
half the domain.  Reproduction commands were:

```text
/tmp/tw2 12  20000  1
/tmp/tw2 20 100000 31
/tmp/tw2 28 100000 32
/tmp/tw2 40 100000 33
```

Best recorded states:

| `n` | seed | four defects | `supp(u^8)` | total defect / `n` |
|---:|---:|:---|---:|---:|
| 12 | 1 | `0,4,0,4` | 6 | 0.667 |
| 20 | 31 | `0,8,0,8` | 12 | 0.800 |
| 28 | 32 | `0,10,0,10` | 15 | 0.714 |
| 40 | 33 | `0,14,0,14` | 21 | 0.700 |

The best states decompose into small orbits of the generated permutation
group.  Their positive mark is carried by small `u`-cycles whose lengths do
not divide eight, and each such component pays positive relator error.  This
explains the roughly linear totals in this search landscape; it is not a
general obstruction to connected or growing-block solutions.

## Structural conclusions proved from the failed ansatzes

The cyclic/dihedral states suggested collecting words under
`e u e=u^q`, `q^2=1`.  Three relators become

```text
R_rho=u^(-6-7q)e,       R_b=u^(-3-9q),       R_a=u^(-9)e.
```

Putting `P=R_b` and `Q=R_rho R_a^(-1)`, the exact exponent identity

```text
-P+qP-2qQ=8
```

gives the rigorous inequality

```text
d_H(u^8,1)<=2(d_H(R_rho,1)+d_H(R_b,1)+d_H(R_a,1)).
```

Thus no cyclic-normalizer sequence works.  Passing to equal-sized block
quotients also proves that a cyclic block lift can work only when the mark is
asymptotically invisible on the quotient and survives inside its fibres.

The natural voltage lift of the exact `C_2` quotient has both generators
flip a two-point base and use translations in an abelian fibre.  There
`u^2` is a uniform central fibre translation.  More generally, with

```text
eta=d_H(u^2e,eu^2),       delta=d_H(c^2,1),
```

the exact involution-sandwich calculation proves

```text
d_H(u^8,1)<=delta+6 eta.
```

Hence even nontrivial abelian fibre voltages cannot rescue this lift.  Any
positive construction must have both genuinely non-cyclic monodromy and
macroscopic failure of `u^2` to commute with `e`.

## Honest endpoint

No scalable positive family was found.  The exhaustive computation covers
only the single-cycle ansatz through dimension 14, and annealing is
heuristic.  The rigorous gain is the elimination of two broad structured
families and the resulting design constraint: a successful lift must hide
the mark in nonabelian fibre monodromy rather than in a cyclic block quotient
or a central abelian voltage.
