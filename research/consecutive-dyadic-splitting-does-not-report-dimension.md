---
rg: 2
id: consecutive-dyadic-splitting-does-not-report-dimension
kind: claim
title: Consecutive dyadic splitting reports only 2-adic valuation, not growing multiplicity
distinct_from:
  constant-hs-groupification-of-residual-dyadic-splitter: that asks for an adaptive positive-density compiler whose replicas remain independent on the whole residual carrier; this rules out the simpler controller which stops at the first failed exact halving.
  adaptive-all-pairs-schur-replica-table-compiler: that asks a complete multiplication table to certify supercritical simultaneous replicas with one global error; this shows why a nested local divisibility test cannot replace that certificate.
  determinant-index-cannot-authenticate-julia-heat-overlap: that rules out bounded indices and determinant phases for the Julia selector; this computes the exact arithmetic and normalized-HS failure of a dyadic multiplicity sensor before any Julia return is attached.
---

ESTABLISHED.  Let a consecutive dyadic controller on a multiplicity space
`C^k` declare level `j+1` available only when every live level-`j` block is
the orthogonal sum of two Murray--von Neumann equivalent child blocks.  If
the identities are exact and the live block has full support, then a depth
`r` split forces

```text
2^r divides k.                                             (CDS1)
```

Consequently the first exact failure depth is at most `v_2(k)+1`.  This is
not a dimension report: there are arbitrarily large odd `k` for which the
controller fails at its first split, and for every fixed `a` there are
arbitrarily large `k` with `v_2(k)=a`.

The failure has no uniform normalized-HS gap.  Fix a depth `r`, write

```text
k=2^r q+s,                   0<=s<2^r,                    (CDS2)
```

and decompose a subspace of dimension `2^r q` into `2^r` equal coordinate
blocks.  On that subspace the full depth-`r` binary tree, including all
equivalences between sibling projections, is exact.  Extend every partial
isometry by zero on the residual projection `R` of rank `s`.  All failures
of the root coverage and recursive splitting relations are supported on
`R`; in particular

```text
||R||_(2,k)=sqrt(s/k) < sqrt(2^r/k).                      (CDS3)
```

More generally, evaluation of any fixed finite list of bounded star words
in these projections and partial isometries differs from its exact bulk
evaluation by at most `C sqrt(2^r/k)`, where `C` depends only on that fixed
word list.  This follows by telescoping each word: every changed factor is
supported on `R`, multiplication by contractions does not increase the
normalized Hilbert--Schmidt norm, and the list has fixed total length.

For the first split the obstruction is already sharp.  If `k` is odd, take
two orthogonal rank `(k-1)/2` projections, an exact partial isometry between
them, and a rank-one residual `R`.  The sibling equivalence relations are
exact and the sole coverage error is

```text
||R||_(2,k)=1/sqrt(k) -> 0.                               (CDS4)
```

Thus neither the stopping depth nor the local defect of consecutive
halving tends in the required direction as `k->infinity`.  A bounded trigger
for `dimension-reported-julia-amplitude-return` cannot choose
`t(k)->infinity` from the first failed dyadic split.  It must instead use a
sensor that sees more than `v_2(k)` and makes the unmatched residual
extensive -- for example the still-open adaptive all-pairs replica table --
or return to the Amitsur--Levitzki/constant-sound PCP route.
