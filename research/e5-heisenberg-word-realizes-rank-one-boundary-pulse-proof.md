---
rg: 2
id: e5-heisenberg-word-realizes-rank-one-boundary-pulse-proof
kind: route
title: Compute the Heisenberg roots, block transporter, and unique top coefficient
target: e5-heisenberg-word-realizes-rank-one-boundary-pulse
requires:
  - alternating-free-ring-shears-have-strict-degree-drift
  - paired-frame-hard-characters-form-forced-two-cycle
---

The Steinberg commutator relations immediately give `(EHP2)`; all other
commutators among the four roots in `(EHP1)` vanish.  The two roots
`e_01(x),e_43(x)` commute and form

```text
diag([[1,x],[0,1]],1,[[1,0],[x,1]]).
```

Likewise `e_10(x),e_34(x)` form the opposite pair.  Multiplication gives
`(EHP3)`.  Block conjugation then sends a `2 by 1` upper-middle column `P`
to `SP`, a `1 by 2` middle-right row `Q` to `QS`, and their `2 by 2`
commutator block to `SZS`.  Inverse conjugation gives `S^-1` on both frame
coordinate pairs.

Write

```text
S^n=[[a_n,c_n],[c_n,d_n]],
S^-n=[[d_n,c_n],[c_n,a_n]].                               (EHP7)
```

The strict-degree calculation gives

```text
deg a_n=2n, deg c_n=2n-1, deg d_n=2n-2                  (n>=1),
```

with all three leading coefficients equal to one.  Pulling the cross form
`H`, represented by the `2 by 2` matrix `[[1,1],[1,0]]`, through `S^-n`
and adding `H` yields `Delta_n`.  Direct multiplication shows that its wedge
coordinates `(01,02,03,12,13,23)` have degree profile

```text
n=1:  (-1,-1,1,1,2,-1),
n>=2: (-1,4n-4,4n-3,4n-3,4n-2,-1).                      (EHP8)
```

Only the `e_13^*` coordinate reaches degree `4n-2`, and its leading
coefficient is one.  This proves `(EHP6)`.

Now let `delta:R_add -> {+1,-1}` be a relative character trivial on all
monomials of degree below `4n-2` and negative on the top monomial.  Applying
`delta` entrywise to `(EHP8)` kills every coordinate except `e_13^*`.
That alternating form has rank two, so finite Heisenberg/Clifford theory
identifies its simple sector with one Pauli factor.  In an adjoint
representation, `delta` is the quotient of the source character and its
stationary coefficient reference character; it need not be the absolute
selector character.  This is why high valuation is compatible with the
nontrivial hard packet sector.
