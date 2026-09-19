---
rg: 2
id: same-center-prefix-whitehead-swap-proof
kind: route
title: Conjugate the three q-factorizations by adjacent partial Whitehead words
target: same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
requires:
  - commuting-double-commutator-has-direct-mark-overlap
---

Prefix cancellation gives

```text
a_mb_m=q,                       b_ma_m=e_m,
c_md_m=e_(m+1),                 d_mc_m=e_m,
a_md_m=a_(m+1),                 c_mb_m=b_(m+1).        (SCWP1)
```

The roots `z` and `C` have disjoint rectangles, so they commute.  The direct
marked-root overlap estimate, followed by Weyl equality of the two
same-coefficient root traces, gives `(SCW1)`.

For each `m`, the Steinberg commutator rule and `(SCWP1)` give

```text
[x_(4,k_m)(a_m),x_(k_m,2)(b_m)]=x_42(q)=C.
```

Roots belonging to different pairs have neither composable index pattern,
and roots with a common initial or terminal index commute.  Thus all cross
commutators vanish.  Every arm also commutes with `z` and `C`, so `F`
reduces the packet.  On `F`, the common center acts as `-1`.  The elementary
extraspecial representation calculation now gives the three-qubit Pauli
factor in `(SCW2)`.

Fix `m`, abbreviate `o=k_m`, `n=k_(m+1)`, `a=a_m`, `b=b_m`, `c=c_m`, and
`d=d_m`.  Conjugate `x_(4,o)(a)` successively by the three factors of
`W_m`.  Only ordinary non-opposite Steinberg commutators occur.  The two
extra root terms have coefficients `ad=a_(m+1)` and
`adc=a e_m=a`; the latter cancels the original root in characteristic two.
Hence

```text
W_m x_(4,o)(a_m) W_m^(-1)=x_(4,n)(a_(m+1)).           (SCWP2)
```

The same calculation on the terminal arm uses `cb=b_(m+1)` and
`dcb=e_mb_m=b_m`, and gives

```text
W_m x_(o,2)(b_m) W_m^(-1)=x_(n,2)(b_(m+1)).           (SCWP3)
```

Reversing `(SCWP2)--(SCWP3)` gives the swap in the other direction; the
third pair is distant from both root positions in `(SCW3)` and is fixed.
The indices in `(SCW3)` are disjoint from the endpoints of `z` and `C`, so
`W_m` commutes with both and preserves `F`.

On the irreducible three-qubit Pauli factor, the automorphism just computed
is implemented by the canonical adjacent tensor-factor swap.  Two
implementers of the same full matrix-algebra automorphism differ by a
unitary in its commutant, proving `(SCW4)`.  A two-qubit swap has a
three-dimensional positive symmetric space and a one-dimensional negative
antisymmetric space.  Tensoring with the untouched qubit gives negative
dimension `2` out of `8`; this is the transport-label calculation recorded
in the claim.

Finally `W_m` commutes with both spectral involutions defining `F`, so its
compression to `F` is a unitary.  Hence `S_m^*S_m=S_mS_m^*=F`, and inserting
this twice gives `(SCW5)`.  Removing the fixed adjacent swaps from `(SCW4)`
leaves `V_1^*V_2` in the full Pauli commutant.  This is a statement about the
two one-quarter transport labels; it does not attach either reservoir factor
to the separately required one-eighth controlled selector.
