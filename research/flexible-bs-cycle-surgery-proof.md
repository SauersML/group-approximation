---
rg: 2
id: flexible-bs-cycle-surgery-proof
kind: route
title: Cut long fourth-power cycles and round short monodromies
target: flexible-bs-cycle-surgery-absorbs-exact-coboundaries
requires: []
---

Decompose the spectrum of `V` into fourth-power cycles and identify the
equal-dimensional spectral blocks along each cycle using `H`.  In these
coordinates `(FCS1)` says that consecutive block values of `c` differ, in
quadratic mean, by `e-1`.

For a cycle longer than `2K`, partition it into consecutive segments with
lengths between `K` and `2K`.  On each segment replace `c` by the transport
of its first block value.  Cauchy--Schwarz along paths of length at most
`2K` gives global error at most `2K delta`.

Close every segment into a new exact fourth-power cycle.  If its first
eigenangle is `theta`, choose the nearest solution `theta~` of

```text
(4^ell-1)theta~=0 mod 1.
```

Then the error at its `j`-th point is at most
`C 4^(j-ell)`.  The squared error summed over the segment is bounded by a
universal constant, so all new `V` blocks cost `O(K^(-1/2))` globally.
Keep the old transports inside each segment and change only its closing
transport.  Boundary blocks occupy at most `1/K` of the dimension, giving
the same `O(K^(-1/2))` cost for `H`.  Choose each closing transport to
intertwine the constant transported value of `c`; the resulting `c_0`
commutes with the new exact core.

On an original cycle of length at most `2K`, transport to one block.  The
accumulated equation says that its initial `c` value almost commutes with
the return monodromy, with aggregate error `O(K delta)`.  Normalized-HS
stability of a commuting pair of unitaries perturbs the value and monodromy
to a commuting pair with a universal modulus tending to zero.  Change only
the closing transport and propagate the rounded value around the cycle.
For heterogeneous cycles, first discard the blocks whose accumulated error
exceeds a threshold and apply the same modulus on the rest; Chebyshev makes
the discarded trace tend to zero.  This avoids assuming concavity of the
commuting-rounding modulus.

Combining long and short cycles gives `(FCS3)` plus the stated modulus.
Take, for example, any `K(delta)->infinity` with `K(delta)delta->0`.

