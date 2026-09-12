# Same-dimensional bounded-cycle truncation for exact BS(1,4) packets

An exact finite-dimensional pair `R S R^{-1}=S^4` decomposes into periodic
fourth-power spectral packets.  A packet of length `m>K` can be cut into
`b=ceil(m/K)<2m/K` consecutive pieces.  For a piece of length `ell` beginning
at angle `alpha`, choose

```text
eta=q/(4^ell-1),
```

where `q` is nearest to `(4^ell-1)alpha`.  Then `eta` is exactly periodic for
the map `theta |-> 4theta`, and

```text
d_T(4^j eta,4^j alpha) <= 4^j/[2(4^ell-1)].
```

The total chordal square error on one piece is at most

```text
pi^2(4^ell+1)/[15(4^ell-1)] <= pi^2/9.
```

Only one shift edge per piece is changed.  Summing over all packets and
normalizing by dimension gives

```text
||R-R_K||_2^2 <= 8/K,
||S-S_K||_2^2 <= 2pi^2/(9K).
```

The replacement is exact, same-dimensional, and has all fourth-power orbit
lengths at most `K`.  Fourier diagonalization on a cycle of length `L<=K`
then gives

```text
||(1-psi)^(-1)||_(fixed-perp)
 <= [2sin(pi/K)]^(-1) <= K/4.
```

This separates the generic long-cycle loss from the remaining arithmetic
compatibility: the former can be removed at controlled Hilbert--Schmidt cost;
the latter is concentrated in defect transport, fixed components, and
multiplicity/monodromy data.

The executable checker `experiments/bs14_bounded_cycle_shadowing_check.py`
constructs random exact scalar packets, performs the cut-and-shadow
construction, verifies `R_K S_K R_K^{-1}=S_K^4`, and checks both displayed
bounds numerically.
