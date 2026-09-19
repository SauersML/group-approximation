---
rg: 2
id: torsion-symbols-exactify-by-corners-not-infinite-symbol
kind: claim
title: Torsion Laurent symbols exactify on a large corner but the torus symbol has no automatic spectral absorber
distinct_from:
  stable-laurent-k2-has-minimal-three-symbol-packet: that identifies the algebraically minimal quotient packet; this separates the positive finite-order Hilbert--Schmidt exactification from the infinite-order gap
---

Use the stable-range notation of the three-symbol packet and let `pi` be an
exact finite-dimensional unitary representation of `St_r(R)`.  Put

```text
delta_m=2 sin(pi/m),       m=q-1>1.
```

If `P_i` is the spectral projection of `pi(c_i)` at eigenvalue `1`, for
`i=1,2`, and `P=P_1 P_2`, then `P` commutes with the whole representation,
`c_1` and `c_2` vanish exactly on `P`, and

```text
tr(1-P)
 <= (||pi(c_1)-1||_2^2+||pi(c_2)-1||_2^2)/delta_m^2.         (TSE1)
```

Thus the two torsion relations have an explicit almost-full invariant-corner
absorber.  If both defects are at most `eps`, the discarded fraction is at
most `2 eps^2/delta_m^2`.  For `q=2` these two relations are absent.

No estimate of the form (TSE1) follows for the infinite-order torus symbol
`c_0` from centrality and small Hilbert--Schmidt defect alone.  The sharp
finite-dimensional model is the discrete Heisenberg relation

```text
<u,v,z | z central, [u,v]=z>.
```

For every `n>=2`, the clock--shift representation has

```text
pi_n(z)=omega_n^(-1) 1_n,       omega_n=exp(2 pi i/n),
||pi_n(z)-1||_2=|omega_n-1| -> 0,
ker(pi_n(z)-1)=0.                                             (TSE2)
```

Even after adjoining any exact `z=1` block of dimension `s_n=o(n)`, the
`z=1` subspace has dimension only `s_n`, not `n-o(n)`.  Therefore small
padding cannot produce an almost-full exact invariant corner while the
original block is frozen.

This is a precise method firewall.  It does not assert that the Laurent
Steinberg group realizes the Heisenberg phase family, and it does not rule
out perturbing the original generators.  It proves that the infinite symbol
requires a genuinely Laurent-specific spectral or Hilbert--Schmidt stability
input; the finite-order corner argument that completely handles `c_1,c_2`
cannot handle `c_0`.

DERIVATION
central-spectrum-and-heisenberg-padding-proof
