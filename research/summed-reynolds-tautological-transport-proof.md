---
rg: 2
id: summed-reynolds-tautological-transport-proof
kind: route
title: Replace the high-density Reynolds projection by the identity and extend every corner polar unitary by identity
target: summed-reynolds-carrier-transports-only-tautologically
requires:
  - summed-reynolds-cut-synchronizes-kernel-corners
  - km-triangle-local-bimodules-have-finite-nonflat-models
---

Since `q` is a projection,

```text
||q-I||_2^2=tr(I-q)=1-beta<=alpha,                      (SRT8)
```

which proves `(SRT2)`.  For a unitary `U`, the two projections `q` and
`UqU^*` have the same trace.  Applying the projection-difference identity to
their complements gives

```text
||[U,q]||_2^2
 =||UqU^*-q||_2^2
 =||(I-UqU^*)-(I-q)||_2^2
 <=2 tr(I-q)
 <=2 alpha.                                             (SRT9)
```

Thus the carrier is approximately invariant under every unitary in the
ambient matrix algebra, not merely the finite subgroup used in its Reynolds
average.

For every unitary `Y`,

```text
qYq-Y=(q-I)Yq+Y(q-I),
```

so Hilbert--Schmidt ideality and `(SRT2)` prove `(SRT4)`.  Also

```text
qY_aq-q=q(Y_a-I)q,
```

and compression is `L^2`-contractive; since each summand of `E` is at most
`E`, this proves `(SRT5)`.

The orthogonal block sum `tilde B_a=B_a+(I-q)` is unitary.  Its difference
from the identity is supported on `q`, and `(SRC4)` gives

```text
||tilde B_a-I||_2^2
 =beta ||B_a-q||_(2,q)^2
 <=4 beta |H|s.                                        (SRT10)
```

The same calculation with `B_a-B_b` proves the second inequality in
`(SRT6)`.  Setting `s=sqrt(E)` gives the asserted optimized rates.

Finally `(SRT7)` is an identity, and

```text
||Y_a-I||_2^2<=E.
```

Nothing in `(SRC1)--(SRC7)` names the separately exactified `P_13`
representation or a comparison map to it.  Therefore none of the proved
inequalities can identify `tilde B_a` with that missing coefficient.  This
is not only a logical omission: the exact regular local counterpacket permits
one `P_13` overlap identification to be multiplied by an arbitrary unitary
in its multiplicity commutant.  That operation preserves the entire
tree-side Reynolds datum and every local intertwining equation while changing
the returned chart coefficient.  It is therefore an exact finite-dimensional
countermodel to Reynolds-data-only coefficient extraction.  This proves the
stated boundary between automatic carrier transport and the open relative
coefficient comparison.
