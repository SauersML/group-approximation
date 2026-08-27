# Exact BS packet classification and the Higman product holonomy

## Packet normal form

For unitaries `C,D` with `CDC^-1=D^2`, conjugation preserves the weighted
spectrum of `D`.  On a finite support, squaring is therefore a permutation.
Every atom is a root of unity of odd order, and each squaring orbit has equal
eigenspace multiplicity.  On an orbit of length `m`, `D` is scalar diagonal
and `C` shifts the `m` eigenspaces cyclically, with an arbitrary unitary on
the multiplicity space at the wrap.  Diagonalizing that wrap splits it into
scalar-monodromy packets.

This classification shows where multiplicity freedom lives, but it does not
automatically align repeated generator occurrences between adjacent packets.

## Exact gauge equation

For one packet `(P,D)`, gauge edge `i` by `G_i`.  The target occurrence of
generator `i` is `G_(i-1)DG_(i-1)^*`; its conjugator occurrence is
`G_iPG_i^*`.  With `H_i=G_(i-1)^*G_i`, the seam is

```text
||D-H_iPH_i^*||_2,
```

and the ordered gauge increments telescope to

```text
H_1 H_2 H_3 H_0=I.
```

This is necessary and sufficient.  Centralizer gauges and packet
multiplicities change the available matcher set, but the ordered-product
condition remains literal.

## Optimal transport kills three seams

For the odd periodic clocks `(P_q,D_q)`, choose primes along which both
spectral measures converge to Haar.  The quadratic Wasserstein distance of
the spectra tends to zero, so normal-matrix eigenvalue matching gives a
unitary `H_q` with `H_qP_qH_q^*` HS-close to `D_q`.

Gauge four successive edges by `I,H_q,H_q^2,H_q^3`.  Three occurrence seams
tend to zero.  All conjugator occurrences remain at distance tending to
`sqrt(2)` from identity.  The fourth seam is bounded by the spectral-matching
error plus

```text
||[H_q^4,P_q]||_2.
```

Thus every proposed lower bound assembled from one, two, or three packet
interfaces is false even in multiplicity one.  The full problem is the
fourfold product-holonomy constraint, not an uncertainty bound for one
doubling pair.

This does not claim a full Higman microstate: the fourth seam is precisely
the unresolved gate.  It reduces the periodic-clock sector to the concrete
order-four matcher question without hiding the missing condition.

## Long-path/Folner block transport does not remove the gate

Let `S` be one approximate matcher and place the conjugated packets
`S^k(P,D)S^-k` on `L` blocks.  The cyclic block shift matches `P` to `D` on
`L-1` blocks, so its one-step error is at most
`(epsilon^2+4/L)^(1/2)`.

Its fourth power, however, compares `S^(k+4)PS^(-(k+4))` with
`S^kPS^(-k)` on every interior block.  Therefore its squared error lies
between

```text
(1-4/L)||S^4PS^-4-P||_2^2
```

and that quantity plus `16/L`.  The product holonomy is a bulk density, not
the single cyclic wrap.  A varying moduli path has the same formula with the
product of four consecutive matcher increments at each site.

This also pinpoints why an eigenvalue-quartet argument is insufficient.
Optimal spectral matching chooses a unitary between two different
eigenbases.  Requiring its fourth power to return is a constraint on the
fourfold eigenbasis transport, not merely on grouping the paired eigenvalues
into four-cycles.
