---
rg: 2
id: flexible-bs-cycle-surgery-proof
kind: route
title: Cut long fourth-power cycles and round short monodromies
target: flexible-bs-cycle-surgery-absorbs-exact-coboundaries
requires: []
---

Decompose the spectrum of `V` into fourth-power cycles.  For one orbit write

```text
H_O=E_0 (+) ... (+) E_(m-1),       dim(E_j)=k,
T_j:E_j->E_(j+1),                  c_j=c|E_j,
d_j=||c_(j+1)T_j-T_jc_j||_F,                         (FCP1)
```

with cyclic indices.  Equal eigenvalues from repeated scalar packets are
included in the same multiplicity space `E_j`; thus the `c_j` are arbitrary
`k by k` unitaries and `(FCP1)` already includes all matrix multiplicities
and return monodromy.  Orthogonality of the edge blocks gives

```text
delta^2=d^(-1) sum_(O,j) d_j^2.                       (FCP2)
```

For a cycle longer than `2K`, partition it into consecutive segments with
lengths between `K` and `2K`.  On each segment replace `c` by the transport
of its first block value along the retained `T_j`.  For a segment of length
`ell`, telescoping and Cauchy--Schwarz give

```text
sum_(r<ell)||c_r-c_r^0||_F^2
 <= ell^2 sum_(j<ell-1)d_j^2.                         (FCP3)
```

Hence the global normalized-HS gauge error is at most `2K delta`.

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
the same `O(K^(-1/2))` cost for `H`.  If `P:E_0->E_(ell-1)` is the retained
path transport, use `P^(-1)` as the closing transport.  It intertwines
`Pc_0P^(-1)` with `c_0`, so the transported gauge commutes with the new
exact core.  This choice also makes the segment return monodromy one; the
old arbitrary matrix return is paid only on the changed boundary block.

On an original cycle of length `m<=2K`, gauge all but the return edge to the
identity and write `M` for the resulting return monodromy.  Transporting
`c_0` around the cycle gives a constant gauge at cost at most `m delta_O`,
where

```text
delta_O^2=(mk)^(-1)sum_j d_j^2.
```

The final telescoping sum gives

```text
eta_O:=k^(-1/2)||[M,c_0]||_F <= m delta_O.             (FCP4)
```

Glebsky's normalized-HS commuting-unitary theorem supplies commuting
unitaries `M_0,c_0^0` within `30 eta_O^(1/9)` of `M,c_0`.  Replace only the
return edge by `M_0` and propagate `c_0^0` around the packet.  The BS
relation stays exact and the new gauge commutes with the entire packet.

This packetwise use is uniform over heterogeneous orbit labels.  Indeed, if
`w_O=mk/d`, concavity gives

```text
sum_O w_O eta_O^(2/9)
 <= (sum_O w_O eta_O^2)^(1/9)
 <= (2K delta)^(2/9).                                 (FCP5)
```

Thus the aggregate short-packet contribution is at most
`30(2K delta)^(1/9)` (up to one harmless absolute factor for perturbing both
unitaries).  No packetwise threshold or unrecorded concavity assumption is
needed.

Combining long and short cycles gives, for an absolute `C`,

```text
||V-V~||_2+||H-H~||_2+||c-c_0||_2
 <= C(K delta+K^(-1/2))+C(2K delta)^(1/9).             (FCP6)
```

Take, for example, `K=floor(delta^(-1/2))`; then every term tends to zero.
This proves `(FCS2)` and the long-cycle estimate `(FCS3)` with arbitrary
matrix multiplicities and arbitrary return monodromy.

Primary source for the only imported step: Lev Glebsky, *Almost commuting
matrices with respect to normalized Hilbert--Schmidt norm*, Theorem 1,
arXiv:1002.3082, gives the constant `30` and exponent `1/9` for two
unitaries.
