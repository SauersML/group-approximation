# Matrix cyclotomic lifts and the growing-rank escape

This note separates two coefficient-decoder regimes that look similar but
obey different invariants.

## Exact finite carriers

Let `O subset C` have a residue map `O->F_2`.  A coefficient-faithful matrix
carrier assigns a matrix `C_g in M_k(O)` to every occurrence of a modular
coefficient `1`, with `C_g mod p=I_k`.  If decorated sums `A,B` lifted a
modular defect `ab=1!=ba` and satisfied `AB=I_k`, direct finiteness of
`M_k(L(G))` would give `BA=I_k`; reduction would give `ba=1`.  This excludes
every finite `k`, not merely scalar phases or bounded `k`.

For `O=Z[zeta_(2^m)]`, the prime `(1-zeta_(2^m))` is the relevant residue
map, so integral Pauli/cyclotomic blocks are included.  A normalized Hadamard
matrix uses `1/sqrt(2)`.  Inverting that element also inverts the prime above
two, so there is then no residue map to `F_2`.  This is a genuine dichotomy:
the denominator does not encode characteristic-two addition; it destroys the
special fiber in which that addition lives.

## Approximate growing carriers

The correct metric after reduction is normalized rank, not normalized
Hilbert--Schmidt norm.  A sequence of faithful asymptotically multiplicative
coefficient decoders is precisely an embedding of `k[G]` into a rank-metric
matrix ultraproduct, i.e. linear soficity of the `k`-algebra.  Restricting the
embedding makes `G` linear sofic over `k`.  Arzhantseva and Paunescu prove the
converse for `k=C`; they do not prove it for arbitrary coefficient fields.

Rank ultraproducts are stably finite coordinatewise.  The elementary identity

```text
rank(I-AB)=rank(I-BA)
```

follows because `B` and `A` identify the two `1`-eigenspaces.  Thus a modular
group algebra that is not directly finite cannot possess a faithful growing
rank decoder.

This locates the exact open bridge.  Turning arbitrary unitary HS microstates
into faithful `F_2[G]` decoders would establish the coefficient-sensitive
statement `hyperlinear G => F_2[G] linear sofic`, and hence direct finiteness
of `F_2[G]`.  This is stronger than merely showing that `G` is linear sofic.
It is also not the same as `hyperlinear => sofic`: on `F_q^d`, a rank-`r`
discrepancy fixes a proportion `q^(-r)` of vectors, so an `o(d)` rank defect
may still disagree on almost every vector.  No permutation approximation
follows from the naive finite-vector action.

Primary reference: G. Arzhantseva and L. Paunescu, *Linear sofic groups and
algebras*, arXiv:1212.6780, especially Theorem 1.2/Corollary 7.7 and
Proposition 2.8.  Their Question 7.9 records the coefficient-field direct
finiteness boundary.
