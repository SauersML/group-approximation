# Operator scaling as the finite-multiplicity selection backend

Date: 2026-08-19

## Why this is relevant

The atlas Wedderburn route has reached a finite-coordinate selection problem:
a fixed universal block support or fixed cost matrix cannot separate the exact
factor model, so the obstructing directions have to be selected from the
finite microstate itself.  A natural object is the spectral low-energy matrix
space of an intertwiner Laplacian

```text
E(T)=sum_s ||rho(s)T-T sigma(s)||_2^2.
```

A linear-size shrunk subspace of that matrix space is a quantitative obstruction
to a low-energy unitary by `spectral-low-energy-shrunk-space-obstruction`.
This makes noncommutative rank / operator scaling an algorithmic backend for the
missing finite-multiplicity step.

## Primary sources

- Garg--Gurvits--Oliveira--Wigderson, **Operator scaling: theory and
  applications**, arXiv:1511.03730.  This gives a deterministic polynomial-time
  operator-scaling algorithm for noncommutative rank and quantitative capacity
  control.
- Franks--Soma--Goemans, **Shrunk subspaces via operator Sinkhorn iteration**,
  arXiv:2207.08311.  This specifically upgrades Sinkhorn-style scaling from a
  rank test to extraction of the smallest shrunk subspace, and proves that a
  sufficiently accurate approximate shrunk subspace can be rounded to the exact
  one over the complex field.

The project does not need these papers for the elementary analytic inequality
already proved in Cairn.  Their relevance is computational and structural:
they say that once a finite basis for the selected low-energy matrix space is
available, the dual obstruction is not an unspecified existential object.
There are algorithms designed to find precisely the shrunk subspace we need.

## Proposed atlas compiler

For each finite atlas microstate:

1. exactify the fixed finite chart packet;
2. form the positive intertwiner Laplacian on the coefficient/multiplicity
   matrix space;
3. choose a threshold `a` above the total defect scale and take the spectral
   low-energy space `K_a`;
4. run operator scaling / shrunk-subspace extraction on a rational or certified
   approximation of `K_a`;
5. if a subspace `X` has

   ```text
   dim X - dim K_a(X) >= gamma d,
   ```

   commit `X` as the finite certificate.  The generic Cairn theorem then gives
   a normalized-HS energy floor `a gamma`.

The key distinction from the old Hall-support search is that `K_a` may retain
only selected singular directions inside a Wedderburn block.  Thus the method
can exploit finite rank/spectral information while remaining proof-carrying.

## Falsification criterion

If every low-energy space produced by the atlas packet has full
noncommutative rank (or only `o(d)` shrinkage), then this lane cannot yield a
constant normalized-HS obstruction.  That negative outcome is useful too: it
would rule out the entire operator-scaling formulation rather than one guessed
support graph.