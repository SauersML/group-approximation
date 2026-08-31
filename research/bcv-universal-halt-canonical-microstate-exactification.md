---
rg: 2
id: bcv-universal-halt-canonical-microstate-exactification
kind: claim
title: One decidable-word-problem group uniformly exactifies canonical microstates into perfect BCV HALT strategies
distinct_from:
  bcv-no-computable-perfect-halt-readable-bound: that proves the exact readable-dimension lower bound after a perfect HALT strategy is already present; this asks for a fixed group and an effective approximate-to-exact front end producing such strategies.
  bcv-every-perfect-compression-amplifies-readable-closure: that inverts Compression at zero loss and stays inside one exact strategy; this must start from a finite-tolerance canonical group microstate and reach zero loss.
  bcv-pauli-amplification-haarizes-only-the-packet: that identifies the trace and coherence data not forced by the BCV packet equations; this asks that those data be supplied uniformly by one group.
  decidable-wp-hyperlinear-computable-microstate-modulus: that computes approximate canonical microstates for any promised hyperlinear group; this is the missing transfer from those approximate witnesses to exact BCV strategies.
  finite-schur-clifford-packet-flexible-hs-exactification: that flexibly exactifies each fixed finite packet; this asks for simultaneous exactification of the packet, its source multiplicity strategy, all shared contexts, and all recursively exposed levels.
---

**OPEN.** Construct the following data.

1. A fixed finitely presented group
   \(\Gamma=\langle X\mid R\rangle\), together with a word-problem decider
   \(W\).
2. Total computable functions \(n(M),q(M)\ge1\), a computable finite packet
   of words in \(F(X)\) for each Turing machine \(M\), and any required
   central-corner prescription.
3. A total computable numerical function
   \(A(M,\ulcorner U\urcorner)\) with this property. If \(U\) is any rational
   canonical \((n(M),q(M))\)-microstate of \(\Gamma\) in the sense of
   decidable-wp-hyperlinear-computable-microstate-modulus
   and \(M\) halts, then the evaluated packet admits an exactification to an
   attained-perfect finite-dimensional ZPC strategy \(S\) for the BCV game
   \(G_M\), with

   \[
      \dim D_\infty(S)\le A(M,\ulcorner U\urcorner).       \tag{BEX1}
   \]

The output in \((\mathrm{BEX1})\) must have BCV Definition 2.27's literal
typing: Z-aligned signed-permutation observables, edge commutation, and zero
loss. An approximately multiplicative unitary tuple, an ultraproduct
strategy, or a general finite-dimensional PVM strategy is not enough.

The corner prescription must likewise be effective at the finite matrix
level. If a central involution \(J\) is used to select the \(J=-1\) sector,
the procedure must control the dimension of the selected sector and
exactify all relations there. Merely observing that the limiting canonical
trace has \(\tau_\Gamma(J)=0\) does not produce exact finite-matrix spectral
or game relations.

This interface is deliberately only as strong as the diagonal needs:
\(A\) must be total, but the perfect strategy need only be guaranteed on
halting inputs. A stronger total constructor returning the strategy itself
would imply it.

## Attempts

### Fixed-dimension quantifier elimination is circular

For a fixed game \(G_M\) and a fixed dimension \(d\), the perfect ZPC
conditions are a finite real semialgebraic problem; with literal
signed-permutation typing they are even a finite combinatorial search after
the measurement labels are fixed. Hence one can decide whether a
\(d\)-dimensional perfect strategy exists. If none exists, compactness gives
a positive minimum loss, and real quantifier elimination computes a positive
rational lower bound

\[
 \eta(M,d)>0.                                             \tag{BEX2}
\]

This is only a **dimensionwise** gap. The canonical microstate search returns
a dimension \(d(M,q)\) which itself depends on the requested tolerance
\(2^{-q}\). Tightening the tolerance changes the semialgebraic problem whose
gap is relevant. There is no reason that a search will find \(q\) with

\[
 \text{decoded defect at }2^{-q}<\eta(M,d(M,q)),          \tag{BEX3}
\]

and indeed, whenever no exact strategy exists in dimension \(d(M,q)\), the
existence of the decoded approximate strategy forces the reverse inequality.
The gaps may shrink faster than the chosen tolerances while the dimensions
escape. This is the ordinary nonclosure mechanism for finite-dimensional
correlations. Quantifier elimination therefore gives no total stopping rule
and no computable bound on the first dimension carrying an exact strategy.

### Finite-packet HS stability stops at the source tail

A dimension-independent flexible HS-stability theorem for the **whole**
BCV presentation, with a computable tolerance and computable dimension
padding, would establish \((\mathrm{BEX1})\). Available stability results do
not do so:

- Gowers--Hatami exactifies an all-pairs approximate representation of each
  finite Pauli group, and
  finite-schur-clifford-packet-flexible-hs-exactification converts one fixed
  packet presentation to that setting.
- Finite-dimensional \(C^*\)-algebra stability likewise corrects the packet
  matrix units.
- Both results stop at the arbitrary multiplicity/source algebra. They do
  not correct its game relations, synchronize independently corrected
  shared contexts, or make its generators signed permutations in one common
  Z-aligned basis.
- The recursive packet parameters and the number of exposed source levels
  grow with the unknown halting time. Fixed-level Gowers--Hatami uniqueness
  does not choose compatible nested multiplicity reservoirs, as recorded by
  gowers-hatami-uniqueness-does-not-lock-nested-pauli-reservoirs.

Thus Pauli stability is a local ingredient, not the missing uniform
exactification theorem.

The route bcv-effective-microstate-search-nonhyperlinear-route proves that
any data satisfying this claim make the displayed \(\Gamma\)
non-hyperlinear. The current BCV exact wrapper inverses do not establish the
claim: they begin with an already perfect ZPC strategy and decode it
backward. No quantitative rounding modulus from canonical group microstates
to that exact starting object is presently known.
