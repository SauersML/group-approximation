---
rg: 2
id: bcv-universal-halt-canonical-microstate-exactification
kind: claim
title: One decidable-word-problem group uniformly exactifies canonical microstates into perfect BCV HALT strategies
distinct_from:
  bcv-no-computable-perfect-halt-readable-bound: that proves the exact readable-dimension lower bound after a perfect HALT strategy is already present; this asks for a fixed group and an effective approximate-to-exact front end producing such strategies.
  bcv-every-perfect-compression-amplifies-readable-closure: that inverts Compression at zero loss and stays inside one exact strategy; this must start from a finite-tolerance canonical group microstate and reach zero loss.
  bcv-pauli-amplification-haarizes-only-the-packet: that identifies the trace and coherence data not forced by the BCV packet equations; this asks that those data be supplied uniformly by one group.
  decidable-word-problem-hyperlinear-has-computable-canonical-microstate-modulus: that computes approximate canonical microstates for any promised hyperlinear group; this is the missing transfer from those approximate witnesses to exact BCV strategies.
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
   \`decidable-word-problem-hyperlinear-has-computable-canonical-microstate-modulus\`
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

The route
\`bcv-effective-microstate-search-nonhyperlinear-route\` proves that any such
data make the displayed \(\Gamma\) non-hyperlinear. The current BCV exact
wrapper inverses do not establish this claim: they begin with an already
perfect ZPC strategy and decode it backward. No quantitative rounding
modulus from canonical group microstates to that exact starting object is
presently known.
