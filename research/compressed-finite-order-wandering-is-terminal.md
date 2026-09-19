---
rg: 2
id: compressed-finite-order-wandering-is-terminal
kind: claim
title: A positive corner cannot make an infinite-order word look finite-order in canonical microstates
distinct_from:
  compressed-reflection-kills-even-cesaro-mark: that estimates a marked Cesaro sum from one reflection compression; this observes that the compression itself already contradicts the canonical trace, without a mark, Hamiltonian, or Cesaro amplification.
  one-filtered-wandering-return-is-already-nonhyperlinearity: that assumes a positive scalar filtered-return moment; this derives a vanishing localized group-algebra norm directly from compression to any finite-order corner unitary.
  finite-graph-packet-compression-wandering-no-go: that constructs finite-quotient countermodels for finite Bass--Serre packets; this is the terminal obstruction for an arbitrary finitely presented group if the compression estimate has actually been proved.
---

Let `Gamma=<S|R>` be finitely presented, let `0!=q=q^*=q^2` have finite
support in `C[Gamma]`, and let `w in Gamma` have infinite order.  Suppose
that, after a fixed finite-packet exactification which changes the evaluated
group-algebra elements by `o(1)`, every canonical-trace matrix microstate has
a corner unitary `V_U` satisfying

```text
V_U=q_U V_U q_U,             V_U^m=q_U,               (CFW1)
||q_U w(U) q_U-V_U||_2 ->0                            (CFW2)
```

for one fixed `m>=1`.  Then `Gamma` is non-hyperlinear.

In particular the case `m=2` applies to a compressed reflection.  No
positive signal below `q`, Dirichlet inequality, marked translate, or Cesaro
sum is additionally needed.

The key point is that `(CFW2)` does not merely control one compression.  A
compression of a unitary which is close to a corner unitary has vanishing
off-corner leakage.  Consequently it controls the fixed group-algebra
element

```text
(w^m-1)q.                                               (CFW3)
```

Canonical convergence makes the norm of `(CFW3)` converge to its faithful
regular-trace norm.  That norm is nonzero: if `(w^m-1)q=0`, left
multiplication by `w^m` preserves the nonempty finite support of `q`, hence
some positive power of `w^m` is the identity, contrary to the infinite order
of `w`.

This is a circularity firewall for wandering-promotion gadgets.  Once a
dimension-independent finite-matrix compression `(CFW2)` has been proved,
the construction has already produced the non-hyperlinear witness.  A
finite-multiplicity or Hilbert-hotel return cannot be treated as an
innocent algebraic preprocessing step whose output is only later amplified
by the verifier.
