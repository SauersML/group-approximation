---
rg: 2
id: relative-t-heisenberg-adjoint-quantum-expansion
kind: claim
title: Relative property (T) makes irreducible Heisenberg adjoint actions uniform quantum expanders
distinct_from:
  explicit-constant-degree-quantum-expanders: that constructs abstract explicit channels; this extracts one fixed word set from a single relative-Kazhdan pair and applies it uniformly to all of its finite irreducible Heisenberg quotients.
  quantum-expander-relative-commutant-rounding: that starts from a quantum-expander channel; this manufactures the channel from group representation theory.
---

Let `N normal Gamma`, and suppose that the pair `(Gamma,N)` has a finite
symmetric relative Kazhdan set `S` with constant `kappa>0`: in every unitary
representation with no nonzero `N`-fixed vector, every unit vector is moved by
at least `kappa` by some member of `S`.

Let

```text
pi_q: Gamma -> PU(H_q)
```

be any finite-dimensional projective representation whose restriction to
`N` is irreducible. Projective phases disappear under conjugation, so
`Ad pi_q` is an honest unitary representation on `L^2(End(H_q))`. Define the
lazy random-unitary channel

```text
Psi_q(X) = (1/2)X + (1/(2|S|)) sum_(s in S) pi_q(s)Xpi_q(s)*.   (RTH1)
```

Then `Psi_q` fixes the scalar matrices and its normalized Hilbert--Schmidt
operator norm on the traceless subspace is at most

```text
lambda = 1-kappa^2/(4|S|) < 1.                                (RTH2)
```

Thus the same `|S|+1` word templates form a quantum expander in every such
irreducible quotient, with degree and gap independent of `dim H_q`.

For a finite Heisenberg quotient in its fixed nontrivial central-character
Schrodinger representation, irreducibility is the finite Stone--von Neumann
property. Consequently, any one finitely generated relative-Kazhdan Jacobi
group admitting a compatible tower of those quotients automatically supplies
the dimension-uniform expander checks required by the Clifford-tape program.

