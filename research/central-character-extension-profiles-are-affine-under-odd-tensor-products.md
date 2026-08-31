---
rg: 2
id: central-character-extension-profiles-are-affine-under-odd-tensor-products
kind: claim
title: Every ordinary-group central-character extension profile is affine
distinct_from:
  one-hot-central-character-selector-forces-weight-three-ghost: that constructs one weight-three ghost from deterministic branches of a four-outcome selector; this classifies the entire multiport extension profile and gives the minimal two-port NAND obstruction.
  central-selector-spectra-cannot-prune-a-nonlinear-predicate: that assumes the selector words form a central subgroup or uses the regular marked corner; this needs no commutation or centrality of the port words and permits arbitrary noncommuting auxiliaries.
  finite-clifford-couplings-cannot-prune-a-forbidden-atom: that induces a selector character through a finite or residually finite overgroup; this applies to every ambient group, including nonamenable and non-residually-finite groups, whenever the port values are scalar in the tested sectors.
---

**ESTABLISHED UNIVERSAL GROUP-EXTENSION NO-GO.**

Let \(\Gamma\) be any group, let \(Z\leq Z(\Gamma)\), let
\(\zeta:Z\to\mathbf T\) be a character, and fix arbitrary words
\(r_1,\ldots,r_k\in\Gamma\). Define \(\mathsf E_\zeta\subseteq
\{\pm1\}^k\) to be the set of sign patterns \(\epsilon\) for which there is
a nonzero unitary representation \(\pi_\epsilon\) satisfying

\[
 \pi_\epsilon(z)=\zeta(z)I
 \quad(z\in Z),
 \qquad
 \pi_\epsilon(r_i)=\epsilon_iI
 \quad(1\leq i\leq k).
 \tag{ACT1}
\]

Then \(\mathsf E_\zeta\) is either empty or an affine subspace of the
Boolean cube. The same statement holds if only finite-dimensional
representations are admitted.

The proof is the ternary tensor operation

\[
 (\pi_\epsilon,\pi_\eta,\pi_\theta)
 \longmapsto
 \pi_\epsilon\otimes\pi_\eta\otimes\overline{\pi_\theta}.
 \tag{ACT2}
\]

It preserves the central character because
\(\zeta^2\overline\zeta=\zeta\), and its port pattern is
\(\epsilon\eta\theta\). A nonempty subset of an elementary abelian group
closed under \(x y z^{-1}\) is an affine coset.

In particular, consider two projection reflections \(r,s\). If one
ordinary-group auxiliary gadget has marked extensions of the three
orthogonality-compatible scalar sectors

\[
 (r,s)=(+,+),\quad(-,+),\quad(+,-),
 \tag{ACT3}
\]

then the same marked sector necessarily has an extension with

\[
 (r,s)=(-,-).
 \tag{ACT4}
\]

Explicitly, tensor the \((- ,+)\) and \((+,-)\) extensions with the
conjugate of the \((+,+)\) extension. This conclusion is independent of
the number or nature of the auxiliary generators and relators. It covers
Coxeter and Clifford cells, controlled-Pauli and Halmos dilations,
property-(T) interfaces, Higman word gadgets, and Steinberg wordization as
long as the source projections are read as scalar signs of ordinary group
words in the tested sectors.

There is also an asymptotic normalized-Hilbert--Schmidt version: tensoring
three approximate extensions adds, rather than amplifies, their relator
and port defects. Hence a local gadget with vanishing-defect completeness
on all three sectors in (ACT3) automatically has a vanishing-defect
forbidden extension. It cannot have a dimension-independent decoder which
rejects (ACT4).

Applied to the perfect-qc SynchBCS source, this closes every compiler which
maps each Boolean projection to \((1-r_i)/2\) for an ordinary group word
and whose auxiliary extension is complete atom by atom. A surviving
compiler must violate at least one hypothesis: use a genuinely
non-character Hecke/corner projection, couple the whole source so that the
three local atoms do not extend separately, or use a one-sided
representation-dependent trace return. No nonhyperlinear group is
constructed.

DERIVATION
ternary-tensor-closure-and-the-forbidden-and-sector-proof
