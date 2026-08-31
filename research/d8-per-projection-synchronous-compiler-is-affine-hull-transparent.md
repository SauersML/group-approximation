---
rg: 2
id: d8-per-projection-synchronous-compiler-is-affine-hull-transparent
kind: claim
title: A D8 cell at every synchronous projection is transparent to the affine-hull solution group
distinct_from:
  controlled-pauli-reflection-dilation-is-a-hyperlinear-d8-absorber: that classifies one reflection cell; this iterates the cells over an entire synchronous context and computes the exact one-hot and arbitrary-predicate residue.
  finite-selector-gadget-induction-barrier: that uses induction to recreate central selector characters for an arbitrary finite overgroup; this gives an explicit extension of every representation through the proposed D8 graph and an iff theorem for hyperlinearity.
  unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra: that rules out nonlinear group spectra after selecting one simple central block; this shows that leaving the D8 blocks separate does not select anything at all.
  fd-invisible-coequalizers-have-only-affine-tv-packets: that computes the Taller--Vidick Fourier residue under automorphic coequalizers; this proves the same affine-hull boundary for arbitrary synchronous PVM and pair-predicate contexts.
---

**EXACT FULL-CONTEXT FIREWALL; THE D8 COMPILER ADDS PERFECT
DILATIONS BUT NO PREDICATE SOUNDNESS.**

Let \(R\subseteq\{\pm1\}^k\) be a nonempty Boolean context support.  Let
\(L_R\) be the set of all parity equations

\[
 \prod_{i\in S}w_i=J^b
 \tag{DPC1}
\]

which hold on every point of \(R\), where \(J\) denotes the scalar
\(-1\).  The commuting-involution group defined by \(L_R\) has joint
character set exactly

\[
 \operatorname{Aff}_{\mathbf F_2}(R),
 \tag{DPC2}
\]

the affine hull of \(R\).  Thus group products encode every affine
consequence and nothing beyond it.

For an \(n\)-outcome PVM, write \(w_a=1-2P_a\).  Orthogonality and
partition imply

\[
 [w_a,w_b]=1,\qquad \prod_{a=1}^n w_a=J.
 \tag{DPC3}
\]

Conversely, (DPC3) says only that an odd number of the scalar eigenvalues
are \(-1\).  The affine hull of the one-hot support is

\[
 \left\{x\in\mathbf F_2^n:\sum_a x_a=1\right\}.
 \tag{DPC4}
\]

For \(n\geq3\), it contains the odd high-weight sectors excluded by a PVM.
No additional equation made solely from commuting products can remove
them.

Now let \(G_{\rm aff}\) be the ordinary solution group obtained from all
context commutations and all parity equations valid on the supports of a
finite synchronous game.  Choose any finite list of nontrivial involutive
words

\[
 r_1,\ldots,r_m\in G_{\rm aff}.
 \tag{DPC5}
\]

Attach a \(D_8\) controlled-Pauli cell to every word:

\[
 \Gamma_{\rm D8}
 =G_{\rm aff}
   *_{\langle r_1\rangle=\langle z_1\rangle}D_8^{(1)}
   *\cdots*
   _{\langle r_m\rangle=\langle z_m\rangle}D_8^{(m)}.
 \tag{DPC6}
\]

Then:

1. \(G_{\rm aff}\) embeds in \(\Gamma_{\rm D8}\), and finite presentation is
   preserved.

2. Every unitary representation of \(G_{\rm aff}\) extends, after tensoring
   one Pauli qubit per cell, to a unitary representation of
   \(\Gamma_{\rm D8}\).  Hence restriction from the D8 compiler is
   surjective up to a fixed finite amplification.

3. In particular, every finite-dimensional forbidden affine-hull sector
   which exists for \(G_{\rm aff}\) survives in the D8 compiler.  The
   D8 actors impose no extra spectral support condition.

4. Hyperlinearity is exactly unchanged:

   \[
    \Gamma_{\rm D8}\text{ is hyperlinear}
    \quad\Longleftrightarrow\quad
    G_{\rm aff}\text{ is hyperlinear}.
    \tag{DPC7}
   \]

Thus putting a Julia/controlled-Pauli edge at every game projection
collapses exactly to the ordinary affine-hull solution group for both
representation-theoretic soundness and hyperlinearity.

There are only two ways to leave this theorem.  Coupling the cells inside a
single finite selected central block returns to
unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra:
the unique block has flat affine joint spectra.  Leaving the predicate
projections as genuine Hecke sums avoids that theorem, but equality of
those sums across contexts is not a group relator and the Steinberg
root-kernel gate remains.

Therefore separate D8 edge actors cannot compile a perfect non-CE
synchronous game to a group.  They give exact perfect-completeness
dilations of whatever affine representation is already present, including
the unwanted sectors.

DERIVATION
iterated-controlled-pauli-extension-and-onehot-affine-hull-proof
