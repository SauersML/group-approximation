---
rg: 2
id: controlled-pauli-reflection-dilation-is-a-hyperlinear-d8-absorber
kind: claim
title: Controlled-Pauli reflection dilation is a hyperlinear D8 absorber
distinct_from:
  steinberg-unitization-encodes-hecke-sums-but-is-trace-blind: that proves homogeneous elementary-root attachments retract and finite coefficient matrix groups are linear; this tests the first nonhomogeneous relation which identifies a root word with a genuine reflection.
  prime-cyclic-finite-packet-amalgams-reflect-the-source-hs-gap: that treats arbitrary prime cyclic finite-packet selectors and proves quantitative source-gap equivalence; this gives the explicit order-two Julia/controlled-Pauli formula and identifies exactly what projection an arbitrary unitary representation recovers.
  split-steinberg-conditional-swap-has-root-kernel-countermodel: that kills the Whitehead word in an exact split countermodel; this preserves a nontrivial Whitehead reflection by a load-bearing relation but proves that the new finite attachment cannot create a gap.
  unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra: that rules out group-native nonaffine joint spectra in a simple finite central block; this shows why the projection recovered from the new commutator remains unrelated to the original predicate.
---

**EXACT MIXED-RELATION CLASSIFICATION; PERFECT TRACE EXTENSION AND
BASS--SERRE SURVIVAL HOLD, BUT NO NEW HYPERLINEAR GAP IS CREATED.**

Let \(G\) be a group and let \(w\in G\) have order two.  Let

\[
 D_8=\langle u,v,z\mid
 u^2=v^2=z^2=1,\ [z,u]=[z,v]=1,\ [u,v]=z\rangle.
 \tag{CPD1}
\]

Define the mixed reflection compiler

\[
 \Gamma_w
 =G*_{\langle w\rangle=\langle z\rangle}D_8.
 \tag{CPD2}
\]

Equivalently, adjoin two involutions \(u,v\) to \(G\), require their
commutator to equal \(w\), and require \(w\) to commute with \(u,v\).

Then:

1. Both vertex groups embed in \(\Gamma_w\).  In particular \(w=z\neq1\),
   and if \(G\) is finitely presented then so is \(\Gamma_w\).

2. Every unitary representation of \(G\) extends after a fixed
   two-dimensional amplification.  If
   \(\pi:G\to\mathcal U(M)\), put

   \[
    W=\pi(w),\qquad P=\frac{1-W}{2},
    \tag{CPD3}
   \]

   and let \(X,Z\) be anticommuting Pauli involutions.  On
   \(M\overline\otimes M_2\), set

   \[
   \begin{aligned}
    U&=(1-P)\otimes I+P\otimes X,\\
    V&=(1-P)\otimes I+P\otimes Z.
   \end{aligned}
   \tag{CPD4}
   \]

   Then \(U^2=V^2=1\) and

   \[
    [U,V]=W\otimes I.
    \tag{CPD5}
   \]

   Hence (CPD4) gives a representation of \(\Gamma_w\) extending
   \(g\mapsto\pi(g)\otimes I\).  Every tracial representation of \(G\)
   therefore has a tracial extension, with its old trace unchanged.

3. Hyperlinearity is exactly preserved:

   \[
    \Gamma_w\text{ is hyperlinear}
    \quad\Longleftrightarrow\quad
    G\text{ is hyperlinear}.
    \tag{CPD6}
   \]

   The reverse implication uses hyperlinear permanence for amalgamation
   over the finite edge \(\langle w\rangle\); the forward implication uses
   the embedded copy of \(G\).

4. In every unitary representation \(\rho\) of \(\Gamma_w\), the formula

   \[
    P_\rho=\frac{1-\rho(w)}2
           =\frac{1-\rho([u,v])}2
    \tag{CPD7}
   \]

   recovers a genuine projection.  But (CPD7) recovers only the spectral
   projection of the chosen group reflection.  It does not imply that
   \(P_\rho\) equals a prescribed Hecke polynomial in other group
   generators.

Apply this to the Whitehead reflection

\[
 w=W_p^2=\operatorname{diag}(1-2p,1-2p)
 \tag{CPD8}
\]

in an elementary coefficient host.  Relation (CPD5) destroys the
root-killing retraction if the new \(D_8\) center is protected, and
Bass--Serre normal form preserves that center.  The intended coefficient
model extends by (CPD3)--(CPD5) whenever it already gives a unitary
representation of the host.

Nevertheless, (CPD6) proves that this mixed relation is an absorber, not an
amplifier.  If the elementary host is one of the finite-coefficient linear
groups from
steinberg-unitization-encodes-hecke-sums-but-is-trace-blind, then
\(\Gamma_w\) is hyperlinear.  If the host is unknown, the compiled group is
nonhyperlinear exactly when that host already is.

Trying to identify \(P_\rho\) in (CPD7) with a nonaffine BCS atom returns to
the original gate.  A finite group-element identity which makes the
reflection a function of commuting selector involutions has affine joint
support by
unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra.
A Hecke-sum identity is not a group relator.  Therefore the controlled-Pauli
dilation gives perfect completeness and exact survival, but no
finite-dimensional or hyperlinear soundness beyond the source reflection.

DERIVATION
d8-amalgam-normal-form-trace-extension-and-permanence-proof
