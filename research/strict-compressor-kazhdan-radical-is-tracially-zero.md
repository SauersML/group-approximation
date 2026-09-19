---
rg: 2
id: strict-compressor-kazhdan-radical-is-tracially-zero
kind: claim
title: The strict-compressor Kazhdan projection is invisible to every trace, not only finite-dimensional representations
artifacts:
  - research/strict-compressor-trace-seam-proof.md
distinct_from:
  strict-kazhdan-compressor-forces-non-rfd: that constructs the nonzero finite-dimensional radical projection; this proves that the same projection lies in the kernel of every tracial GNS representation.
  monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable: that uses Pauli microstates to refute actor stability; this shows why the maximal-C-star projection itself can never become a regular-trace root.
  manzoor-native-haar-envelope-is-ce-after-corners: that excludes a native algebraic envelope for a known non-CE IRS trace; this rules out IRS averaging of the strict-compressor witness before Connes embeddability is even considered.
---

**ESTABLISHED TRACE-SEAM NO-GO.**

Let \(H\leq G\) have property \((T)\), let
\[
 K=tHt^{-1}<H,
\]
and let \(p\in C^*_{\max}(G)\) be the Kazhdan projection of \(H\).  Put
\[
 q=tpt^{-1},\qquad e=q-p.
\]
The strict-compressor theorem proves that \(e\) is a nonzero projection.
Nevertheless,
\[
 \boxed{\qquad
 \pi_\tau(e)=0\quad\hbox{for every tracial state }
 \tau\in T(C^*_{\max}(G)).
 \qquad}                                                  \tag{STS1}
\]
Equivalently,
\[
 0\ne e\in I_{\mathrm{tr}}(C^*_{\max}(G))
 :=\bigcap_{\tau\in T(C^*_{\max}(G))}
       \{a:\tau(a^*a)=0\}.                                \tag{STS2}
\]
Indeed traciality gives
\[
 \tau(e)=\tau(tpt^{-1})-\tau(p)=0,                        \tag{STS3}
\]
and \(e=e^*=e^2\).  The tracial null space is a two-sided ideal, so the
whole GNS representation kills \(e\).

This also kills the named nonnormality commutator.  If
\(\gamma\in H\) and
\[
                    c=[q,\gamma],
\]
then \(p\) commutes with \(\gamma\), hence
\[
                    c=[e,\gamma].                        \tag{STS4}
\]
Thus every tracial GNS representation kills \(c\) and
\[
                    \tau(c^*c)=0                         \tag{STS5}
\]
for every trace, even when the quasi-regular representation proves
\(c\ne0\).

Consequences:

1. The quasi-regular \(K\)-state detecting \(e\) is necessarily
   nontracial.  Averaging it to any conjugation-invariant law destroys the
   signal exactly.  In particular every IRS trace satisfies
   \[
                         \tau_{\mathrm{IRS}}(e)=0.
   \]
2. No unital star-homomorphism from \(C^*_{\max}(G)\) into a finite tracial
   von Neumann algebra can carry \(e\) nontrivially.  This includes every
   matrix tracial ultraproduct and every nonzero corner of a group factor.
3. The canonical reduced representation is only one instance of (STS1).
   Therefore \(e\) is a maximal-C-star/RFD and actor-stability obstruction,
   not evidence for a nonhyperlinear canonical group trace.
4. A norm-ultraproduct representation may detect \(e\), because a norm
   matrix ultraproduct need not have a faithful finite trace.  Tensoring
   such a detector with a regular-character carrier does not by itself
   produce positive normalized-HS mass: after passage to a tracial
   ultraproduct, (STS1) forces the detector to vanish.

The 2025--26 non-co-hyperlinear IRS results do not bridge this seam.
Manzoor constructs a non-Connes-embeddable IRS GNS algebra and embeds it in
an equivalence-relation algebra, while the acting free group itself is
hyperlinear.  Thus a non-CE IRS trace does not imply failure of the
canonical regular trace.  Standard coinduction and generalized wreath
constructions retain a supplied finite-algebra payload in a crossed product,
but their canonical group unitaries still generate the regular group factor,
not the IRS GNS algebra.

Accordingly, no IRS averaging, double, wreath, shared-center extension, or
finite group-factor corner can promote the particular projection \(e\).
A successful root construction must first manufacture a different positive
element which is visible to a tracial representation, and then give a
trace-preserving embedding of that representation into a canonical group
factor.  That trace-to-regular compiler remains open.
