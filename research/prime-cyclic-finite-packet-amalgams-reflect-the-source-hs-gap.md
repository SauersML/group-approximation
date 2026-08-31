---
rg: 2
id: prime-cyclic-finite-packet-amalgams-reflect-the-source-hs-gap
kind: claim
title: Prime-cyclic finite-packet amalgams reflect the source HS gap exactly
artifacts:
  - research/prime-sector-tensor-balancing-and-finite-packet-absorption-proof.md
distinct_from:
  deligne-q8-finite-edge-terminal-compiler-is-equivalent-to-source-gap: that proves the order-three quaternion instance with an explicit spin matrix and an explicit four-to-one HS estimate; this classifies every finite selector and every prime-order actor mark by tensor-balancing all central sectors.
  finite-selector-gadget-induction-barrier: that classifies exact characters inside one finite overgroup; this transfers arbitrary almost-representation sectors through a finite-edge amalgam and proves an equivalence of dimension-uniform HS collapse.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that uses unbounded Pauli rank and therefore lies outside the finite-packet hypothesis; this proves why replacing that moving rank by any fixed finite packet cannot improve the actor's metric gap.
---

Let \(p\) be prime. Let \(E\) be a finitely presented group with a
central element \(c\) of order \(p\). Let \(K\) be finite,
\(\alpha\in\operatorname{Aut}(K)\) satisfy \(\alpha^p=1\), and let
\(1\ne z\in Z(K)\) be fixed by \(\alpha\). Assume that \(z\) dies in the
coinvariant quotient

\[
 K_\alpha
 =K/\langle\!\langle\alpha(k)k^{-1}:k\in K\rangle\!\rangle.
                                                               \tag{1}
\]

Put \(B=K\rtimes_\alpha C_p\), with cyclic generator \(r\), and form

\[
 \Pi(E,K,\alpha,z)
 =
 B*_{C_p\times\langle z\rangle}
 (E\times\langle z\rangle),                              \tag{2}
\]

identifying \(r\) with \(c\) and the two copies of \(z\).

Then:

1. \(\Pi\) is finitely presented and contains \(z\) as a nontrivial
   central element.
2. If every finite-dimensional unitary representation of \(E\) kills
   \(c\), then every finite-dimensional unitary representation of
   \(\Pi\) kills \(z\).
3. Hyperlinearity is reflected exactly:
   \[
      E\text{ is hyperlinear}
      \quad\Longleftrightarrow\quad
      \Pi\text{ is hyperlinear}.                         \tag{3}
   \]
4. For fixed finite presentations containing the marked generators,
   universal normalized-HS collapse is reflected exactly:
   \[
   \operatorname{Collapse}_{HS}(E,c)
   \quad\Longleftrightarrow\quad
   \operatorname{Collapse}_{HS}(\Pi,z).                  \tag{4}
   \]

The forward implication in (4) is quantitative. There are constants
\(A,B<\infty\), depending only on the finite packet presentation and a
fixed proof of \(z=1\) in (1), such that every unitary tuple of
\(\Pi\)-presentation defect at most \(\delta\) satisfies

\[
 \|Z-I\|_2\leq A\|C-I\|_2+B\delta.                       \tag{5}
\]

For the reverse implication, one surviving nontrivial \(c=\omega^jI\)
sector generates every \(p\)-th-root sector by fixed tensor powers because
\(p\) is prime. After equalizing dimensions, these sectors match the
restriction to \(C_p\) of a nontrivial \(z\)-character block of the
regular representation of \(B\). This supplies \(\Pi\)
almost-representations in which \(z\) is a fixed nonidentity scalar.

Consequently no finite selector packet attached to a prime-order
property-(T) central mark by the normal-form amalgam (2) can strengthen
the source estimate. Exact finite-dimensional invisibility transfers, but
the complete asymptotic obstruction transfers in the opposite direction.
The moving-rank extraspecial construction escapes this theorem precisely
by having no fixed finite packet. No nonhyperlinear group is constructed
here.
