---
rg: 2
id: odd-principal-kernel-is-one-root-normal-closure
kind: claim
title: Every odd principal Iwahori kernel is the normal closure of one root power
distinct_from:
  one-unipotent-quotients-are-bounded-congruence: that gives a uniformly bounded error from the expected congruence quotient using the finite congruence kernel; this exact normal-generation theorem identifies the principal kernel itself.
  iwahori-mod-p-quotient-is-psl2: that treats odd prime fields through a Behr--Mennicke presentation; this holds for every odd composite or prime level.
---

**ESTABLISHED LITERATURE INPUT WITH PROJECTIVE CHECK.** Put

\[
 \widetilde\Gamma=\operatorname{SL}_2(\mathbb Z[1/2]),\qquad
 \Gamma=\widetilde\Gamma/\{+\!I,-I\},
\]

and let

\[
 t=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
\]

For every odd integer \(m>1\), Mennicke's normal-generation theorem gives

\[
 \ker\!\left(
 \widetilde\Gamma\longrightarrow
 \operatorname{SL}_2(\mathbb Z/m\mathbb Z)\right)
 =
 \langle\!\langle t^m\rangle\!\rangle_{\widetilde\Gamma}. \tag{MNG1}
\]

Consequently, for projective reduction

\[
 q_m:\Gamma\longrightarrow
 G_m=\operatorname{SL}_2(\mathbb Z/m\mathbb Z)/\{+\!I,-I\},
\]

one has the exact identity

\[
 \ker q_m=\langle\!\langle t^m\rangle\!\rangle_\Gamma.   \tag{MNG2}
\]

For the projective step, every class in \(\ker q_m\) has a representative
which is \(I\) modulo \(m\): if a representative is \(-I\) modulo \(m\),
multiply it by the central matrix \(-I\). The restriction of the central
projection to the principal subgroup in (MNG1) is injective because
\(m\) is odd and \(-I\not\equiv I\pmod m\). It is therefore an
isomorphism onto \(\ker q_m\), and normal closure commutes with the central
projection.

**Source.** J. Mennicke, *On Ihara's modular group*, Invent. Math. 4
(1967), 202--228. The precise form used here is also quoted immediately
before Corollary 2.2 of C.-F. Nyberg-Brodda, *The abelianization of
SL2(Z[1/m])*, arXiv:2401.08146, version dated 24 August 2026:
for \(\gcd(r,p)=1\), the level-\(r\) principal congruence subgroup of
\(\operatorname{SL}_2(\mathbb Z[1/p])\) is the normal closure of one
elementary unipotent \(r\)-th power. Take \(p=2\) and \(r=m\).
The opposite-root convention in the quoted statement is immaterial,
because the Weyl element conjugates the two elementary root groups.

This is an exact abstract-group identity. It does not provide a
quantitative stability modulus for approximate matrix tuples.

DERIVATION
mennicke-normal-generation-projective-check
