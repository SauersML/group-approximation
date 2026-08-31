---
rg: 2
id: tv-antipodal-pair-forbids-coherent-negative-sign-refinement
kind: claim
title: The Taller--Vidick antipodal pair forbids every coherent negative-sign refinement
artifacts:
  - research/tv-two-row-hs-wall-and-refinement-no-go-proof.md
distinct_from:
  taller-vidick-positive-noise-collapses-central-sign: that gives the exact two-equation proof that J equals one; this proves the sharp corner Hilbert--Schmidt identity which forbids even approximate central-sign-preserving maps into later systems.
  taller-vidick-positive-noise-fixed-support-reweighting: that bounds arbitrary weighted van Kampen certificates; this certificate has two rows and gives an exact lower bound independent of proof area.
  reverse-kleene-does-not-remove-tv-completeness-loss: that closes proof-search self-reference; this closes the proposed coherent refinement and decreasing-noise diagonal.
---

**ESTABLISHED ROBUST NO-REFINEMENT THEOREM.**

Fix any positive-noise Taller--Vidick LCS and its two antipodal equations

\[
 L=J^a,\qquad L=J^{a+1}.                                \tag{TVR1}
\]

Let the old generators be evaluated by arbitrary unitaries in a finite
tracial von Neumann algebra, with \(J\) an exact central involution. Put
\(p_-=(1-J)/2\) and \(\eta=\tau(p_-)\). If \(r_+\) and \(r_-\) are the two
relator unitaries from (TVR1), then

\[
 \|p_-(r_+-1)\|_2^2+\|p_-(r_--1)\|_2^2=4\eta.           \tag{TVR2}
\]

In particular, on a full negative sector,

\[
 \max\{\|r_+-1\|_2,\|r_--1\|_2\}\geq\sqrt2.             \tag{TVR3}
\]

If the two old rows have fixed positive weights \(q_+,q_-\), their weighted
squared defect is at least

\[
 4\min(q_+,q_-)\eta.                                    \tag{TVR4}
\]

Consequently there is no coherent sequence of positive-noise systems and
word maps which sends every old relator to \(o(1)\)-defect while sending
the old central sign to a later negative central sector of nonvanishing
mass. This remains impossible if the later noise tends to zero arbitrarily
fast or is set equal to zero. The later honest strategy can have small
average loss only because the offending later rows have small sampling
weight; it cannot make a fixed old antipodal pair pointwise small.

Thus a diagonal choice such as
\(\epsilon_{n+1}\ll A_n^{-2}\), where \(A_n\) is the area of a proof of
\(J_n=1\), cannot force some \(J_n\ne1\). Here \(A_n=2\) already, and
(TVR2) is independent of \(\epsilon_{n+1}\). Algebraically, a homomorphism
of solution groups cannot preserve the marked sign either, since every
positive-noise source group has \(J_n=1\).

The precise non-nesting support is the folded pair obtained from a query
\(f\) and the two masks \(f^\uparrow\) and \(-f^\uparrow\). Both occur at
every positive noise and give the identical folded left word with opposite
right-hand sides. At zero noise at least one row is deleted. That support
deletion is not a refinement: retaining an approximate image of both old
rows would violate (TVR2).

This closes coherent refinement of the published long-code equations only.
It does not rule out a new source-dependent shared cyclic system which
removes the antipodal pair and proves a different zero-noise decoder. No
nonhyperlinear group is claimed.

DERIVATION
tv-two-row-hs-wall-and-refinement-no-go-proof
