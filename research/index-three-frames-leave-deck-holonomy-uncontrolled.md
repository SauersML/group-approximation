---
rg: 2
id: index-three-frames-leave-deck-holonomy-uncontrolled
kind: claim
title: Index-three Frobenius frames leave finite-quotient deck holonomy uncontrolled
artifacts:
  - research/bass-serre-tree-localizes-the-missing-normal-rows.md
distinct_from:
  index-three-qsystem-rounding-is-relative-repair: that proves joint invariant-flat rounding is equivalent to relative repair; this identifies the exact global deck-holonomy datum which the unrounded three-sheet frames do not see.
  exact-core-domain-does-not-descend-to-normal-quotient: that gives the vacuum-versus-translated-row obstruction in a general Stinespring formulation; this places the obstruction in the Bass--Serre tree and shows why fixed index at both modular vertices does not remove it.
  optimized-core-full-pd-energy-is-intrinsic-selector: that defines the section-free finite-quotient target; this proves local index-three coefficient data live upstream of that target until all deck holonomies vanish.
---

Let
\[
 A=V_+*_{B}V_-,\qquad V_\pm\simeq PSL_2(\mathbb Z),\qquad
 [V_\pm:B]=3,                                            \tag{IDH1}
\]
with the opposite Iwahori edge identification, and put
\[
 \Lambda_N=\langle\!\langle t^N\rangle\!\rangle_A,\qquad
 G_N=A/\Lambda_N.                                        \tag{IDH2}
\]
Let \(\beta:B\to U(d)\) satisfy \(\beta(t)^N=1\), and consider
\[
 \rho=\operatorname{Ind}_B^A\beta,\qquad
 J:\mathbb C^d\to\mathcal H_\rho                         \tag{IDH3}
\]
on the identity-coset fiber.

For either vertex \(V_\pm\), the three cosets in \(V_\pm/B\) span a
\(3d\)-dimensional invariant subspace
\[
 \mathcal K_\pm=
 \overline{\operatorname{span}}\{\rho(v)J\mathbb C^d:v\in V_\pm\}
 \simeq\operatorname{Ind}_B^{V_\pm}\beta.                \tag{IDH4}
\]
Hence every local index-three Frobenius/Q-system identity is exact on
\(\mathcal K_\pm\): the three coordinate projections, the fixed Schreier
cocycles, and the identity-fiber \(B\)-intertwining contain no moving
level or section loss.

Nevertheless \(\rho\) does not factor through \(G_N\). One has
\[
 (\rho(t)^N-1)J=0,                                       \tag{IDH5}
\]
but the first extender-translated normal row is maximally bad:
\[
 \frac1{\sqrt d}
 \|(\rho(xt^Nx^{-1})-1)J\|_{\mathrm F}=\sqrt2.            \tag{IDH6}
\]
Indeed, the two terms in (IDH6) lie on distinct \(B\)-coset fibers because
\[
 xt^Nx^{-1}\notin B.                                     \tag{IDH7}
\]
In the standard matrix model, \(B\) is upper triangular and the word in
(IDH7) is the nontrivial lower unipotent with entry \(-N\).

The general descent criterion is
\[
 (\rho(\lambda)-1)\rho(w)J=0
 \quad\text{for every }\lambda\in\Lambda_N,\ w\in A.      \tag{IDH8}
\]
These are precisely the deck-holonomy rows for the finite quotient of the
Bass--Serre tree by \(\Lambda_N\). The three-sheet systems inspect the two
vertex stars of one edge. They do not inspect the return maps around the
cycles created by the quotient, and (IDH6) is already the first missed
return.

This remains the direction check after optimizing the exact core.
Changing \(\beta\) changes the fiber transports, and can absorb the cyclic
and endpoint-conjugation gauges, but the condition
\(\beta(t)^N=1\) still controls only the stabilizer row (IDH5).
It does not imply (IDH8). Therefore finite-index Frobenius induction can
produce uniformly controlled local coefficient data, or an upstream ucp
window on the infinite amalgam, without producing a positive-definite
table on the finite group \(G_N\).

A joint invariant flat projection over one common optimized fiber would
remove the obstruction: its compression is an exact representation of
\(A\) extending \(\beta\), and \(\beta(t)^N=1\) then kills the whole normal
closure. This is exactly why
index-three-qsystem-rounding-is-relative-repair makes joint flat rounding
quantitatively equivalent to the original problem. Without that rounding,
the fixed index does not prove (OPD11).

Thus the passage from the two index-three modular stars to the finite
one-power quotient has one exact missing datum: global deck-holonomy
trivialization. No uniform OPD bound or counterexample to the root is
proved here; the root remains open.

DERIVATION
bass-serre-tree-localizes-the-missing-normal-rows
