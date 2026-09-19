---
rg: 2
id: perfect-synchbcs-forces-actor-mass-beyond-regular-orbit
kind: claim
title: The perfect SynchBCS forces actor mass beyond the two-compressor regular orbit
distinct_from:
  actor-fourier-mixing-is-the-naimark-defect-of-the-base-povm: that derives the coefficient Gram equation and one quarter-overlap bound; this sums those equations over every losing cell of the perfect source and obtains a global game-gap lower bound.
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: that identifies the binary A,B cylinder group as a residually finite regular wreath; this applies the shared-center spin version to exclude an exact no-CE SynchBCS corner map.
  property-t-actor-keeps-fd-invisible-center-in-lef-models: that constructs LEF spin models for the regular SL3 action; this uses their hyperlinearity as a terminal obstruction to any algebraic source map confined to the regular orbit.
  kt-ab-marked-return-is-the-first-mixed-cylinder: that names the first arithmetic cylinder outside the regular orbit; this proves that the full source's necessary actor mass cannot be carried by any A,B-only algebraic atlas.
artifacts:
  - research/perfect-game-loss-actor-variance-and-regular-orbit-proof.md
---

**ESTABLISHED GLOBAL MASS AND TWO-COMPRESSOR SUBCORNER FIREWALL; NO
NONHYPERLINEAR GROUP IS CLAIMED.**

Let \(G_{\mathrm{game}}\) be the finite synchronous game behind
\(\mathcal A_I\), with question distribution \(\mu\), at most \(k\) answers
per question, and

\[
 \omega^*(G_{\mathrm{game}})\leq\frac12.
 \tag{PAM1}
\]

Let \(B\rtimes_{\mathrm{alg}}\Lambda\) be an algebraic tracial crossed
product whose base is locally matricial. Suppose, conditionally, that the
game projections have an exact algebraic image

\[
 P_{x,a}=\sum_g a_{x,a,g}u_g
 \tag{PAM2}
\]

and put \(A_{x,a}=a_{x,a,1}=E_B(P_{x,a})\). Then all
\(A_{x,a}\) lie in one finite matrix block and form POVMs. Define their actor
variance by

\[
 v_{x,a}=\tau(A_{x,a}-A_{x,a}^2)
        =\sum_{g\ne1}\|a_{x,a,g}\|_2^2.
 \tag{PAM3}
\]

The full perfect-game relations force

\[
 \boxed{\qquad
 \sum_{x,a}v_{x,a}\geq\frac{1-\omega^*(G_{\mathrm{game}})}{k}
 \geq\frac1{2k}.
 \qquad}                                                    \tag{PAM4}
\]

Thus every exact algebraic crossed-product realization of the source has a
dimension-independent total nonidentity actor Fourier mass. At least one
source projection has actor-tail squared norm at least
\(1/(2kN)\), where \(N\) is the number of question-answer generators.

The local \(1/20\) root-port bound also globalizes combinatorially. Suppose
reference base projections \(Q_i\) are assigned to source generators, and
let \(\mathcal L_{1/4}\) be any graph of losing cells
\(\{i,j\}\) for which \(\tau(Q_iQ_j)=1/4\). Then

\[
 S=\left\{i:\|A_i-Q_i\|_2\geq\frac1{20}\right\}
 \tag{PAM5}
\]

is a vertex cover of \(\mathcal L_{1/4}\). In particular, for every matching
\(M\) in that graph,

\[
 \sum_i\|A_i-Q_i\|_2\geq\frac{|M|}{20}.
 \tag{PAM6}
\]

Now specialize to the shared-center Kun--Thom host. Let

\[
 H=\langle A,B\rangle=SL_3(\mathbf Z),\qquad
 O=H\Gamma\subset G/\Gamma
 \tag{PAM7}
\]

be the regular orbit of the two positive compressors. The shared-center
spin group on this orbit,

\[
 \Pi_O=E(O)\rtimes H,
 \tag{PAM8}
\]

is the regular-action LEF group from
`property-t-actor-keeps-fd-invisible-center-in-lef-models`, after
renaming \(O\) as \(H\). Hence \(\Pi_O\) is hyperlinear. There is no unital
star homomorphism

\[
 \mathcal A_I\longrightarrow
 p_-\mathbf C[\Pi_O]p_-.
 \tag{PAM9}
\]

Indeed, such a map would pull the hyperlinear canonical corner trace back to
a Connes-embeddable trace on \(\mathcal A_I\), whereas every trace on
\(\mathcal A_I\) is non-CE.

Consequently both compressors, every finite spin cylinder on their regular
orbit, and arbitrary finite actor Fourier sums in \(H\) are still
insufficient. Any surviving full-corner map must leave the subcorner in
(PAM9): it must use a base site outside \(O\), an actor coefficient outside
\(H\), or both. In the explicit presentation this means genuinely mixed
\(\Gamma\)--compressor incidence. The first named such return is

\[
 r=e_{12}(x_1)\in\Gamma,\qquad
 h=LrL^{-1}=e_{12}((x_1x_2x_3)^{-1}),
 \tag{PAM10}
\]

with \(L\in\langle A,B\rangle\), together with a finite Kazhdan stabilizer
packet.

Equations (PAM4)--(PAM9) are an exact finite-support/moment obstruction to
every A,B-only atlas. They do not contradict a mixed full-actor atlas and do
not construct one. The remaining task is to solve the Fourier Gram equations
simultaneously with the mixed return (PAM10) and the full stabilizer packet.
Cairn remains OPEN.

DERIVATION
perfect-game-loss-actor-variance-and-regular-orbit-proof
