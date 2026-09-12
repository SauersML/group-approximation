---
rg: 2
id: mennicke-normal-generation-projective-check
kind: route
title: Apply Mennicke at p=2 and pass through the single global sign
target: odd-principal-kernel-is-one-root-normal-closure
requires:
  - iwahori-square-free-bs14-presentation
---

Let

\[
 \pi:\widetilde\Gamma=\operatorname{SL}_2(\mathbb Z[1/2])
 \longrightarrow
 \Gamma=\operatorname{PSL}_2(\mathbb Z[1/2])
\]

be the central quotient. Mennicke's theorem says that, whenever
\(\gcd(m,2)=1\), the principal level-\(m\) subgroup is the normal closure
of an elementary root power:

\[
 \widetilde K_m
 =\ker\bigl(\widetilde\Gamma\to
             \operatorname{SL}_2(\mathbb Z/m\mathbb Z)\bigr)
 =\langle\!\langle e_{21}(1)^m\rangle\!\rangle_
   {\widetilde\Gamma}.                                  \tag{MNP1}
\]

The Weyl matrix belongs to \(\widetilde\Gamma\) and conjugates lower and
upper elementary matrices, up to a harmless sign in the root parameter.
Thus the last normal closure in (MNP1) is also

\[
 \langle\!\langle e_{12}(1)^m\rangle\!\rangle_
 {\widetilde\Gamma}
 =\langle\!\langle t^m\rangle\!\rangle_
 {\widetilde\Gamma}.                                    \tag{MNP2}
\]

We now check that the projective kernel introduces no extra factor. If
\(g\in\widetilde\Gamma\) represents a class in \(\ker q_m\), then

\[
 g\equiv I\pmod m\quad\hbox{or}\quad g\equiv -I\pmod m.
\]

In the second case \(-g\in\widetilde K_m\) and
\(\pi(-g)=\pi(g)\), so \(\pi(\widetilde K_m)=\ker q_m\). On the other
hand,

\[
 \widetilde K_m\cap\ker\pi
 =\widetilde K_m\cap\{I,-I\}
 =\{I\},                                                \tag{MNP3}
\]

because \(m>1\) is odd. Therefore
\(\pi:\widetilde K_m\to\ker q_m\) is an isomorphism.

For a surjective homomorphism, the image of the normal closure of a set is
the normal closure of its image. Applying this to (MNP2) gives

\[
 \ker q_m
 =\pi(\widetilde K_m)
 =\langle\!\langle\pi(t)^m\rangle\!\rangle_\Gamma,
\]

which is (MNG2).

The source statement is Mennicke, *Inventiones Mathematicae* 4 (1967),
202--228. A current source-level restatement appears at
https://arxiv.org/html/2401.08146 immediately before Corollary 2.2.
