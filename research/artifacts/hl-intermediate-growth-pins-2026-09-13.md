# Finitely presented intermediate growth: cover, automorphism and gap pins (2026-09-13)

Lane hl-intermediate-growth. Sources fetched on MSI under
`/scratch.global/sauer354/hl-intermediate-growth/src/` (the Grigorchuk survey TeX from the earlier
lane lives in `/scratch.global/sauer354/solve-fp-intermediate-growth/src/1111.0512/`).

## Benli–Grigorchuk–de la Harpe, arXiv:1206.2072, TeX `BGHS+3may13.tex`

- l.386–392: "\begin{thm}[\cite{GrHa--01}] ... Any finitely presented cover of the group
  $\mathfrak G$ is large. \end{thm}"
- l.394–396: "Recall that a group is \textbf{large} if it contains a subgroup of finite index that
  has non-abelian free quotients. Note that large groups have non-abelian free subgroups."
- Theorem 1.7 (l.407–413): "For each $n \ge 0$, the group $\mathfrak G_n$ has a normal subgroup
  $H_n$ of index $2^{2^{n+1}+2}$ that is isomorphic to the direct product of $2^n$ free groups of
  rank $3$."
- Theorem 1.8 (Erschler, l.430ff): "Any finitely presented cover of the Basilica group
  $\mathfrak B$ has non-abelian free subgroups."
- Theorem 1.9 (l.486ff): "Let $G$ be an infinite finitely generated self-similar group. Assume
  that $G$ is contracting faithful self-replicating. Let $G_0$ denote a standard contracting cover
  of $G$ ... If $G_0$ has non-abelian free subgroups, then so does any finitely presented cover of
  $G$. If $G_0$ is large, any finitely presented cover of $G$ is large."
- l.511–512: "Let $\Omega_+$ denote the complement in $\Omega$ of the space of eventually constant
  sequences."
- Theorem 1.10 (l.516–521): "For $\omega \in \Omega_+$, the group $G_\omega$ is of intermediate
  growth, and any finitely presented cover of $G_\omega$ is large."
- Corollary 1.11 (l.525–534): "Let $H$ be a finitely generated cover of one of $\mathfrak G$ (as in
  Theorem \ref{GrHa+i}), $\mathfrak B$ (as in Theorem \ref{Erschler}), or $G_\omega$,
  $\omega \in \Omega_+$ (as in Theorem \ref{ThGri84}). Any finitely presented cover of $H$ is
  large."

## Grigorchuk–Sidki, author PDF `sidkigrig3.pdf` (IJAC 14 (2004)), ghostscript text

- p. 1: "the 3-generated infinite 2-group G(2) constructed by the first author and shown to have
  intermediate growth".
- p. 1: "The groups G(2),G(3) have trivial centers and therefore are isomorphic to their inner
  group of automorphisms."
- p. 2: "Theorem 1. The group G(2) admits an infinite set of automorphisms of order 2 which
  generate a group V such that AutG(2) = (InnG(2))V and OutG(2) is elementary abelian 2-group of
  infinite rank."
- Abstract misprint: "elementary abelian 3- group of infinite rank"; Theorem 1 is used.

## Benli, arXiv:1112.1764, TeX `GMJ-11-0168.tex`

- l.37–40 (abstract): "We prove that if $H$ is a finitely generated normal subgroup of a finitely
  presented group $G$ with $G/H$ cyclic, then $H$ has ascending finite endomorphic presentation. It
  follows that any finitely presented indicable group without free semigroups has the structure of
  a semidirect product $H \rtimes \field{Z}$ where $H$ has finite ascending endomorphic
  presentation."
- l.491–494 (Remark 1): "the endomorphisms of the L-presentation of $H$ actually induce
  automorphism of $H$ and $H$ embeds into $G$ as a normal subgroup."
- l.498–502 (Remark 2): "I have been told by Mark Sapir (private communication) that not all
  finitely generated recursively presented groups embed into finitely presented groups
  \textit{as normal subgroups}. His example was the first Grigorchuk group."
- l.508: the conjectural characterization "A finitely generated group is a normal subgroup of a
  finitely presented group if and only if it has an ascending finite L-presentation where the
  endomorphisms induce automorphisms of the group."

## Grigorchuk survey, arXiv:1111.0512, `Grigorchuk10.tex`

- l.674–679: Sapir's observation that the finitely presented ascending HNN extension of $\mathcal
  G_\xi$ "cannot serve as a normal subgroup of any finitely presented groups".
- l.683–689: the de la Harpe–Grigorchuk observation, and "it would be interesting to find a finitely
  presented group with a normal subgroup of intermediate growth and to find a finitely presented
  group without a free subgroup on two generators (or perhaps even a finitely presented amenable
  group) that can be mapped onto a group of intermediate growth. This is discussed in detail in
  \cite{benli_grigorch_harpe:13}."
- l.1893–1896 (Theorem gap1) and l.1908–1911 (Theorem lubmann): the gap theorems for residually
  finite-$p$ and residually nilpotent groups.

## What this lane landed

1. Imports: `fp-covers-of-grigorchuk-groups-are-large`,
   `grigorchuk-group-has-trivial-center-and-elementary-abelian-out`,
   `fg-kernel-of-fp-onto-z-has-ascending-finite-l-presentation`,
   `residually-nilpotent-groups-below-exp-sqrt-growth-are-polynomial`.
2. Theorem `centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp` (elementary retract
   argument) and corollary `grigorchuk-group-is-a-normal-subgroup-of-no-fp-group`, a written proof of
   the fact Benli reports from Sapir, which answers the survey's normal-subgroup question negatively
   for $\mathfrak G$ itself.
3. Synthesis `fp-intermediate-growth-witness-exclusions`.

No novelty claimed.
