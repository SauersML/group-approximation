# Finitely presented groups of intermediate growth: source pins (2026-09-13)

Sources fetched on MSI under `/scratch.global/sauer354/solve-fp-intermediate-growth/src/`.

## Grigorchuk, arXiv:1111.0512 (TeX source `Grigorchuk10.tex`)

- l.644–649: "All known examples of groups of intermediate growth are infinitely presented
  groups. \begin{prob} \label{finitepresent} Is it true that the growth function of a finitely
  presented group is equivalent either to a polynomial or to the exponential function $2^n$?
  \end{prob}"
- l.652–657: "In \cite{grigorch-pak:intermediate_growth}, it is conjectured that there are no
  finitely presented groups of intermediate growth. At the same time, the author suggests even a
  stronger conjecture. \begin{conj} A finitely presented group either contains a free
  subsemigroup on two generators or is virtually nilpotent. \end{conj}"
- l.669–673: the finitely presented envelope of the first Grigorchuk group "is an ascending
  $HNN-$extension of $\mathcal{G}_{\xi}$ ... Unfortunately (or fortunately), the group
  $\tilde{\mathcal{G}_{\xi}}$ has exponential growth but shares the property of amenability".
- l.683–685: "it was observed by P. de la Harpe and the author that any finitely presented group
  $\hat{\mathcal G}$ that can be homomorphically mapped onto $\mathcal{G}$ contains a free subgroup
  on two generators and hence is of exponential growth."
- l.883–886: the elementary amenable quotient theorem (imported in
  `no-free-semigroup-ea-quotient-kernels-are-fg-citation`).
- l.831–833, l.1084, l.1088–1090: Milnor–Wolf and Gromov (imported in
  `gromov-and-milnor-wolf-growth-alternatives-citation`).

## Bartholdi–Grigorchuk–Šunić, *Branch groups*, arXiv:math/0510294 (TeX source)

- `presentation.tex` l.4–5: "Branch groups are probably never finitely presented and this is
  established for the known examples."
- `presentation.tex` l.54: "The first Grigorchuk group $\Gg$ is not finitely presented."
- `presentation.tex` l.163–165: "\begin{corollary} \label{theorem:spinalnotfp} No torsion spinal
  group is finitely presented. \end{corollary}"
- `questions.tex` l.68: "Do there exist finitely presented branch groups?"

## What this lane added

1. `ascending-hnn-non-surjective-contains-free-subsemigroup`: explains why every ascending HNN
   envelope along a non-surjective endomorphism has exponential growth.
2. `intermediate-growth-z-quotient-kernels-fg-intermediate`: witnesses with a map onto `Z` are
   `N ⋊ Z` with `N` finitely generated of intermediate growth.
3. `fp-intermediate-growth-iff-subexponential-truncation`: the question is equivalent to finding
   an intermediate growth group with a truncated presentation of subexponential growth, and any
   witness has a neighbourhood of subexponential quotients in the space of marked groups.

None of these is new mathematics as far as checked; no novelty is claimed.
