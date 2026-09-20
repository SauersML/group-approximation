---
rg: 2
id: peterson-thom-sl2-s-integer-character-rigidity
kind: claim
title: Extremal characters of SL2 over S-integers with infinitely many units factor through finite quotients or vanish off the center
distinct_from:
  character-rigidity-equals-hyperfinite-hs-stability: that imports the Dogon--Vigdorovich equivalence for higher rank lattices and mentions Peterson--Thom only in prose; this imports the Peterson--Thom SL2 theorem itself, verbatim, as a reusable node.
  bs14-character-split-leaves-only-the-regular-microstate-face: that applies the rigidity to cut one tracial ultraproduct into a finite and a regular face; this is the bare literature statement it uses.
  sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index: that is the normal subgroup theorem, a statement about subgroups; this is the classification of extremal characters.
---

**Established by citation.** J. Peterson, A. Thom, *Character rigidity for
special linear groups*, J. reine angew. Math. 716 (2016), 207--228;
arXiv:1303.4007. The source file `OAsuperrigidity140203.tex` (arXiv
e-print, retrieved 2026-09-19), environment `\label{secondmain}` in the
subsection "Characters on SL_2(BS^{-1})", transcribed verbatim:

> Let $B$ an order in the ring of algebraic integers of some number field.
> Let $S \subset B$ be a multiplicative subset and $BS^{-1}$ the
> corresponding localization. Assume that $BS^{-1}$ has infinitely many
> units. Let $\tau: SL_2(BS^{-1}) \to \mathbb C$ be an extremal character.
> Then either
> 1. the character $\tau$ factorizes through a finite quotient of
>    $SL_2(BS^{-1})$, or
> 2. $\tau$ is induced from $C \subset SL_2(BS^{-1})$.

Here `C` is the **center** (not the modular group), and "induced from" is
defined in the same source, introduction, verbatim: "We say that a character
$\varphi$ is induced from a normal subgroup $\Lambda \subset \Gamma$, if
$\{ g \in \Gamma \mid \varphi(g) \neq 0\} \subset \Lambda.$" The proof ends
with "this shows that $\tau(g) = 0$ for any non-central element $g$".

**Instance used in this graph.** `B = Z`, `S = {2^k}`, so `BS^{-1} = Z[1/2]`,
whose units `±2^Z` are infinite. Every extremal character of
`SL_2(Z[1/2])` either factors through a finite quotient or vanishes off the
center `{±1}`.
