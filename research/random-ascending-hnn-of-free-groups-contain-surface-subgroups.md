---
rg: 2
id: random-ascending-hnn-of-free-groups-contain-surface-subgroups
kind: claim
title: Random ascending HNN extensions of free groups, and Sapir's group, contain surface subgroups
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this covers HNN extensions of free groups along random endomorphisms and one explicit endomorphism.
  cyclic-graphs-of-free-groups-contain-surface-subgroups: that needs cyclic edge groups; here the edge group is the whole free group.
---

For fixed rank `k >= 2`, the HNN extension `F *_phi` of `F = F_k` along a random
endomorphism `phi` of length `n` contains an essential surface subgroup with
probability at least `1 - O(C^{-n^c})`. Sapir's group `C = <a,b> *_phi`, with
`phi: a -> ab, b -> ba`, contains a closed surface subgroup of genus 28.

D. Calegari and A. Walker, *Surface subgroups from linear programming*,
arXiv:1212.2618. TeX source `sslp.tex`, fetched on MSI 2026-09-13.

- **Random f-folded Surface Theorem** (l.1353--1356), verbatim: "Let $k\ge 2$ be
  fixed, and let $F$ be a free group of rank $k$. Let $\phi$ be a random
  endomorphism of $F$ of length $n$. Then the probability that $F*_\phi$ contains
  an essential surface subgroup is at least $1-O(e^{-n^c})$ for some $c>0$." The
  introduction (l.166--171) states the bound as $1-O(C^{-n^c})$ for some $C>1$.
  A random endomorphism of length `n` sends each generator to an independent
  uniformly random reduced word of length `n` (l.1325--1330).
- **Sapir's group** (Definition l.2050--2051; Theorem l.2061--2062), verbatim:
  "Sapir's group $C$ contains a closed surface subgroup of genus 28." The paper says
  (l.2054--2055) that Sapir posed this as Problem 8.1 of his problem list.
- **Injectivity criteria** used for these results:
  - Proposition `proposition:f_folded_injective` (l.990--991): "Suppose $f:R \to R$
    is an immersion, and $X$ is $f$-folded. Then $S*_f(X) \to K$ is
    $\pi_1$-injective."
  - Proposition `proposition:bounded_f_folding_injective` (l.1266--1268): "Suppose
    $f:R \to R$ has bounded folding, and $g:X \to R$ admits bounded $f$-folding.
    Then $S*_f(X) \to K$ is $\pi_1$-injective."
- **Known cases listed by the authors** (l.133--141, "this list is not exhaustive"):
  Coxeter groups (Gordon--Long--Reid); graphs of free groups with cyclic edge groups
  and `b_2 > 0` (Calegari); hyperbolic 3-manifold groups (Kahn--Markovic); certain
  doubles of free groups (Gordon--Wilton, Kim--Wilton, Kim--Oum). Not read at source.
