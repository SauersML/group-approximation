---
rg: 2
id: nst-weakly-sofic-perfect-groups-psl-conjugacy-models-citation
kind: route
title: Nikolov--Schneider--Thom, proof of Theorem 4, pp. 2, 4 and 13--14 of arXiv:1703.06092v2
target: nst-weakly-sofic-perfect-groups-psl-conjugacy-models
requires: []
---

Read on 2026-09-13 by lane `ex3-weak-sofic-fg-dichotomy` from the arXiv PDF (arXiv:1703.06092v2, stamped 24 May 2017),
pages 1--5, 10--14 and 19--20, as page images. The copy is in lane `ex2-weak-sofic-bounded-factors`'s `lit/nst.pdf`.

**Page 2 (Introduction), verbatim:** "In Section 4, using results of the first author from [18] and of Liebeck and
Shalev from [16], we prove that any non-trivial group which is approximable by finite groups has a non-trivial
homomorphism into a metric ultraproduct of finite simple groups of type PSL_n(q) with conjugacy length function (see
Theorem 4)."

**Page 4, verbatim:** "The projective rank length function ℓ^pr_G is defined if G ≤ PGL_n(q) for some n ∈ N and q a
prime power; ℓ^pr_G(g) := (1/n) min{rk(1 − ĝ) | ĝ some lift of g}." And: "For example, ℓ^c and ℓ^pr are Lipschitz
equivalent on the class of non-abelian finite simple groups, which follows from [16] (see the argument at the end of
Section 4)."

**Page 5, Example 1, verbatim:** "A group is sofic (resp. weakly sofic) if and only if it is Alt-approximable (resp.
Fin-approximable) as an abstract group."

**Pages 13--14 (proof of Theorem 4, P = F/N perfect), verbatim excerpts:**
- "Since F̂/KM is solvable as a quotient of F̂/K, this homomorphism restricts to KM/LM, which is a non-trivial
  homomorphic image of the metric ultraproduct K/L. Since the latter is simple by Proposition 3.1 of [25], we are only
  left to show that K/L, which is a metric ultraproduct of the sequence (S_i)_(i∈I) of finite simple groups from above
  with conjugacy length function with respect to some ultrafilter U, embeds into a metric ultraproduct of groups
  PSL_(n_i)(q_i) equipped with the conjugacy length function ℓ^c_i (i ∈ I), since then P would have the same property."
- "Let us briefly sketch the argument for this: [...]"
- "Hence we can embed our ultraproduct K/L into an ultraproduct of groups PSL_(n_i)(q_i) equipped with the projective
  length function ℓ^pr_i (i ∈ I). But by the former Lipschitz equivalence, ℓ^pr_i can be replaced by the conjugacy length
  function ℓ^c_i (i ∈ I). This ends the proof."

**Bibliography (p. 19):** "[16] Martin W. Liebeck and Aner Shalev, Diameters of finite simple groups: sharp bounds and
applications, Annals of mathematics (2001), 383–406." "[18] Nikolay Nikolov and Dan Segal, Generators and commutators
in finite groups; abstract quotients of compact groups, Inventiones mathematicae 190 (2012), no. 3, 513–602." "[25] Abel
Stolz and Andreas Thom, On the lattice of normal subgroups in ultraproducts of compact simple groups, Proceedings of the
London Mathematical Society 108 (2014), no. 1, 73–102."

**Reading.** Theorem 4's hypothesis (p. 11) is "finitely generated **Fin**-approximable". In the perfect case the proof
shows `P -> K/L` nontrivial, then embeds `K/L` in a projective-rank ultraproduct of groups `PSL_(n_i)(q_i)`. The target
claim records exactly that. The embedding step is labelled a sketch by the authors.
