---
rg: 2
id: nst-weakly-sofic-perfect-groups-psl-conjugacy-models
kind: claim
title: A nontrivial finitely generated perfect weakly sofic group maps nontrivially to a projective-rank ultraproduct of groups PSL_n(q)
distinct_from:
  nst-simple-weakly-sofic-groups-are-psl-approximable: that is the statement of Nikolov--Schneider--Thom Theorem 4, with an arbitrary invariant length on PSL_n(q); this is the stronger conclusion reached in their proof, where the length is the conjugacy length, equivalently the projective rank length.
---

**ESTABLISHED (literature import)** by `nst-weakly-sofic-perfect-groups-psl-conjugacy-models-citation`.

Let `P` be a nontrivial finitely generated perfect **Fin**-approximable (that is, weakly sofic) group. Then `P` has a
nontrivial homomorphism into a metric ultraproduct `prod_U (PSL_(n_i)(q_i), l^pr_i)` with the projective rank length.
Since `l^c` and `l^pr` are Lipschitz equivalent on nonabelian finite simple groups, the conjugacy length gives the same
ultraproduct group.

**In particular.** A finitely generated simple weakly sofic group embeds in such an ultraproduct, because the
homomorphism is injective by simplicity.

**Source status.** This is the proof of Theorem 4 in Nikolov--Schneider--Thom, arXiv:1703.06092v2, pp. 12--14. The
paper *sketches* the last step, the embedding of the abstract ultraproduct `K/L` of simple factors into
projective-rank ultraproducts of `PSL_n(q)`. The published version was not checked. An independent proof of the
consequence used downstream, which needs only the statement of Theorem 4, is route
`fg-simple-weak-sofic-linear-sofic-via-near-scalar-covering`.
