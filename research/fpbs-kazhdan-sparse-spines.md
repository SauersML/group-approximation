---
rg: 2
id: fpbs-kazhdan-sparse-spines
kind: claim
title: All infinite Kazhdan groups admit arbitrarily sparse FIID connected infinite vertex sets
root: true
---

OPEN restricted research target. Together with the sparse-spine lemma it would prove fixed price one for this class, not for every countable group.

## Attempts

* **Use the sparse-spine lemma.** `fpbs-sparse-spine-cost-bound` proves that
  an FIID vertex set `I` that is almost surely nonempty, infinite and
  connected in the Cayley graph, with density `theta=P(o in I)`, gives
  `C^*(Gamma) <= 1+(d/2-1)theta`: keep the ambient edges inside `I` and attach
  every outside vertex along a strictly decreasing distance to `I`, breaking
  ties with extra iid labels. So spines of arbitrarily small density would
  give fixed price one for this class. The reduction is proved; only the
  construction is missing.
* **Upgrade the Hutchcroft--Pete construction to a factor of iid.**
  `fpbs-kazhdan-groups-have-cost-one` already gives a cost-one action for
  every infinite Kazhdan group, so it is natural to try to make the witnessing
  low-cost invariant percolation admissible. **Where it dies:** Section 5 of
  `research/artifacts/fpbs/exploration.md` cites [HP, Remark 4.4] for the
  reason this fails: a low-cost invariant percolation construction can cease
  being a factor of iid before producing the positive-frequency cluster needed
  to upgrade a minimum-cost result to a maximal, that is Bernoulli, cost
  result. Admissibility rather than density is the obstruction, and it is the
  same gap that keeps the published theorem at cost one instead of fixed price
  one.
* **Colour whole infinite components.** Assigning a globally constant random
  colour to an infinite component is the obvious way to select a sparse
  connected set. **Dead:** such a rule is not a factor of iid. Section 3 of
  `research/artifacts/fpbs/creative-branches.md` proposes overlapping infinite
  cells with repeated contact opportunities instead, following the
  infinite semi-touching and horoball geometry used in recent product-group
  proofs, and does not carry it out for property (T) groups.
* **Certify connectivity without short routes.** The well-founded replacement
  lemma of Section 3.1 lets a deleted edge of level `m` be replaced by a
  finite path using retained edges and deleted edges of lower level, so
  connectivity survives arbitrarily long detours and a limit of cycle
  deletions. **Where it dies:** the lemma is purely qualitative. It supplies
  no edge-intensity bound and therefore no sparsification, which is the entire
  content of this claim.
* **Check which Kazhdan groups published theorems already cover.** Read from
  source on 2026-09-12. Hutchcroft--Pete (arXiv:1810.11015, introduction)
  leave fixed price one for Kazhdan groups open, say their construction is
  very far from a factor of iid, and tie the question to Abert--Nikolov's
  conjecture that higher-rank lattices have absolute rank gradient `0`.
  Fraczyk--Mellick--Wilkens (arXiv:2307.01194) prove that every pmp action of
  a lattice in a higher-rank semisimple real Lie group, or in a product of at
  least two automorphism groups of regular trees, has cost one; their ideal
  Poisson--Voronoi cells pairwise share unbounded borders. Slutsky's preprint
  arXiv:2607.20273 (e-print fetched 2026-09-12, Corollaries
  `cor:local-field-semisimple`, `cor:affine-buildings` and `cor:lc-products`)
  gives fixed price one for every lattice in `G(k)` with `k` a local field and
  `rank_k G >= 2`, for every lattice in a closed unimodular subgroup acting
  cocompactly on a locally finite thick regular affine building of Euclidean
  rank at least `2`, and for every lattice in a product of two noncompact,
  compactly generated, unimodular lcsc groups. No counterexample lives in
  those classes. **Where it dies:** the stated classes do not include lattices
  in `Sp(n,1)` or `F_4^(-20)`, which have property (T) and real rank one, nor
  Kazhdan Golod--Shafarevich groups, and no source read here covers them.
  Slutsky's metric Corollary `cor:lc-metric` asks for
  `liminf_R lambda(B(2R+D))/lambda(B(R))^2 = 0`. With the symmetric-space
  metric in real rank one, `lambda(B(R))` grows like `e^(hR)` with no
  polynomial factor, so the ratio stays above a positive constant and that
  corollary does not apply. Whether his Theorem `thm:lc-criterion` holds there
  with other sets `F_n` is not decided here. The rank-one route proposed by
  Fraczyk--Mellick--Wilkens is their open Question `q-DualGraphCritical`:
  whether `p_u` of the ideal dual graph vanishes almost surely for some
  rank-one symmetric space. A further question of theirs asks whether
  `p_u=0` would give fixed price one.
* **Use the percolation characterization of property (T).** Read from source:
  Mukherjee--Recke, arXiv:2303.17429, Theorem `maintheorem-Kazhdan`: a
  finitely generated group has property (T) if and only if some `alpha*<1`
  makes every invariant bond percolation with
  `E deg_omega(o) > alpha* deg(o)` satisfy `inf_{g,h} tau(g,h) > 0`.
  **Where it dies:** the theorem constrains only percolations of density
  close to one and does not involve factors of iid. A spine needs density
  tending to zero inside the FIID class, where the theorem says nothing.
