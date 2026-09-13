# Lane solve-sofic-amalgam, 2026-09-13: amalgams over non-amenable edge groups

**Question.** Is `A *_H B` sofic for sofic `A, B` and non-amenable `H`? Test
case: `SL_3(Z) *_{F_2} SL_3(Z)`.

## Where the graph already stood

- **Nonsofic.** Doubles over infranormal Kazhdan edge groups are nonsofic
  (`kt-pair-group-double-is-nonsofic`, Kun--Thom v3 Theorem A). So the general
  question is answered negatively, but the free edge groups asked about here
  are not covered.
- **Sofic.** A sofic coset action makes the double sofic
  (`sofic-coset-action-makes-amalgam-double-sofic`), and every double of a free
  group is sofic (`free-group-doubles-over-any-subgroup-are-sofic`).
- **Weakly sofic.** Doubles of residually finite groups are weakly sofic
  (`residually-finite-doubles-are-weakly-sofic`).
- **Thin pair.** `SL_3(Z)` has an explicit free, profinitely dense, property-tau
  subgroup (`explicit-sl3-thin-codense-tau-pair`). Before this lane it fed only
  unitary HNN statements.

## What this lane proved (unreviewed)

- **Fold theorem**, `codense-tau-amalgams-fold-under-flexible-stability`. Take
  flexibly stable vertex groups and an edge group with a uniform gap on finite
  actions. Every sofic approximation then identifies `i_0(a)` with `i_1(b)`, in
  Hamming distance, for every `(a,b)` in the profinite closure of the edge
  graph. So the amalgam is not sofic whenever that graph is not separable.
  - Mechanism: in the doubled finite action, the swap vector's defect equals the
    Hamming distance between the two vertex actions.
  - The edge gap and the profinite closure transfer agreement on the generators
    to the whole closure.
- **SL_3 endpoint**, `sl3z-thin-free-double-nonsofic-if-sl3z-flexibly-stable`.
  If `SL_3(Z)` is flexibly stable, then `SL_3(Z) *_{<a,b>} SL_3(Z)` is not
  sofic. It is finitely presented, and the edge group is free of rank two. The
  same holds for `SL_n(Z)`, `n >= 3`.
- **New OPEN hole**, `sl3z-is-flexibly-permutation-stable`.

## Directive step 2: different embeddings

The fold inequality (FT1) is stated for two embeddings. After flexible
correction, two honest vertex actions whose restrictions to `H` are Hamming-close
agree across the whole profinite closure of the graph
`Delta = {(iota_0 h, iota_1 h)}`.

- **Doubles.** Rigidity forbids the conjugate restricted approximations that
  soficity needs, conditional on (FS).
- **Twisted embeddings.** For `SL_3(Z)`, the conclusion needs a uniform gap for
  the graph subgroup on all finite `SL_3(Z) x SL_3(Z)`-sets, i.e.
  arbitrary-modulus expansion for Zariski-dense subgroups of `SL_3 x SL_3`.
  Not pinned. Gap recorded.

## Converse direction (attempted, not proved)

Does soficity of `G *_C G` force soficity of the action of `G` on `G/C`?

- **The candidate.** `G/C` is the orbit of the base point in the retract action
  of `D = K x| i_1(G)` on `D/i_1(G)`, with `K` free.
- **The obstruction.** GKP orbit charts need an internal labeling that is
  invariant under `C` and transversal to `G \ C`. The orbit partition of the
  second vertex copy is not internal, and finite-scale Voronoi labelings fail
  on expander Schreier graphs.
- **Status.** Undecided.

## Literature pins (arXiv TeX fetched on MSI, verbatim)

**Bowen--Burton, arXiv:1906.02172** (`flexiblestability-2019.09.26.tex`):

- Abstract: "We establish that if $\mathrm{PSL}_d(\mathbb{Z})$ is flexibly
  stable for some $d \geq 5$ then there exists a group which is not sofic."
- l.147: "We say that a sofic group $G$ is \textbf{flexibly stable} if every
  sofic approximation to $G$ is conjugate to a perfect sofic approximation to
  $G$."
- l.149: "In \cite{2018arXiv180900632B} it is shown that no infinite property
  (T) group is strictly stable."
- l.157: "We need that $d\ge 5$ only because this condition guarantees that all
  $\mathrm{PSL}_2(\mathbb{Z})$ orbits in $\mathrm{PSL}_d(\mathbb{Z}/p\mathbb{Z})$
  have density bounded by a constant which is strictly less than 1. We do not
  know whether the result can be improved to $d \in \{3,4\}$."
- Theorem `thm:general` (l.167–196): flexibly stable `H` with subgroups `A, B`
  satisfying orbit containment, an involution `omega`, orbit density `lambda > 1`,
  and property `(tau)` for `A` makes
  `<H, t | t^2 = 1, t a t^(-1) = omega(a)>` nonsofic.
- Lemma `lem.right` (l.320): profinitely dense finitely generated subgroups of
  `PSL_d(Z)`, `d >= 3`, have property `(tau)` via Bourgain--Varju plus the
  congruence subgroup property.

**Becker--Lubotzky, arXiv:1809.00632** (`main.tex`, l.1106–1137): for
`sigma` in `Sym(n)` and `tau` in `Sym(m)` with `n <= m`,

```text
d_n^flex(sigma, tau) = (1/n) ( |{x in [n] : sigma(x) != tau(x)}| + (m - n) ),
```

"We say that $\Gamma$ is $\calP$-\emph{flexibly}-stable if every
$\calP$-stability-challenge for $\Gamma$ has a flexible solution."

**GKP Definition 2.1(5)** and Proposition 2.9: verbatim in
`research/artifacts/gkp-2401-04945-verified.md`. Re-read from the TeX on MSI,
l.191–304.

## Exact gap

1. **The hypothesis.** Flexible (Bowen--Burton) stability of `SL_3(Z)`. It is
   open, and the lane found no route to it.
2. **Unconditional nonsoficity.** Nonsoficity of `SL_3(Z) *_{F_2} SL_3(Z)`
   without that hypothesis would need a different finite-model obstruction.
3. **Positive side.** Soficity would need non-correctable almost-actions of
   `SL_3(Z)` whose restrictions to `F_2` can be twisted apart, which refutes
   hole 1.
