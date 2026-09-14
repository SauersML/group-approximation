# Mean-free amenable actions of Thompson's F (lane hl-f-mean-free-actions, 2026-09-14)

**Question.** The reduction of `thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived` makes
following-model soficity of `F` equivalent to a mean-free amenable action of `F`: an `F`-set with an
invariant mean `m` and `m(Fix(g)) = 0` for all `g ≠ e`. Does `F` admit one?

**Verdict.** Not decided. This lane contributes three things:
- the literature pins behind the notion;
- a split of every witness into two shapes, with every bounded configuration type killed;
- a barrier: any refutation proves `F` nonamenable, and any construction proves `F` sofic.

## 1. Literature pins

- **Elek–Szabó (Math. Ann. 332 (2005); arXiv:math/0408400).**
  - The notion is their *essentially free amenable action* (Definition 1.3), with a Følner and a
    non-paradoxical characterization (Theorem 3).
  - The source also has amenable or residually finite ⇒ existence (Proposition 4.3), property (T) ⇒
    (existence ⇔ RF) (Proposition 4.4), and the obstruction subgroup `N_Γ` (Proposition 5.1).
  - Node `elek-szabo-essentially-free-amenable-actions`.
  - **Priority correction.** `mean-free-amenable-actions-residually-amenable-and-sofic` (items 1, 3) and
    `kazhdan-groups-mean-free-amenable-iff-residually-finite` restate Propositions 4.3–4.4 and part of
    Theorem 3 without citing the source. They disclaim novelty but lack the citation; the new node
    records the priority in its `distinct_from`.
- **Chaudkhari (arXiv:1809.05146v2).**
  - Theorem 3.1: `H ≤ F` is confined iff `St⁰_(F')(S) ≤ H ≤ St_F(S)` for some finite `S ⊂ [0,1]`.
  - Node `thompson-f-confined-subgroups-fix-finite-sets`.
  - Remark 1 there: Schreier graphs of confined subgroups are amenable.
- **Savchuk (Geom. Dedicata 175 (2015); arXiv:1105.4017).** Abstract, verbatim: "As applications we prove
  that the pointed Schreier graphs of points from $(0,1)$ are amenable, have infinitely many ends, and
  are pairwise non-isomorphic." Not made into a node; it is consistent with the end-rigid node.
- **Soficity and amenability of `F`.** Both open. Nothing found that decides the existence of an
  essentially free amenable action of `F`.

## 2. The split (`thompson-f-mean-free-actions-dense-configurations-or-unconfined`)

- **Canonical configurations.** For a point `ω` with confined stabilizer, `S(ω) = Fix_(0,1)(Stab(ω))` is
  finite and equivariant, and every commutator supported off `S(ω)` fixes `ω`.
- **Two shapes.** `F` has a mean-free amenable action iff one of these holds:
  - (I) finite subsets of `(0,1)` carry an invariant mean meeting every open interval almost surely;
  - (II) some `F`-set with only non-confined stabilizers carries a mean-free mean.
- **Bounded types die.** `m(Moved(c) ∩ {|S(ω)| ≤ k}) = 0` for all `k`, by `k+1` disjoint commutators. So
  every transitive `F/H` with `H` confined has `t = 0`.
- **Profile of (I).** `m(n_I/n_(I')) = 0` for `I ⊆ int(I')`: points hug the ends of every interval at every
  scale.
- **Amenability.** If `F` is amenable, both shapes exist: (I) through dyadic grids pushed by Følner sets,
  (II) through the regular action.
- **Obstruction group.** `N_F ∈ {1, F'}` (Elek–Szabó 5.1 plus normal subgroups of `F`).

## 3. Natural actions (directive step 2)

| F-set | stabilizer | confined? | `t = m(Moved(c))` | reason |
|---|---|---|---|---|
| dyadic rationals; any point of `(0,1)` | `St_F(x)` | yes | 0 | item 3 (`k = 1`) |
| Cantor set / boundary of the tree | between `St⁰_(F')({x})` and `St_F({x})` | yes | 0 | item 3 |
| parabolic, breakpoint and germ stabilizers | same shape | yes | 0 | item 3 |
| finite configurations of fixed size `k` | `St_F(S)` | yes | 0 | item 3 |
| all finite configurations (`Conf`) | `St_F(S)` | yes, unbounded `k` | open = shape (I) | gap |
| `F_Z`, `Z` with interior (end-rigid, interval) | rigid stabilizers | no | `t > 0` ⇒ `F` amenable | interval-coset node |
| amenable `H` (incl. `H = e`) | `H` | no | invariant mean ⇒ `F` amenable | interval-coset node, item 3 |
| stabilizers of infinite closed sets, subgroups with no rigid subgroup | varies | typically no | open = shape (II) | gap |

## 4. Why no decision was reached here

- **Every refutation proves nonamenability.** Amenability of `F` gives (I), (II) and a mean-free action
  (item 5). Any contradiction derived from a hypothetical witness therefore proves `F` nonamenable.
- **A test of that barrier.** The lane derived multiscale constraints for (I), `B(x, r/2) ≤ ε B(x, r)`
  in mean for every point and scale. It then checked that finite configurations with exponentially
  graded counts satisfy any finite family of them, as the barrier predicts.
- **Every construction proves soficity.** Constructing (I) or (II) proves `F` sofic.
- **The natural candidates.** Poisson and i.i.d. point models are Hellinger-perturbations of the Koopman
  representation on `ℓ²(D)` or `L²(0,1)`. They need almost invariant vectors whose defect is small
  relative to their mass on every interval. This was not pursued to a theorem.

## 5. Exact gap

- **(I)** An invariant mean on finite subsets of `(0,1)` under which configurations meet every interval.
  Its profile (item 4) forces concentration at the ends of every interval at every scale.
- **(II)** A mean-free invariant mean on an `F`-set all of whose stabilizers are not confined. Such
  a stabilizer `H` satisfies `St⁰_(F')(S) ≤ H ≤ St_F(S)` for no finite `S`. By Chaudkhari Theorem 4.1 their orbital
  graphs have exponential uniform growth, and their rooted Schreier graphs approach the Cayley graph.
- **Obstruction direction.** `N_F = F'`, i.e. every amenable `F`-action gives full mass to the fixed
  points of every `g ∈ F'`, would refute following-model soficity. It would also prove `F` nonamenable.

## 6. Compute

- MSI was down for most of the lane, and no jobs were run.
- Local work was limited to extracting text from two arXiv PDFs.
