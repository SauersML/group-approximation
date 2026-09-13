# Ideas: a non-hyperlinear group via continuous model theory and computability

Idea lane `nh-model-theory`, 2026-09-13. Target: `non-hyperlinear-group`.
Nothing here is claimed as a theorem of the graph. Each approach records its
kill test and the result of running it.

## Baseline read first

Repo nodes read before ideating, so as not to repeat them:
`approximation-property-recognition-dichotomy` (existence iff `HYP_fp` is
undecidable iff `NONHYP_fp` is not r.e., and the second-level forms),
`nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound`,
`nonhyperlinear-existence-is-two-generator-simple`,
`kleene-mipco-self-destroying-game`, `canonical-profile-kleene-higman`,
`local-approximation-properties-are-marked-closed`,
`taller-vidick-entangled-long-code-citation`,
`free-direct-product-max-tensor-presentation-is-not-computable`,
`fp-residually-finite-groups-have-solvable-word-problem`.

Sources checked in this pass, at abstract level only:
- Goldbring–Hart, *The universal theory of the hyperfinite II_1 factor is not
  computable* (Bull. Symb. Logic, 2024).
- Arulseelan–Manzoor, arXiv:2508.21709 (IMRN 2026): locally universal tracial
  von Neumann algebras have undecidable universal theories and no computable
  presentation. The abstract says this builds on Lin's MIP^co = coRE.
- Lin, arXiv:2510.07162, *MIPco = coRE*.
- Mousavi–Nezhadi–Yuen, arXiv:2110.04651: "quantum value exactly 1" is
  Pi_2-complete for two-player games. Their abstract credits Slofstra with
  Pi_1-completeness of "commuting-operator value equal to 1".
- Slofstra, arXiv:1806.05267: a finitely presented group with at least
  subexponential hyperlinear profile.
- Taller–Vidick, arXiv:2507.22444. The abstract says the result proved has a
  constant soundness gap, and that "achieving the same result with ε=0 would
  imply the existence of a non-hyperlinear group".
- Dogon, arXiv:2211.10492: if Sp_{2m}(Z) is flexibly HS-stable, a
  non-hyperlinear group exists.
- Fournier-Facio–Gerasimova–Spaas, arXiv:2307.13155, and Eckhardt–Shulman,
  arXiv:2207.01089. The second shows that for amenable groups very flexible
  HS-stability is equivalent to maximal almost periodicity.

## Approach 1: gapless perfect-LCS separation

**Idea.**
- Let `P_qa` and `P_qc` be the sets of LCS games whose approximately-finite
  and commuting-operator values equal 1. Always `P_qa ⊆ P_qc`, and `P_qc`
  holds exactly when the central `J` is nontrivial in the solution group, so
  `P_qc` is Pi_1 (the relation `J = 1` is r.e.).
- If every group is hyperlinear, then `P_qa = P_qc`. A trace-preserving
  embedding of the solution group in `U(R^ω)` sends `J` to a symmetry that
  commutes with the generator images. Compressing to its `-1` spectral
  projection gives `J = -1` in a corner of `R^ω`, hence a perfect q_a
  strategy.
- So under "all groups hyperlinear" `P_qa` is Pi_1. Any many-one reduction
  from HALT with "halts ⇒ ω_qa = 1" and "does not halt ⇒ ω_qa < 1" is
  therefore a contradiction, and a non-hyperlinear solution group must exist.
- No constant soundness gap is needed; completeness must be exact.

**Would prove.** Existence, non-constructively: the witness is the solution
group of some game `G_M` with `M` non-halting.

**Kill test.** Is the sufficient condition already known, and is there an
obstruction?
- Taller–Vidick state the implication for their gapped statement with ε = 0.
  The gapless relaxation above is a sharpening of the same idea, not a new
  mechanism.
- Mousavi–Nezhadi–Yuen give exactly the Pi_2 hardness one would want, but for
  general games. What is missing is an LCS-ization that preserves "value
  exactly 1" in both directions.
- Taller–Vidick's introduction and the repo node
  `taller-vidick-entangled-long-code-citation` record the generic
  BCS-to-LCS obstruction.
- No counter-obstruction to the gapless form was found.

**Verdict: survives, as a sharpened target, not a new route.**
- Minimal input: many-one Sigma_1-hardness of exact q_a-value 1 on LCS games,
  with completeness exact and soundness gapless.
- Natural source: an exact-value-preserving LCS-ization of the
  Mousavi–Nezhadi–Yuen Pi_2-hard family.
- Next test: do the repo's BCS/LCS transformations (`bcs-to-lcs-exact-support-gap`,
  the cyclic equality splitting node) preserve "value exactly 1" in both
  directions for synchronous games?

## Approach 2: a word-problem filter for stability candidates

**Idea.**
- A hyperlinear group that is flexibly HS-stable is maximally almost periodic.
  When finitely generated it is then residually finite (Mal'cev), and when
  finitely presented its word problem is solvable (McKinsey; repo node
  `fp-residually-finite-groups-have-solvable-word-problem`).
- So a finitely presented, flexibly HS-stable group with unsolvable word
  problem is non-hyperlinear.
- The computability gain: unsolvable word problem is an explicit, checkable
  replacement for "not residually finite", which is Pi_2-complete for
  finite presentations (`residual-finiteness-of-finite-presentations-is-pi2-complete`).

**Would prove.** Existence, provided such a group is shown flexibly HS-stable
by a method that does not pass through hyperlinearity.

**Kill test.** Look for a candidate class and its known obstructions.
- **Amenable candidates die.** By Eckhardt–Shulman, very flexible HS-stability
  equals maximal almost periodicity for amenable groups. So Kharlampovich's
  finitely presented solvable groups with unsolvable word problem are not
  very flexibly HS-stable. This is consistent and gives nothing.
- **(T) candidates.** Infinite hyperlinear (T) groups are never HS-stable
  (Becker–Lubotzky, strengthened to local stability by
  Fournier-Facio–Gerasimova–Spaas). The flexible version is open, and Dogon's
  implication for Sp_{2m}(Z) is a different mechanism (central extensions of
  groups with solvable word problem).
- A quick search found no finitely presented (T) group with unsolvable word
  problem.
- The locator for "hyperlinear + flexibly HS-stable ⇒ maximally almost
  periodic" comes from search summaries and was not pinned in a primary
  source here.

**Verdict: unclear.** The criterion is clean and uses known ingredients, but
there is no candidate class with a stability technique independent of
hyperlinearity.

## Approach 3: a gap between group-language universal theories

**Idea.**
- Compare the universal theories, in the language of metric groups (words
  and the normalized HS distance), of `U(R^ω)` and of `U(M)` for a locally
  universal tracial `M`. The latter is undecidable by Arulseelan–Manzoor.
- Take a separating sentence that also yields exact relators in an ultrapower.
  The unitaries it produces would generate a group with one word bounded away
  from 1 in `M` but killed in every matricial approximation.

**Would prove.** Existence, if the separation can be made exact.

**Kill test (hand argument).**
- Let unitaries in `M^ω` satisfy finitely many relators exactly with
  `||u_w - 1||_2 = d`, and let `Γ` be the group they generate.
- If `Γ` is hyperlinear, a trace-preserving embedding in `U(R^ω)` gives matrix
  approximations of all of `Γ`'s relations with `||w - 1||_2 → √2`. So matrices
  already reach √2 on that sentence.
- A separation therefore needs `d > √2`, that is, a non-canonical trace value
  `τ(u_w) < 0`, such as a central involution driven to `-1`.
- That is approach 1, or the repo's character and trace-promotion programme
  (`canonical-trace-promotes-non-ce-profile`, `non-ce-trace-on-sofic-racg`).
- Undecidability of both theories gives no separation by itself.

**Verdict: killed as an independent route.** It reduces to approach 1 or the
existing character programme.

## Approach 4: a locally universal group von Neumann algebra

**Idea.**
- Suppose `L(U)` is locally universal, meaning every separable tracial von
  Neumann algebra embeds in `L(U)^ω`. Then `U` is not hyperlinear.
- Otherwise `L(U)` would sit in `R^ω`, so `L(U)^ω` embeds in an ultrapower of
  `R`, and every tracial von Neumann algebra would be Connes-embeddable. That
  contradicts MIP* = RE (and Goldbring–Hart's alternative proof).
- So it suffices to build a single countable group whose group von Neumann
  algebra is locally universal, instead of one rigid relation pattern.
- A candidate family: groups assembled from solution or synchronous-game
  groups over all games, so that their game corners approximate the universal
  sentences Lin and Arulseelan–Manzoor use.

**Would prove.** Existence, with a stronger structural statement.

**Kill test.**
- (a) The implication is solid.
- (b) Necessary condition, via Arulseelan–Manzoor: a locally universal
  algebra has no computable presentation. If a group with solvable word
  problem gives a computable presentation of `L(U)`, then `U` must have
  unsolvable word problem. That step is standard but was not checked against
  their definition.
- (c) Repo duplicate scan: no node states "some `L(U)` locally universal ⇒ `U`
  non-hyperlinear". The entry point still requires turning synchronous
  algebras into group algebras, which is the repo's groupification programme
  and is blocked by the BCS-to-LCS obstruction.

**Verdict: survives** as a new existence form, stronger than needed. Its
tractability is unclear.
- Next test: can a free product of all LCS solution groups have a locally
  universal `L(U)` despite the BCS-to-LCS obstruction? Or does the obstruction
  already fence off every group von Neumann algebra built only from solution
  groups?

## Approach 5: a self-referential diagonal and marked-group compactness

**Idea.** Either a recursion-theorem group that searches for its own approximate
representations and adds relators to kill them, or density of hyperlinear
marked groups.

**Kill test.** Repo duplicates: `kleene-mipco-self-destroying-game`,
`canonical-profile-kleene-higman`, the threshold-free reverse Kleene diagonal,
the dichotomy (D2), and `local-approximation-properties-are-marked-closed`.
There is also a structural obstruction: the added relators must hold exactly in
the group while killing approximate separations, and that is the missing
stability-gap relation itself.

**Verdict: killed (duplicate).**

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Gapless perfect-LCS separation | survives, sharpened target, not new |
| 2 | Word-problem filter for flexible HS-stability | unclear |
| 3 | Group-language universal-theory gap | killed (reduces to 1 or the character programme) |
| 4 | Locally universal group von Neumann algebra | survives, new existence form |
| 5 | Self-referential diagonal / marked density | killed (duplicate) |
