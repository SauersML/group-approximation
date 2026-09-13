# Non-free and non-expansive hosts for a finitely presented infinite simple amenable group

Lane solve-fp-amenable-nonfree-hosts, 2026-09-13. Target: gap (L2) of
`fp-infinite-simple-amenable-group`, recorded as case (S2) there and as "non-free or
non-expansive groupoid hosts" in `research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part1.md`,
Section 5.

The root and the Labbé, Penrose and `Z^d` full-group nodes belong to peer lanes. Only new
files were added.

## 1. Outcome

Three elementary theorems landed. Cairn computes them ESTABLISHED; they have not been
independently reviewed, and no novelty is claimed.

1. **`equicontinuous-action-full-group-fg-subgroups-are-rf`.** Every finitely generated
   subgroup of the full group of an equicontinuous Cantor action is residually finite, with
   no freeness or minimality hypothesis.
   - This kills groupoids of germs of groups acting on rooted trees, with isotropy, including
     bounded automaton groups. That was the candidate proposed for step 2 of this lane.
   - It also kills odometers and profinite actions.
2. **`fg-full-group-subgroups-factor-onto-subshift-full-groups`.** A finitely generated
   subgroup of the full group of any Cantor `Λ`-system maps onto a subgroup of the full group
   of a subshift factor over the same `Λ`. The map is an isomorphism when the subgroup is
   infinite simple.
   - So non-expansive hosts add nothing.
   - For abelian `Λ` and minimal `X`, the factor is a free minimal subshift over an infinite
     quotient of `Λ`, which is case (S1).
3. **`topologically-free-subshift-fp-subgroups-extend-to-sft`.** The SFT extension theorem,
   its simple-group corollary, and the periodic-approximation obstruction all hold under
   topological freeness instead of freeness.

The root stays OPEN. What is left of (S2) is Section 4.

## 2. Step 2 of the directive: germ groupoids of bounded automaton groups

- **Geometry.** A group `H ≤ Aut(T)` of a locally finite rooted tree acts on `∂T` by
  isometries of `d(x, y) = 2^{-|x ∧ y|}`.
- **Full groups.** The topological full group of its germ groupoid is `[[H ~ ∂T]]`: an element
  agreeing locally with elements of `H` has a locally constant cocycle, by compactness.
- **Result.** By theorem 1, every finitely generated subgroup of that full group permutes the
  vertices of every level below a fixed depth, so it is residually finite.
- **No simple subgroups.** No finitely generated infinite simple group lies there, whether or
  not the action is topologically free. This includes the alternating full group of the germ
  groupoid of any bounded automaton group.
- **Consistency checks.**
  - The Röver–Nekrashevych groups `V_d(H)` also use the one-sided shift, whose germs change
    depth. They are not in `[[H ~ ∂T]]`; they contain `V` and are already dead through
    `amenable-full-group-forces-invariant-measure`.
  - The fragmentation groups of dihedral actions (Nekrashevych's simple periodic groups) live
    over minimal `Z`-subshifts and are already dead through
    `periodic-approximable-subshifts-host-no-fp-simple-group`.
- **Not re-read here.** The finite-presentation theorems for full groups of expanding or
  hyperbolic groupoids (Nekrashevych, arXiv:1312.5654). Per
  `fp-simple-group-in-amenable-orbit-full-group`, Attempts, every finite-presentation theorem
  found for full groups uses compression, so those hosts carry no invariant measure and fall
  under `amenable-full-group-forces-invariant-measure`.

## 3. Where Theorem G breaks for non-free subshifts

Theorem G is `fp-alternating-full-groups-of-free-subshifts-force-sft`. Its proof uses freeness
in two places:
- the relator step: trivially acting words have trivial formal cocycles;
- the separation constant `R_1` of Lemma 0: every `x` is separated from `u·x` on `B(R_1)`, for
  `e ≠ u ∈ B(12)`.

**Relator step: repaired under topological freeness.** Step 3 of
`topologically-free-subshift-sft-extension-proof`: a locally constant cocycle with values in
stabilizers, on a topologically free system, is identically `e`.

**Separation: genuinely lost at short stabilizers.**

*Lemma 3.1 (rule 3-cycles cannot be defined at fixed points).* Let `π` be a pattern occurring
at `x_0 ∈ X` with `s·x_0 = x_0` for some `s ≠ e`. Then `x_0 ∈ [π] ∩ s·[π]`, so the blocks
`[π]`, `s·[π]`, `t·[π]` of a rule 3-cycle with shape `{e, s, t}` are not disjoint, and no rule
3-cycle with that shape exists for `π` or for any pattern occurring at `x_0`.

*Lemma 3.2 (no uniform separation on minimal non-free systems).* Let `X` be minimal, and let
`x_0 ∈ X` be fixed by some `u ∈ B(12) ∖ {e}`. Then for every `R_1` and every `x ∈ X` there is
`λ` with `(λ·x)|_{B(R_1)} = (u·λ·x)|_{B(R_1)}`.

*Proof.*
- The orbit of `x` is dense, so some `λ·x` agrees with `x_0` on `B(R_1 + 12)`.
- For `μ ∈ B(R_1)`, `μu ∈ B(R_1 + 12)`. So `(u·λ·x)(μ) = (λ·x)(μu) = x_0(μu) = (u·x_0)(μ) = x_0(μ) = (λ·x)(μ)`. ∎

**Consequences.**
- On a minimal subshift with a point fixed by a short element, the constant `R_1` of Theorem G
  does not exist.
- Detecting an illegal pattern near the fixed-point locus needs rule 3-cycles on patterns of
  unbounded radius, but a finite presentation controls only bounded radius.
- This is the exact break. It is not a proof that such hosts have finitely presented full
  groups.

**Remark (unchecked; not a node).** Suppose no element of `B(12) ∖ {e}` has a fixed point in
`X` (for a suitable finite generating set) and `X` is topologically free. Then compactness gives
`R_1`, and the Theorem G argument appears to go through verbatim. I compared this only with the
proof route's summary, not with Sections 1–4 of
`research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part2.md`, so it is not landed.

**Non-topologically-free subshifts: the extension theorem itself breaks.**
- If `Fix(λ)` has interior for some `λ ≠ e`, a relator can act trivially on `X` while its formal
  cocycle equals `λ` on a clopen set.
- The condition "the relator acts trivially" is then `x ∈ Fix(c_r(x))`. That is a closed global
  condition, not a finite-type condition, so no SFT neighbourhood is produced.

## 4. Census of (S2) after this lane

| Host class | Status | Node |
|---|---|---|
| Equicontinuous actions: rooted-tree boundaries with isotropy (bounded automaton groups), odometers, profinite actions | DEAD: no finitely generated infinite simple subgroup | `equicontinuous-action-full-group-fg-subgroups-are-rf` |
| Non-expansive Cantor systems over `Λ` | REDUCED to subshift factors over the same `Λ`, with the same minimality and invariant measures | `fg-full-group-subgroups-factor-onto-subshift-full-groups` |
| Minimal systems over abelian `Λ`, of any kind | REDUCED to free minimal subshifts over infinite quotients of `Λ`, which is case (S1) | same, item 5 |
| Topologically free subshifts | SFT extension and the (PA) obstruction hold | `topologically-free-subshift-fp-subgroups-extend-to-sft` |
| Compressible groupoids (expanding maps, hosts containing `V`) | DEAD (already on main) | `amenable-full-group-forces-invariant-measure` |
| Minimal non-free subshifts over non-abelian `Λ` with short stabilizers | LIVE: Theorem G breaks (Lemma 3.2) | none |
| Subshifts that are not topologically free | LIVE: the extension theorem breaks | none |
| Non-minimal hosts where `Γ` acts trivially on every minimal subset | LIVE | none |

## 5. Exact gap

A finitely presented infinite simple amenable group in (S2) must live in one of three places:
- **(G1)** a minimal subshift over a non-abelian finitely generated `Λ` that has points with
  nontrivial stabilizers. It is then non-equicontinuous and, by `amenable-full-group-forces-invariant-measure`,
  not compressible if the group realizes moving bisections;
- **(G2)** a subshift that is not topologically free;
- **(G3)** a non-minimal host where the group acts trivially on every minimal subset.

In case (G1) the free-subshift obstructions fail exactly through Lemma 3.2. No candidate group
has been identified in any of the three classes.

## 6. Not done

- No construction of a candidate in (G1)–(G3).
- The Theorem G extension under the no-short-fixed-points hypothesis (Section 3, Remark) is not
  checked against the full proof.
- Sources not re-read here: Juschenko–Nekrashevych–de la Salle; Nekrashevych arXiv:1312.5654.
  They are cited only for context, not as inputs to the landed proofs.
