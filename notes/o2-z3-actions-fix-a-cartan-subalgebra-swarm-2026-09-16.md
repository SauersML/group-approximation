# o2-z3-actions-fix-a-cartan-subalgebra --- swarm pass, 2026-09-16

Lock held on `o2-z3-actions-fix-a-cartan-subalgebra` for this pass. Nothing
committed.

## 0. Verdict

- **The target is not resolved, and was not expected to be.** Through
  `barlak-li-p-half-iff-zp-actions-fix-cartan` (Barlak--Li II Theorem 4.16 at
  `p = 3`) it is equivalent to `uct-for-three-infinity-absorbing-nuclear-algebras`,
  the `3`-local half of Problem II.
- **One sound, elementary contribution** (no priority claim). It closes the
  gap "Item 5 is not proved for `p = 3`" in
  `no-masa-of-o2-is-normalized-by-fixed-point-unitaries`, and it
  generalizes that item:
  - new claim `finite-abelian-actions-have-invariant-masas`;
  - direct-proof route `finite-abelian-actions-have-invariant-masas-proof`
    (`requires: []`).

  For every action of a finite abelian group, a maximal invariant abelian
  C\*-subalgebra is a masa. Invariant masas therefore exist, and any invariant
  abelian subalgebra, or any masa of the fixed-point algebra, extends to one.
  The abelian hypothesis is sharp: an explicit `A_4`-action on `M_2` has no
  invariant masa.
- **Consequence for the target.** For every `α ∈ Aut(O_2)` with `α^3 = id`,
  the maximality part of "invariant Cartan subalgebra" is free. The target is
  exactly the existence of an `α`-invariant masa that is regular and carries a
  faithful conditional expectation. This is a clarification of where the
  difficulty sits, not progress on the UCT.

## 1. Setup and orientation

- **Target.** Every outer strongly approximately inner (SAI) `Z_3`-action on
  `O_2` leaves some Cartan subalgebra invariant. The target node has
  `distinct_from` entries naming the `p = 2` twin and the `3`-half of the UCT,
  and it cites the artifacts `stw-uct-reduction-map-2026-09-11.md` and
  `stw-uct-per-prime-cartan-2026-09-12.md`.
- **Landed context read this pass** (statuses from `bin/cairn why`):
  - `barlak-li-p-half-iff-zp-actions-fix-cartan`: ESTABLISHED via citation.
    The `p`-half of the UCT is equivalent to order-`p` actions fixing Cartan
    subalgebras.
  - `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent`: ESTABLISHED. Cartan-fixing
    at `p` is equivalent to the UCT ascending along Rokhlin `Z_p`-actions
    whose crossed product is `O_2`.
  - `bootstrap-class-zp-actions-on-o2-fix-a-cartan`: ESTABLISHED.
    Bootstrap-class actions fix a Cartan subalgebra.
  - `cartan-respecting-o2-automorphisms-give-uct-crossed-products`:
    ESTABLISHED.
  - `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`,
    `zp-o2-contractible-crossed-product-only-coboundaries` and
    `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`: ESTABLISHED.
    They reduce detection at `p` to Rokhlin rigidity for actions with
    contractible crossed product.
  - `no-masa-of-o2-is-normalized-by-fixed-point-unitaries`: ESTABLISHED.
    - Items 1–4 hold for every prime.
    - Item 5 (maximal invariant abelian implies masa) was proved only for
      `α^2 = id`. Its proof adjoins the self-adjoint eigenparts
      `(y ± α(y))/2`, which has no analogue at `p = 3`.
  - `cartan-invariant-zp-actions-on-o2-have-trivial-action-element`: OPEN.
- **Twin pass.** `notes/o2-z2-actions-fix-a-cartan-subalgebra-swarm-2026-09-16.md`
  records dead ends 1–11 at `p = 2`. They are Zorn masas, pointwise-fixed
  cocycles, implementing unitaries normalizing a masa, Rokhlin dimension ≤ 1
  gluing, trivial-K repackaging, cocycle perturbation, tensor square,
  `α ⊗ id_{O_2}`, finite-stage approximate conjugacy, product-type actions and
  induced involutions. Their recorded failure points are no control of
  normalizers, no Rokhlin property, and no coherent choice along
  approximations. I did not re-check each of them at `p = 3`.
- **Duplicate search.** I ran `bin/cairn search "invariant masa"`,
  `bin/cairn search "maximal abelian"`, `bin/cairn search "spectral subspace"`
  and `bin/cairn search --similar` on the statement. The only related node is
  `no-masa-of-o2-is-normalized-by-fixed-point-unitaries` (item 5, `p = 2`),
  now named in `distinct_from`.

## 2. What was proven

**Node.** `research/finite-abelian-actions-have-invariant-masas.md`, with
route `research/finite-abelian-actions-have-invariant-masas-proof.md`
(`requires: []`). `check.sh` exit 0; the check reports "unlocked by this
change: established".

**Statement.** Let `G` be finite abelian, acting on a C\*-algebra `A`.
1. Every maximal element `D` among the invariant abelian C\*-subalgebras
   satisfies `D' ∩ A = D`, so `D` is a masa.
2. Every invariant abelian C\*-subalgebra lies in an invariant masa. Every
   masa `D_0` of `A^G` is `D ∩ A^G` for some invariant masa `D`.
3. `G = ⟨Ad X, Ad Z, Ad U⟩ ≅ A_4` acting on `M_2`, with
   `U = (1 − iX − iY − iZ)/2`, has only `{0}` and `C1` as invariant abelian
   C\*-subalgebras.

**Proof of item 1** (the new step is (c)). Put `B = D' ∩ A`.
- (a) `B` is an invariant C\*-subalgebra with `D ⊆ Z(B)`.
- (b) `B^G ⊆ D`. A fixed self-adjoint `y ∈ B` generates, together with `D`,
  an invariant abelian algebra, so maximality puts `y` in `D`.
- (c) Let `b ∈ B` with `α_g(b) = χ(g) b`. Then `c = b*b` and `d = bb*` are
  fixed, so they lie in `D ⊆ Z(B)`. Hence `c^2 = b*db = dc` and
  `d^2 = bcb* = cd`, so `(c − d)^2 = 0`, `c = d`, and `b` is normal.
- (d) `C*(D ∪ {b, b*})` is abelian and invariant, so `b ∈ D`.
- (e) `B` is the sum of its spectral components
  `E_χ(B) = |G|^{-1} Σ_g \overline{χ(g)} α_g(B)`, so `B = D`.

**Why item 5 of the older node did not extend.** At `p = 2`, the eigenparts of
a self-adjoint `y ∈ B` are self-adjoint, and they can be adjoined directly.
At `p = 3` the eigenparts `y_χ = |G|^{-1} Σ_k \overline{χ(k)} α^k(y)` are not
self-adjoint. `Re y_χ` and `Im y_χ` are no longer eigenvectors, and a priori
they need not commute, so neither adjoining `y_χ` nor adjoining its real and
imaginary parts is justified. The fix is to first absorb `B^G` into `D`, which
makes every eigenvector of `B` normal.

**Sharpness.** The `A_4` example shows that finiteness of `G` alone gives
nothing; the abelian structure is used through characters. It is the minimal
kind of counterexample on `M_2`: finite dihedral and cyclic images in
`SO(3) = Aut(M_2)` preserve an axis, hence a masa. This sentence is standard
geometry of finite rotation groups, stated here without proof and not part of
the node.

**Honest assessment.** The result is folklore-level, and I found no source
stating it (Section 5), so I claim no priority. It is complete and
unconditional. Its leverage on the target is modest: it removes maximality
from the list of possible obstructions and supplies a clean extension lemma,
but regularity and conditional expectations are untouched.

## 3. Approaches tried and where each dies

**3.1 Adjoining eigenparts, as at `p = 2` (item 5 at `p = 3`).** This dies as
first attempted, because the eigenparts `y_χ` of a self-adjoint `y` commuting
with `D` need not be normal. It is repaired by step (c) of the new route and
now SUCCEEDS.
- An intermediate attempt worked "fibrewise" over the spectrum of `D`, using
  `D ⊆ Z(B)`.
- It was not completed. The two-line identity `c^2 = dc`, `d^2 = cd` superseded
  it.

**3.2 Invariant masa to invariant Cartan subalgebra: regularity.** Zorn
extensions come with no normalizers, so this dies at regularity.
- *Extending a Cartan subalgebra of the fixed-point algebra.* Take a Cartan
  subalgebra `D_0` of `O_2^α` and extend it to an invariant masa `D` with
  `D ∩ O_2^α = D_0` (item 2).
  - A normalizer `u ∈ N_{O_2^α}(D_0)` maps `D` to `uDu*`. That is again an
    `α`-invariant masa with fixed part `D_0`.
  - Nothing forces `uDu* = D`, so `u` need not normalize `D`. Moreover, the
    elements of `N(D)` in the nontrivial spectral subspaces of `O_2` are not
    produced at all.
- *The input is not free anyway.* `O_2^α` is separable and nuclear, so a
  Cartan subalgebra of it already forces the UCT for `O_2^α`
  (`barlak-li-cartan-subalgebras-force-uct`). That is the kind of conclusion
  being sought, so it cannot be assumed.

**3.3 Reducing to the fixed-point algebra: the fixed part of an invariant
Cartan subalgebra.** This dies at a finite-dimensional counterexample.
- *The example.* In `M_3`, let `α = Ad(clock)` with
  `clock = diag(1, ω, ω^2)`, and `D = C*(shift)`.
  - `D` is a Cartan subalgebra: it is a masa normalized by `clock`, the
    products `clock^j shift^k` span `M_3`, and it carries the trace-preserving
    expectation.
  - `D` is `α`-invariant, because `clock · shift · clock* ∈ C·shift`.
  - `D ∩ M_3^α = C1`, while `M_3^α` is the diagonal algebra. So `D^α` is not
    even a masa of the fixed-point algebra.
- *Consequence.* Invariant Cartan subalgebras are not controlled by
  subalgebras of `O_2^α`. The relation in item 2 runs only from masas of `A^G`
  to invariant masas, not back.

**3.4 Intersecting or joining the orbit of a Cartan subalgebra.** Let `D` be a
Cartan subalgebra of `O_2`. This dies at the same place as 3.2.
- *Intersecting.* `D ∩ α(D) ∩ α^2(D)` is invariant and abelian. Item 2 extends
  it to an invariant masa, with no regularity.
- *Joining.* `C*(D ∪ α(D))` is abelian only if `α(D)` commutes with `D`. For
  masas that means `α(D) ⊆ D' ∩ O_2 = D`, i.e. `D` was already invariant.

**3.5 Spectral normalizers.**
- *The idea.* Write `O_2 = ⊕_{χ ∈ Ẑ_3} (O_2)_χ` and `D = ⊕_χ D_χ` for an
  invariant masa `D`. Regularity of `D` would follow if each `(O_2)_χ` were
  spanned by normalizers of `D`.
- *Rokhlin actions.* For these, approximate eigen-unitaries exist in
  central sequences, built from Rokhlin projections.
- *Where it dies.* The actions not yet handled lie outside the equivariant
  bootstrap class, by `bootstrap-class-zp-actions-on-o2-fix-a-cartan`. A
  Rokhlin action is `KK^G`-contractible
  (`outer-actions-on-o2-kk-g-contractible-iff-rokhlin`), and so lies in that
  class. Hence the remaining actions are not Rokhlin. For them, no supply of
  spectral normalizers is known to me. This is the Rokhlin-rigidity wall
  again.

**3.6 Nonabelian enlargements.** One could embed `α` into a larger group
action, e.g. adding an order-two automorphism that inverts `α`, and look for
a masa invariant under the whole group.
- Item 3 shows that no group-independent Zorn argument can work for
  nonabelian groups: `A_4` on `M_2` has no invariant masa at all. So such an
  enlargement must bring its own masa.
- Not pursued further.

**3.7 Trivial-K repackaging at `p = 3`.** A sketch suggests that the target
is equivalent to: every outer SAI `Z_3`-action on `O_2` with contractible
crossed product is Rokhlin. The sketch uses a mapping-cone trick to kill
K-theory, the form `β = id_Ã ⊗ γ` from Barlak--Li II Theorem 4.16, Künneth
with `M_{3^∞}`, Kirchberg--Phillips, Izumi's duality and uniqueness for Rokhlin
actions, Takai duality, and `F_∞(A ⊗ M_3) = F_∞(A)`.
- *Status of the sketch.* I did not check it, and I add nothing to the graph
  for it.
- *What is already landed.* The ESTABLISHED nodes
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`,
  `zp-o2-contractible-crossed-product-only-coboundaries` and
  `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences` cover the same
  ground at every prime.
- *Where it dies.* At Rokhlin rigidity. No new invariant for these actions
  was found.

**3.8 Gauge-type and quasi-free order-three automorphisms.**
- *The example.* `s_1 ↦ s_1`, `s_2 ↦ ω s_2`, i.e. `λ_v` with
  `v = s_1 s_1* + ω s_2 s_2*` in the canonical diagonal `D_2`. It fixes `D_2`
  pointwise, since `s_μ s_μ*` picks up `ω^k \overline{ω^k} = 1`. It is covered
  by `cartan-respecting-o2-automorphisms-give-uct-crossed-products`.
- *Where it dies.* Such examples fix a Cartan subalgebra by construction, so
  they say nothing about exotic actions.

## 4. Computation

`experiments/finite-abelian-invariant-masas-2026-09-16/invariant_masa_check.py`
is a single-threaded numpy script with a fixed seed. It runs in seconds. Its
output (2026-09-16):

```text
Part A: A_4 group order 12 ; only scalar fixed symmetric matrices: OK
Part B: Z3 generic Ad u, n=3 | dim D = 3 | steps 2 | normality checks 0
Part B: Z3 generic Ad u, n=4 | dim D = 4 | steps 2 | normality checks 0
Part B: Z3 generic Ad u, n=5 | dim D = 5 | steps 2 | normality checks 0
Part B: Z3 generic Ad u, n=6 | dim D = 6 | steps 2 | normality checks 0
Part B: Z3xZ3 clock/shift, n=3 | dim D = 3 | steps 2 | normality checks 1
Part B: Z3xZ3 twisted, n=6 | dim D = 6 | steps 3 | normality checks 1
Part B: Z2xZ4, n=4 | dim D = 4 | steps 3 | normality checks 1
ALL CHECKS PASSED
```

- **Part A** checks the identities (a)–(c) of item 3 and the group order `12`.
  The only symmetric `3 × 3` matrices fixed by the `SO(3)` image are scalars,
  so there is no invariant axis and hence no invariant rank-one pair.
- **Part B** runs the greedy form of item 1 on matrix algebras, following
  steps (b)–(e):
  - adjoin fixed self-adjoint elements of `B = D'` until `B^G ⊆ D`;
  - then adjoin spectral elements, asserting that each is normal;
  - stop when `B = D`; the result is an invariant masa.
- **Coverage of step (c).** For a single inner `Z_3`-action on `M_n`, the
  fixed-point algebra contains a masa, so step (c) is never exercised
  ("normality checks 0"). The `Z_3 × Z_3` and `Z_2 × Z_4` cases do exercise
  it.
- **Status.** This is a sanity check only. The proof in the route is
  complete without it.

## 5. Literature gate (2026-09-16)

Fetched this session with WebFetch on `arxiv.org/abs/...` and `arxiv.org/search`
(abstract-page level). Earlier arXiv API attempts this session hit a timeout
and "Rate exceeded".

**Primary sources, 2025–2026.**
- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902. v1 2025-06-12, v2 2026-05-08.
  - The abstract page does not itself state the status of Problem II.
  - That it is listed as open comes from the repository's earlier source check
    (`stw99-problem-ii-nuclear-uct`), not re-read this pass.
- F. Komura, *Cartan-preserving \*-automorphism groups: realization and
  obstructions for compact abelian groups*, arXiv:2607.18844. v1 2026-07-21.
  - It realizes compact abelian groups inside the automorphism groups fixing
    a Cartan subalgebra of certain Kirchberg algebras, and gives obstructions
    for expansive groupoids.
  - The abstract says nothing about finite cyclic actions on `O_2`, invariant
    masas or the UCT problem. Full text not read.
- S. Evington, P. Sibbel, *C\*-diagonals with Cantor spectrum in Cuntz
  algebras*, arXiv:2506.22163. v1 2025-06-27, v2 2026-02-23.
  - It shows that Cuntz algebras contain C\*-diagonals with Cantor spectrum,
    with groupoid models.
  - The abstract does not mention group actions. No bearing on invariance.
- A. Buss, J. Kranz, *On groupoids beyond partial actions, inner amenability,
  and models for Kirchberg algebras*, arXiv:2604.17921. v1 2026-04-20, v2
  2026-04-29.
  - It gives ample transformation-groupoid models for unital UCT Kirchberg
    algebras.
  - These are models inside the UCT class, so there is no bearing on non-UCT
    candidates.
- S. Geffen, S. Hua, J. Kranz, *Dynamical comparison for local
  homeomorphisms*, arXiv:2608.13000. v1 2026-08-13.
  - It establishes dynamical comparison for Deaconu–Renault groupoids; their
    C\*-algebras are UCT Kirchberg algebras.
  - Constructions inside the UCT class. No bearing.

**Searches.**
- arXiv full-text-field search "invariant masa finite group action
  C\*-algebra": no results.
- arXiv abstract search "Cartan subalgebra invariant group action", newest
  first: 19 hits.
  - None concerns finite group actions on `O_2`, invariant masas for finite
    abelian actions, or the UCT problem.
  - Tangential only: arXiv:1812.08478 (free Araki–Woods factors),
    arXiv:math/0408296 (nonconjugate Cartan subalgebras from minimal
    diffeomorphisms), arXiv:math/0112227 (masas of the hyperfinite factor).

**Not re-fetched** (used through repository nodes and artifacts only): Barlak--Li,
arXiv:1511.02697 and arXiv:1704.04939v2; Barlak--Szabó; Izumi; Gardella. The
theorem numbers quoted (BL II 4.16) are as recorded in the repository.

**Outcome of the gate.**
- No 2024–2026 source found resolves the target or the UCT problem, or gives
  invariant Cartan subalgebras for arbitrary outer SAI `Z_3`-actions on
  `O_2`.
- No source found states the invariant-masa lemma for finite abelian groups.
  It is plausibly folklore, and I claim no priority.

## 6. Weakest steps and what remains open

**Weakest steps, for a referee.**
- *Relevance, not correctness.* The node is complete and elementary, but it
  moves the target only by isolating regularity and conditional expectations
  as the whole difficulty.
- *Load-bearing algebra.* Step (c) of the route: `c = b*b` and `d = bb*` lie
  in `B`, because `B` is a \*-algebra containing `b`. They are fixed because
  `|χ(g)| = 1`. So they lie in `B^G ⊆ D ⊆ Z(B)`, and `c^2 = dc`, `d^2 = cd`
  force `(c − d)^2 = 0`.
- *Item 3, step (b).* The symbolic relabelling argument for `UYU* = Z` and
  `UZU* = X`. The script confirms these numerically.

**Open.**
- The target itself.
- Does every outer SAI `Z_3`-action on `O_2` admit an invariant masa with a
  faithful conditional expectation, ignoring regularity? I know no argument
  either way.
- **Extension to compact abelian groups.**
  - Steps (a)–(d) of the route use only `|χ(g)| = 1`.
  - Step (e) would need the standard density of the span of spectral
    subspaces, via an approximate unit of trigonometric polynomials in
    `L^1(G)`.
  - This extension is not written out and not claimed in the node.
- Whether some invariant masa is canonical in a weaker sense than items 3–4 of
  `no-masa-of-o2-is-normalized-by-fixed-point-unitaries` rule out, for
  instance equivariant only under `U(O_2^α)`-conjugation up to approximate
  unitary equivalence. Not investigated.

**Files written this pass.**
- `research/finite-abelian-actions-have-invariant-masas.md` (claim)
- `research/finite-abelian-actions-have-invariant-masas-proof.md` (route,
  `requires: []`)
- `experiments/finite-abelian-invariant-masas-2026-09-16/invariant_masa_check.py`
- this note

No existing node was edited. Nothing committed.

## Referee (2026-09-16)

**What I checked.**
- *Item 1, line by line.* (P1)–(P3), including the character substitution in
  the eigen-equation and the orthogonality decomposition. (a) invariance of
  `B = D' ∩ A`. (b) `B^G ⊆ D`: the set `D ∪ {y}` is `*`-closed, pairwise
  commuting and mapped into itself, so (P2) and maximality apply; no
  unitality is needed. (c) the load-bearing identities: `c = b*b` and
  `d = bb*` are fixed because `|χ(g)| = 1`, lie in `B^G ⊆ D ⊆ Z(B)`, and
  `c^2 = b*db = dc`, `d^2 = bcb* = cd` give `(c − d)^2 = 0`. (d)–(f). No
  hidden hypothesis: unitality, separability, simplicity and outerness are
  never used, and the non-unital case is handled correctly (`D' ∩ A = D`
  directly gives maximality).
- *Item 2.* Zorn over invariant abelian subalgebras containing `C_0`, and
  the fixed-point-algebra extension `D ∩ A^G = D_0`. Correct.
- *Item 3.* Recomputed by hand `N^2 = 3`, unitarity of `U`, `U^3 = −1`,
  `UX = YU = (X + Y − Z − i)/2`, the cyclic relabelling (it preserves all
  Pauli relations and fixes `N`), the group of order `12`, the classification
  of abelian C\*-subalgebras of `M_2`, and the coefficient conditions in
  (e)–(f). Correct.
- *Script.* Re-ran `invariant_masa_check.py` single-threaded; output matches
  Section 4 exactly, `ALL CHECKS PASSED`.
- *p = 2 predecessor.* Read item 5 of
  `no-masa-of-o2-is-normalized-by-fixed-point-unitaries-proof`: it indeed
  uses self-adjoint eigenparts `(y ± α(y))/2` and only covers `α^2 = id`, so
  the new node is a genuine generalization, not a duplicate.
- *Duplicates.* `bin/cairn search --similar` and `bin/cairn search "invariant
  masa"`: only the p = 2 node, already in `distinct_from`.
- *Literature spot-check.* Fetched arXiv abstract pages of 2607.18844
  (Komura, v1 2026-07-21) and 2506.22163 (Evington–Sibbel, v1 2025-06-27,
  v2 2026-02-23); titles, authors, dates and content match the solver's
  descriptions. A further web search could not be run (session search budget
  exhausted), so the folklore/no-priority assessment stands as the solver's.
- *Check.* `check.sh` exit 0; the claim is ESTABLISHED via the route.

**What I changed.**
- Claim, "What an argument must use": item 3 is an `M_2` example, so it only
  rules out constructions valid for all finite group actions on all
  C\*-algebras. The original sentence ("any approach to the target must use
  that `Z_3` is abelian") overstated this; I added that an argument could
  instead use features specific to `O_2` and the action, and that invariant
  masas for nonabelian finite actions on `O_2` are not addressed.
- Route, item 3(c): the identification `G ≅ A_4` was asserted without an
  explicit isomorphism although the claim statement names `A_4`. I added the
  explicit map to `V_4 ⋊ ⟨(123)⟩` and checked the conjugation action matches.
- Section 3.6 of this note has the same overstatement in milder form ("no
  group-independent Zorn argument"), which is accurate as worded; left as is.

**Verdict.** Sound and honestly labelled. The node is elementary (plausibly
folklore, no priority claimed) and leaves the target OPEN: regularity and a
faithful conditional expectation for some invariant masa are untouched.
Landed with the two small fixes above.
