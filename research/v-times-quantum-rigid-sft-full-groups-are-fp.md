---
rg: 2
id: v-times-quantum-rigid-sft-full-groups-are-fp
kind: claim
title: "P2′: if a minimal free SFT over a finitely presented group is quantum rigid, the full group of V times its transformation groupoid is finitely presented"
distinct_from:
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is P2 over all minimal free SFTs, refuted by golden–silver; this is its corrected form, with quantum rigidity added as a hypothesis.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that is the converse (finite presentation implies quantum rigidity), which is ESTABLISHED; this is the open sufficiency direction.
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that is the ring-side sufficiency, which is ESTABLISHED; this is the group-side analogue.
---

**OPEN.** This is gate G3g (P2′) of `research/artifacts/gq-bh-synthesis-master-route.md`.

**Statement.** Let `Λ` be infinite and finitely presented, and `X ⊆ A^Λ` a nonempty minimal SFT on which
`Λ` acts freely. Suppose `X` is `D`-quantum rigid over every field, for all large `D`. Then
`A(G_V × (Λ ⋉ X)) = F(G_V × (Λ ⋉ X))` is finitely presented.

With `fp-v-times-minimal-action-full-groups-have-type-a-actions`, a proof gives PBH for every subgroup of
`Λ`. Together with gates G1 and G2 it gives the master route.

**What is known.**
- The converse holds (`fp-v-times-subshift-full-groups-force-quantum-rigidity`).
- The ring analogue holds (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`).
- The Boolean-inverse-monoid analogue holds for every SFT, rigid or not
  (`sft-groupoid-boolean-inverse-monoids-are-finitely-presented`).
- Representations built from quantum families cannot decide P2′
  (`quantum-family-representations-are-exhausted-at-rigidity`).

## Attempts

**Attempt 1 (2026-09-18, bh-g3-steinfarley): the Stein–Farley set-up, and where it breaks.**

Proved facts are marked (P); unproved steps are marked (S).

- **(P) The splitting system satisfies the cube property.**
  - Cones are `[u] × [P]_F`, with `u` a finite word and `P` a pattern on a finite set `F ⊂ Λ`
    that occurs in `X`.
  - There are two kinds of elementary split: the `C`-split `[u] → [u0] ⊔ [u1]`, and the
    `X`-split at a site `g ∉ F` into the extensions of `P` to `F ∪ {g}` that occur in `X`.
  - Any two elementary splits of a cone have a common refinement, reached by elementary splits in
    either order: cylinders on `F ∪ {g, g'}`, or `C`-split pieces of `X`-split pieces.
  - So, unlike the unimodular-dissection gate (`rational-projective-full-groups-are-finitely-presented`,
    `unimodular-dissection-operad-has-finite-type`), **P2′ is not a "Li without lcms" problem.**
- **(P) Over amenable `Λ`, the real obstruction is infinite type.**
  - A canonical similarity between cones is a prefix replacement times a translation. So the
    similarity type of `[u] × [P]_F` is the translation class of the set `[P]_F`.
  - If `Λ` is amenable, `X` carries an invariant probability measure, of full support by
    minimality. `X` has no isolated points, so a strictly decreasing chain of cylinders has
    strictly decreasing measures, and no two of them are translates. So there are infinitely many
    types. This covers every `Z^d` shift, Labbé's included.
  - Hence the Stein–Farley complex `𝔓` of labelled cone partitions is contractible (partitions are
    directed under common refinement) but not cocompact at any height. Brown's criterion does not
    apply directly.
- **(P) Over non-amenable `Λ`, finite type is not excluded.** A cylinder can equal a translate of a
  strictly larger cylinder (`[λQ]_(λF') ⊊ [Q]_(F')`) exactly when a pattern forces a pattern on a
  translated domain. That is compression realized by `Λ` itself.
  - **New lead:** call `X` *translation-finitely coded* if finitely many cylinder types exist such
    that every cylinder is a finite disjoint union of translates of them, compatibly with
    elementary splits.
  - For such `X`, the standard Stein–Farley argument (cocompact heights, finite stabilizers) applies
    with finitely many colours. The problem is then a finite-type, cube-property complex, like
    Brin–Thompson `nV` with branching given by extension sets.
  - The paradoxical subshifts of `f2-groups-have-paradoxical-free-minimal-subshifts` are the natural
    candidates. This matches design rule 3 ("never rely on amenability") and gives it a group-side
    reason.
  - This is the opposite of the dissection gate, which is finite type (candidate) but non-LCM.
    **One theorem type will not serve both** unless it handles both defects.
- **(S) The domain filtration reduces P2′ to one connectivity statement.**
  - Let `𝔓^(N)` be the subcomplex spanned by partitions into cones whose domain lies in a
    translate of `B_N`. It is `F(T)`-invariant, has finitely many cell types at each height, and has
    finite cell stabilizers.
  - Brown's criterion with the height Morse function then gives `F(T)` finitely presented as soon
    as, for one `N`:
    - (A_N) `𝔓^(N)` is simply connected;
    - (B_N) descending links in `𝔓^(N)` are simply connected above some height.
  - **(B_N) should hold for every SFT.** For large height one piece type repeats many times, and
    `C`-merges among equal types form a join containing a large matching complex. The claim that
    `X`-merges do not destroy this connectivity is not checked.
  - **(A_N) is the rigidity step.**
    - `𝔓 = ⋃_N 𝔓^(N)` is contractible. So every loop in `𝔓^(N)` bounds in some `𝔓^(N')`, and
      (A_N) asks for a uniform `N`.
    - The necessity theorem shows that walls, and every noncommuting quantum family, produce loops
      of `𝔓^(N)` that do not bound in `𝔓^(N)` for any `N` (heuristic reading of its representation).
    - `quantum-family-representations-are-exhausted-at-rigidity` shows that quantum rigidity is
      exactly the linear shadow of (A_N).
- **What would close (A_N).** A local confluence principle for domain reductions.
  - A cone with large domain `F` sits inside a family of siblings only through the extension sets
    `Ext(P|_(F \ g), g)`.
  - A null-homotopy of a loop in `𝔓^(N')` has to be pushed into `𝔓^(N)` by replacing each
    large-domain cone by its sibling family, where the sibling families at different far-apart sites
    are exchanged in the same way that (Q2) propagates commutation.
  - The ring-side proof does this propagation algebraically, inside the universal algebra. A
    group-side proof must do it on cone partitions, which is where the extra non-linear content of
    P2′ sits.
- **The Labbé test case.** Every step above applies to Labbé's shift over `Z^2`. There, quantum
  rigidity itself is still open (`labbe-crossed-product-fp-via-wall-rigidity`: `J_D = 0`), so P2′ at
  Labbé needs both that gate and (A_N). I found no way to test (A_N) at Labbé independently of
  `J_D = 0`.

**Lesson for general BH.**
- **Finite type always holds at the classical level.** The Boolean dynamics of every SFT is finitely
  presented.
- **The whole difficulty is transport of commutation between far-apart supports.** Rings do this
  exactly under quantum rigidity; groups must do it on cone partitions.
- **Consequence for the group-side fp theorem.** For SFT hosts it is not a non-LCM problem.
  - Over amenable `Λ` it must be an infinite-type Stein–Farley theorem. Its content is a uniform
    simple connectivity (A_N) of bounded-domain partition complexes, a group-level
    "local-to-global" statement whose linearization is quantum rigidity.
  - Over non-amenable `Λ`, translation-finitely coded SFTs would restore finite type. The needed
    compression then comes from `Λ`, not from `V`. This is a concrete design target for gates G1
    and G2 (bh-g2-f2f2).

**Attempt 2 (2026-09-18, bh-g3-tfc): the translation-finitely-coded lead is dead for free `X`.**
See `free-sft-hosts-admit-no-finite-type-coding`. A finite graph-directed (Garside) coding of any
ample groupoid produces a contracting loop. In `G_V × (Λ ⋉ X)`, the germ of a contracting loop at
its limit point has a `Λ`-label `λ ≠ 1` with an attracting fixed point in `X`. So:
- For free `X`, no finite-type Stein–Farley, Li, Witzel or Skipper–Witzel–Zaremsky argument exists,
  whatever `Λ` is. Any proof of this node must be infinite type: Attempt 1's non-cocompact
  filtration `𝔓^{(N)}` with (A_N).
- Even without a Garside family, finitely many translation cone types force `X` to have no infinite
  factor with an invariant probability measure. This extends Attempt 1's amenable-`Λ` obstruction
  to every invariant-measure factor.
- The finite-type version of the problem is E3′
  (`v-times-rigid-topologically-free-sft-full-groups-are-fp`). There, isotropy at attracting fixed
  points of non-central elements is required, not merely allowed.

**Lesson for general BH (Attempt 2).** Finitely coded compression is contraction, and contraction
has fixed points. So a free host and a finite-type P2′ exclude each other. The master route either
invents an infinite-type Brown criterion for free `X`, or works with topologically free `X` (E3′)
and inherits Li's theorem.
