# Zaremsky Problem 1.18 (properly nested BNSR invariants): swarm lane, 2026-09-16

## Setup

- **Root.** `zaremsky-1-18-properly-nested-bnsr-invariants`: is there a group `G` of
  type `F_∞` with `Σ^1(G) ⊋ Σ^2(G) ⊋ ⋯` all properly nested?
- **Locked hole.** `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`:
  every `F_∞` group with no finite classifying space has some `m ≥ 1` with
  `Σ^m(G) = Σ^{m+1}(G)`.
  - It is the open prerequisite of
    `every-f-infinity-group-non-proper-bnsr-by-type-f-dichotomy`, the no-side
    route. The type F case is established.
- **Notation.** Depth `δ(χ) = min{m : [χ] ∉ Σ^m(G)}`, with values in
  `{1, 2, …, ∞}`. A yes-group is one whose chain is properly nested at every
  step.

## Literature gate (2026-09-16)

- **Problem list.** M. C. B. Zaremsky, "Some open problems", dated July 12,
  2026 (PDF text saved in the scratchpad). Item 18 of §1 is still unannotated.
  Other items do carry notes such as "[Actually this isn't open, ...]", so the
  missing note is informative.
- **arXiv API, `all:BNSR`, max 25, newest first.**
  - 2606.02978v1 (link groups, 2-knot groups) and 2605.28595v2 (twisted
    homology jump loci as upper bounds for Σ). Neither abstract addresses
    Problem 1.18.
  - 2505.18826v3 (Ershov–Zaremsky, McCool groups) is also listed; v2 was read.
- **arXiv API, `au:Kropholler` and `au:Nucinkis AND ti:amenable`.** These
  returned 1805.10052v2 (Kropholler–Martínez-Pérez) and 1104.0588v2. They did
  not return the Kropholler–Martínez-Pérez–Nucinkis 2009 Crelle paper. It seems
  not to be on arXiv and was not read.
- **Conclusion.** No resolution of 1.18 was found.

### Verified quotes used (LaTeX sources read 2026-09-16)

- **Ershov–Zaremsky, arXiv:2505.18826v2, §2.1.**
  - Setup with a classifying space with finite `n`-skeleton and a height
    function `h_χ(g.x) = χ(g) + h_χ(x)`.
  - Definition of `Σ^m` via essential `(m−1)`-connectivity of `X^{h_χ≥t}`.
  - "This definition is independent of the choices of X and h_χ; see for
    example [bieri03, Theorem 12.1]" (Bieri–Geoghegan, not re-read).
  - Remark (a): any `(n−1)`-connected CW complex with a proper, cocompact,
    cellular action may be used.
- **Zaremsky, arXiv:1507.08597v1.**
  - Definition 1.1 and its well-definedness sentence.
  - §3: "Since P_n has finite index in B_n, its action on X is cocompact, and
    hence can be used to “reveal” the BNSR-invariants of P_n."
  - Corollary 1.6 "Center survives".
- **Hughes–Kielak, arXiv:2302.03346v2, §1.**
  - Definitions of `F_n`, `F_∞`, `F`, VF.
  - "by [KrophollerMartinezPerezNucinkis2009, Theorem 1.1] an elementary
    amenable group of type F_∞ is type VF", with the bibliography entry (J.
    Reine Angew. Math. 637 (2009) 49–62).
- **Kropholler–Martínez-Pérez, arXiv:1805.10052v2**, subsection "Cohomological
  Dimension and Constructible Groups". Kropholler's work "led to a proof that
  elementary amenable groups of type FP_∞ over Z are constructible [K2] ...".
- **Januszkiewicz–Kropholler–Leary, arXiv:0908.3669v1, §1.** Thompson's `F` is
  of type `FP_∞` "and yet having infinite cohomological dimension and so
  failing the key finiteness theorem for HF-groups of type FP∞ established in
  [k-fpinfty]". The exact statement of that theorem was **not verified**.

## What was proven (new nodes)

1. **`bnsr-invariants-are-detected-on-finite-index-subgroups`**, with direct
   proof route `-proof` (`requires: []`). The claim: let `H ≤ G` have finite
   index and `G` be of type `F_n`.
   - `H` is of type `F_n`.
   - `res: S(G) → S(H)` is injective.
   - `[χ] ∈ Σ^m(G) ⇔ [χ|_H] ∈ Σ^m(H)` for `m ≤ n`.

   The proof:
   - `K̃/H` is a `K(H,1)` with finite `n`-skeleton and the same universal
     cover.
   - Each `g ∈ G` has a power `g^r ∈ H` with `1 ≤ r ≤ [G:H]`, by pigeonhole.
   - A `G`-height function is an `H`-height function, and the filtration
     depends only on `(X, h)`. Independence of choices then closes the proof.

   Consequences:
   - A proper drop passes to finite-index subgroups.
   - Stabilization passes up to finite-index overgroups.
   - Consistency check: `P_n ≤ B_n`, via "Center survives".
2. **`virtually-finite-cd-f-infinity-groups-have-stable-bnsr`**, with route
   `virtually-finite-cd-stable-bnsr-via-finite-index-detection`. The claim: if
   `G` is `F_∞` and some finite-index `H` has `cd H = d < ∞`, then
   `Σ^m(G) = Σ^{max(d,2)}(G)` for `m ≥ max(d,2)`.
   - The route uses item 1 and the established
     `bnsr-invariants-stabilize-at-cohomological-dimension`.
   - This covers groups with torsion that are not known to have cocompact
     finite-dimensional proper models.
3. **`elementary-amenable-f-infinity-groups-are-type-vf`**, with citation route
   `-citation` (`requires: []`). This is a secondary import of KMPN 2009,
   Theorem 1.1, as quoted by Hughes–Kielak.
4. **`elementary-amenable-f-infinity-groups-have-stable-bnsr`**, with route
   `elementary-amenable-stable-bnsr-via-type-vf`.
   - A finite `K(H,1)` of dimension `d` gives a free resolution of length `d`,
     so `cd H ≤ d`. Then apply item 2.
   - So no elementary amenable group, in particular no soluble group, answers
     1.18 affirmatively.
5. **Reduction of the locked hole.** Route
   `non-type-f-non-proper-bnsr-by-virtual-cd-dichotomy` splits by whether some
   finite-index subgroup has finite `cd`.
   - The first case is item 2.
   - The second case is the new hole
     **`f-infinity-without-finite-vcd-non-proper-bnsr-inclusion`**: `F_∞` groups
     all of whose finite-index subgroups have infinite `cd`. It has an
     `## Attempts` section.
   - The new hole is strictly smaller in the sense that it excludes VF groups
     and every hypothetical `F_∞` group of finite `cd` that is not of type F.
   - Thompson's `F` is still in it, since `Z^n ≤ F` for all `n`.

## New necessary conditions for an affirmative answer

These are recorded here and in the nodes; the yes-hole
`f-infinity-group-with-properly-nested-bnsr-invariants` was not edited. A
yes-group `G` must satisfy all of the following:

- every finite-index subgroup of `G` has infinite cohomological dimension;
- `G` is not elementary amenable; if `G` is amenable, it answers Problem 1.12
  ("Find an amenable, non-elementary amenable group of type F_∞");
- every finite-index subgroup of `G` is again a yes-group.

## Remarks (not written as nodes)

- **Finite normal subgroups.** Let `N ◁ G` be finite, with `G` and `G/N` both
  of type `F_n`.
  - Every character of `G` vanishes on `N`, since `R` is torsion-free. So
    `S(G) ≅ S(G/N)`.
  - Take `Y` to be the `n`-skeleton of the universal cover of a `K(G/N,1)` with
    finite `n`-skeleton. `G` acts on `Y` through `G/N`, cellularly and
    cocompactly, with cell stabilizers equal to `N`, so properly.
  - By Remark (a) of 2505.18826v2, `Y` is admissible for `G`. The same height
    function then works for both groups, so `Σ^m(G) ≅ Σ^m(G/N)` for `m ≤ n`.
  - This relies on the proper-action version of the definition (Zaremsky,
    Definition 1.1) and on its independence of choices. It is not needed by
    any node, so no node was written.
- **1.18 versus 1.13.** A yes to 1.18 does not by itself give a no to 1.13
  (openness of `Σ^∞`).
  - Openness of every `Σ^m` means `δ` is lower semicontinuous:
    `δ(χ) ≤ liminf δ(χ_k)`.
  - Characters of depths `2, 3, 4, …` can therefore accumulate at a character
    of finite depth without creating a non-open `Σ^∞`.
  - Conversely, `non-open-sigma-infinity-needs-unbounded-sigma-depth` says a
    no to 1.13 needs unbounded finite depths but not all of them.
- **What finite index cannot do.** Restriction transports drops down and
  stability up. It cannot turn a drop in `H` into a drop in `G`, because a
  class in `Σ^m(H) \ Σ^{m+1}(H)` need not lie in the image of `res`. For
  example, for `n ≥ 3`, `S(P_n)` is a sphere of dimension `n(n−1)/2 − 1`,
  while `S(B_n)` is two points. So
  passing to finite-index overgroups cannot build a yes-group.
- **Relation to part 2 §5.1.** Item 3 of the finite-index claim is the general
  "finite-index transfer" asked for in part 2 §5.1 of
  `research/artifacts/zp-properly-nested-bnsr-2026-09-13-part2.md`, in the
  form: membership of `[χ]` is read off from `[χ|_H]`. The
  Meier–Meinert–VanWyk criterion from that item was not addressed here.

## Approaches and exactly where each dies

- **Dimension (Novikov–Sikorav plus `Σ^n = Σ^2 ∩ Σ^n(G;Z)`).** The argument
  needs `Tor` over `ZH` to vanish above some degree for a finite-index `H`,
  that is, finite vcd. The new hole is defined by the failure of exactly this.
- **Cocompact finite-dimensional models.** These need a proper cocompact action
  on a contractible finite-dimensional complex. Thompson-like groups act on
  infinite-dimensional Stein–Farley complexes, and all computed examples stop
  at level 2 for other reasons.
- **Finite index.** This is fully exploited above. It leaves the new hole
  invariant: if `G` is in the class, so is every finite-index subgroup, and
  conversely.
- **Elementary amenable groups.** These are excluded completely, but only
  through a secondary citation of KMPN 2009.
- **Kropholler's LH𝔉 theorem (J. Pure Appl. Algebra 90 (1993)).** If the
  torsion-free form "LH𝔉 groups of type FP_∞ have finite cd" holds as
  paraphrased in `every-torsion-free-f-infinity-group-of-infinite-cd-contains-f`,
  then the torsion-free members of the new hole lie outside LH𝔉. This was
  **not verified**, so no node uses it.
- **Heuristic size-bounded obstruction principle** (part 2 §3 of
  `research/artifacts/zp-properly-nested-bnsr-2026-09-13-part2.md`).
  - In the Morse computations for Stein–Farley-type complexes, links of large
    vertices have connectivity growing linearly in the size.
  - So failures of essential `(m−1)`-connectivity are seen at vertices of size
    at most `C·m`, and only finitely many sign patterns of `χ` on local moves
    occur.
  - This is not a theorem. A proof would need such a linear connectivity bound
    uniformly for a whole class of complexes. The new hole contains groups with
    no known complex of this kind, so the principle cannot currently be
    formalized for the class.
- **Constructions in the earlier lane** (part 2 §4: periodic germs,
  permutational wreath products `A ≀_X F`, measure-weighted lamps). None of
  them gave a character whose level is selected by a size parameter.
  - In `F` itself the germ group at an endpoint is `Z`, so no periodic
    structure survives.
  - In the wreath products the lamp counts are invariant under the dynamics,
    so no character selects a period.
  - No Thompson-like group with characters preserves a suitable measure.
  - The germ-host sub-question of part 2 §4 is still open.

## What remains open

- **`f-infinity-without-finite-vcd-non-proper-bnsr-inclusion`.** Every `F_∞`
  group of infinite vcd has some equality `Σ^m = Σ^{m+1}`. This is now the only
  open prerequisite on the no-side of 1.18 in this chain.
- **The yes-hole `f-infinity-group-with-properly-nested-bnsr-invariants`.** A
  candidate must have infinite vcd, must not be elementary amenable, and must
  have infinitely many distinct finite depths.
- **Weakest imported steps.**
  - The independence-of-choices theorem, known only secondhand through
    2505.18826v2 and 1507.08597v1, not re-read from Bieri–Geoghegan.
  - The KMPN 2009 theorem, known only secondhand through Hughes–Kielak.

## Files

Created:

- research/bnsr-invariants-are-detected-on-finite-index-subgroups.md
- research/bnsr-invariants-are-detected-on-finite-index-subgroups-proof.md
- research/virtually-finite-cd-f-infinity-groups-have-stable-bnsr.md
- research/virtually-finite-cd-stable-bnsr-via-finite-index-detection.md
- research/elementary-amenable-f-infinity-groups-are-type-vf.md
- research/elementary-amenable-f-infinity-groups-are-type-vf-citation.md
- research/elementary-amenable-f-infinity-groups-have-stable-bnsr.md
- research/elementary-amenable-stable-bnsr-via-type-vf.md
- research/non-type-f-non-proper-bnsr-by-virtual-cd-dichotomy.md
- research/f-infinity-without-finite-vcd-non-proper-bnsr-inclusion.md
- notes/zaremsky-1-18-properly-nested-bnsr-invar-swarm-2026-09-16.md

No committed node was modified.

## Referee (2026-09-16)

**What was checked.**

- **Files.** All 11 listed files were read in full. They were checked against
  the existing nodes `bnsr-invariants-stabilize-at-cohomological-dimension`
  (and its proof), `cocompact-contractible-d-complex-bnsr-stabilize-at-d`,
  `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`,
  `every-f-infinity-group-non-proper-bnsr-by-type-f-dichotomy`, the root, and
  the yes-hole. The other untracked `f-infinity-fcd-*` and
  `retract-closure-*` files belong to the Problem 1.21 lane, not this solver.
- **Finite-index detection proof.**
  - Step 1 holds: `K̃/H` is a `K(H,1)`, each free `G`-orbit of cells splits
    into `[G:H]` orbits of `H`, and `X` is admissible for `H`.
  - Step 2 holds, by pigeonhole on cosets.
  - Step 3 holds. The same `(X,h)` is admissible for both groups, so only
    well-definedness of `Σ^m` is used. Independence of `h` is elementary (a
    bounded difference on finitely many vertex orbits), and a note saying so
    was added.
  - The consequences "a drop passes down" and "stability passes up" are
    correct. It is a standard fact, and no novelty is claimed; a novelty
    sentence was added to the claim.
- **Virtual finite cd.** The route composes item 1 with the established
  cd-stabilization claim, and its hypotheses match. The case `d = 0` is
  trivial.
- **Elementary amenable case.** A finite `K(H,1)` gives a free resolution of
  length `dim L`, so `cd H` is finite. Soluble implies elementary amenable.
  The remark about Problem 1.12 is correct.
- **Dichotomy route.** The split is exhaustive. In the new hole, `F` is a
  member, since `Z^n ≤ F` and finite-index subgroups meet `Z^n` in free
  abelian groups of rank `n`. The class is closed under passing to
  finite-index subgroups and to finite-index overgroups of type `F_∞`.

**Quotes re-verified against the arXiv LaTeX sources, downloaded 2026-09-16.**

- **2505.18826v2 §2.1.** The setup, the definition, the independence sentence
  citing [bieri03, Theorem 12.1], and Remark (a) are verbatim.
- **1507.08597v1.**
  - Definition 1.1 and the well-definedness sentence, which cites Bux
    [Definition 8.1].
  - The §3 "reveal" sentence.
  - The numbering of Corollary 1.6 "Center survives" (Def 1.1, Cit 1.2,
    Cit 1.3, Lemma 1.4, Cit 1.5, Cor 1.6).
  - `cor:braid_sig`, and "the center of P_n also equals ⟨Δ²⟩ (for all n)".
- **2302.03346v2.** The definitions sentence, the sentence "by
  [KrophollerMartinezPerezNucinkis2009, Theorem 1.1] an elementary amenable
  group of type F_∞ is type VF", and the bibliography entry (Crelle 637 (2009)
  49–62, doi 10.1515/CRELLE.2009.090) are all verbatim.
- **1805.10052v2.** The "led to a proof ... constructible [K2]" quote is
  verbatim, with K2 = Kropholler, JPAA 90 (1993) 55–67.
- **0908.3669v1 §1.** The "failing the key finiteness theorem" quote is
  verbatim.
- **Zaremsky's problem list.** The PDF was fetched and its streams
  decompressed. It is dated July 12, 2026, and item 18 carries no annotation,
  unlike item 20, which is "(Added 6/12/25)".

**Extra corroboration of KMPN 2009.** The zbMATH review (Zbl 1202.20055, by O.
Talelli, fetched via the zbMATH API) lists the equivalent conditions for
elementary amenable `G`, including "virtually of type F" and "of type
FP_∞". This was added to the citation route. The paper itself is still not
read; the publisher page returned HTTP 405.

**Changes made.**

- The citation route now includes the zbMATH corroboration.
- The finite-index claim now has a novelty and import sentence.
- The finite-index proof now remarks that independence of `h` is elementary.
- In the new hole's Attempts, "the class is defined by the failure of exactly
  this" was an overstatement. The Novikov argument needs only
  `Tor^{ZH}_i(\widehat{ZH}_{-χ}, Z) = 0` for large `i`, and the wording now
  says so.

**Verdict.** The mathematics is sound and the labels are honest: two direct
routes (a proof and a secondary citation import), three composition routes and
one new hole with Attempts. No duplicates were found with
`cairn search --similar`, and all ids are at most 58 characters for claims.
Landed with small fixes.
