# Zaremsky 1.21 (G × Z of type F ⇒ G of type F?): swarm lane 2026-09-16

- Agent: `swarm-zaremsky-1-21-g-times-z-type-f`.
- Root: `zaremsky-1-21-g-times-z-type-f-implies-g-type-f`.
- Hole locked: `f-infinity-groups-of-finite-cd-are-of-type-f`.

## Setup (from the graph)

Two established nodes reduce Problem 1.21 to the hole: every group of type
`F_∞` with finite cd is of type F.

- `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`: `G × Z` of type F ⟺
  `G` is `F_∞` with finite cd ⟺ `G` is finitely presented of type FP.
- `g-times-z-type-f-iff-finitely-dominated-classifying-space`.

The hole is equivalent to `σ(G) = 0 ∈ K̃_0(ZG)` for every finitely presented
FP group (`fp-type-fp-group-is-type-f-iff-wall-class-vanishes`). It follows
from Hsiang / Farrell–Jones (`K̃_0(ZG) = 0` for torsion-free `G`), and it
reduces to `K̃_0` of one universal finitely presented torsion-free tester
(`reduced-k0-of-universal-fp-torsion-free-tester-vanishes`).

## External gate (dated 2026-09-16)

- **Zaremsky's list**, version of July 12, 2026 (op.pdf, fetched this lane):
  Problem 1.21 still posed as open.
- **I. J. Leary**, arXiv:1512.06609v4 (fetched): "No examples are known that
  distinguish between the properties FP(Z), FL(Z) and FH(Z)."
- **W. Lück**, survey arXiv:2507.11337v1 (2025-07-15, fetched):
  - Conjecture 2.1: `K̃_0(ZG) = 0` for torsion-free `G`;
  - Conjecture 2.4 (Serre, FP ⇒ FF) follows from 2.1;
  - §11: "not aware of any group for which the Full Farrell-Jones Conjecture
    8.10 is known to be false".
- **S. Ferry and A. Ranicki**, arXiv:math/0008070 (fetched): Proposition 1.5,
  the mapping torus identity `T(d∘s) ≃ T(s∘d)` and the sum theorem.
- **M. Ershov and M. C. B. Zaremsky**, arXiv:2505.18826 (fetched):
  - §2: `Σ^m(G)` open [BNS87, Ren88], and Aut-invariance;
  - Theorem 2.3: Renz Satz C;
  - Proposition 3.1: `e(G) ≠ 0` ⇒ `Σ^∞ ∩ −Σ^∞ = ∅` for type F;
  - Remark 3.2: the homological variant.
- **arXiv API**, keyword search for 2024–2026 papers on finiteness
  obstruction / FP vs FL / Problem 1.21: nothing resolving the problem.
  WebSearch budget was exhausted mid-lane, so the literature sweep is not
  exhaustive.
- **Not fetched**, recalled only: Bieri–Renz, Comment. Math. Helv. 63 (1988).
  Status unverified here, but it is the same import used by the established
  `nonzero-euler-characteristic-blocks-symmetric-sigma-proof`.

Conclusion: 1.21 remains open. "Yes" is the finitely presented case of
Serre's FP ⇒ FF. "No" would give a torsion-free group with `K̃_0(ZG) ≠ 0`,
refuting Hsiang / Farrell–Jones.

## What was proven

Full proofs are in
`research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md`.

1. **Theorem A′ (sum formula).** Let `G` act cocompactly on a tree without
   inversions, with all stabilizers FP. Then `G` is FP and
   `χ_G = Σ_v ind χ_{G_v} − Σ_e ind χ_{G_e}` in `K_0(ZG)`. Proof: mapping cone
   of a lift of the Bass–Serre boundary map to induced resolutions. Sanity
   checks: `F_2 = Z*Z` has `e = −1`, genus-2 amalgam has `e = −2`,
   `BS(1,n)` has `e = 0`.
2. **Theorem A** (node `ascending-hnn-of-fp-group-has-zero-k0-euler-class`).
   Let `B` be FP and `φ` injective. Then `χ_{B*_φ} = 0`, and `B*_φ` is of type
   F iff it is finitely presented. Corollary: a finitely presented group that
   maps onto `Z` with an FP kernel is of type F. Route
   `ascending-hnn-zero-k0-euler-class-proof`, requiring the established Wall
   criterion.
3. **Theorem B** (node
   `f-infinity-fcd-group-with-antipodal-sigma-pair-is-type-f`). Let `G` be
   `F_∞` with `cd = d`, and suppose `Σ^d(G;Z) ∩ −Σ^d(G;Z) ≠ ∅`. Then `G` is of
   type F with `χ_G = 0`.
   - Proof: openness, a rational discrete character, the kernel criterion,
     `FP_d` + `cd ≤ d` ⇒ FP, then Theorem A.
   - It upgrades Ershov–Zaremsky Prop 3.1 from the integer `e(G)` to the full
     class `χ_G`, and from type F to `F_∞` with finite cd.
   - Route `antipodal-sigma-pair-type-f-proof`.
4. **Theorem C** (node `retracts-of-type-f-groups-are-of-type-f`, OPEN). The
   hole ⟺ "every retract of a type F group is of type F".
   - Route `retract-closure-from-f-infinity-fcd-type-f` uses the retract
     argument: retracts of type F groups are finitely presented of type FP.
   - Route `f-infinity-fcd-type-f-from-retract-closure` uses `G` as a retract
     of `G × Z`.
5. **Proposition D (artifact only).**
   - `σ(A*B) = ind σ(A) + ind σ(B)`, and induction from a free factor is
     injective on `K_0`.
   - So `A*B` is of type F iff `A` and `B` are.
   - Counterexamples are closed under `* H` for `H` of type F, and under
     `× F_2`. Their cohomological dimensions form an upward-closed set
     starting at `≥ 2`.
   - A counterexample has a one-ended Grushko factor that is a counterexample.
   - A `cd 2` counterexample is a finite presentation of a `cd 2` group whose
     `π_2` is projective but not stably free (`σ = −[π_2]`).
6. **Shape of a counterexample `G`** (`d = cd G`):
   - one-ended, after passing to a Grushko factor;
   - no epimorphism to `Z` with an FP kernel;
   - not an ascending HNN extension over any FP base;
   - `Σ^d(G;Z) ∩ −Σ^d(G;Z) = ∅`, so no antipodal pair in `Σ^∞`, and
     `Σ^d(G;Z) = ∅` if some automorphism acts as `−1` on `H^1(G;R)`;
   - in any cocompact FP tree decomposition,
     `Σ_v ind σ(G_v) ≠ Σ_e ind σ(G_e)`;
   - splittings over type F edge groups push the counterexample into a vertex
     group. This needs the recalled fact that vertex groups of a finitely
     presented group split over finitely generated edges are finitely
     presented.

No novelty is claimed: this is standard Wall / Bass–Serre / BNSR
bookkeeping. The contribution is recording it in the graph as constraints on
counterexamples, together with the retract equivalence.

## Approaches tried and where each dies

- **One-sided Σ.** A single `[χ] ∈ Σ^d(G)` should make `G` an ascending HNN
  extension over a good base.
  - For `m = 1`, BNS (recalled) gives a finitely generated base only.
  - For `m ≥ 2` I have no verified statement producing an `FP_m` (or FP) base,
    and Theorem A needs FP.
  - Dies at: extracting an FP base from a one-sided invariant.
- **Novikov-ring localization.** Map `K̃_0(ZG) → K̃_0(\widehat{ZG}_χ)`, where
  the one-sided condition might kill `σ`. Dies: no injectivity of this map is
  known, so vanishing in the Novikov ring says nothing about `σ(G)`.
- **Transfer through the central extension `G × Z`.** Try to lift idempotent
  matrices representing `σ(G)` into `Z[G × Z]` and detect them there. Dies:
  `σ(G × Z) = e(Z)·ind σ(G) = 0` identically, and restriction back to `G`
  loses nothing but gains nothing. Idempotents over `ZG` do not correspond to
  stably free modules over `Z[G×Z]` in any way that sees the class.
- **`cd = 2`.** `σ(G) = −[π_2 X]` for a presentation complex `X`. Dies:
  stable freeness of `π_2` for `cd 2` finitely presented groups is itself
  open. It is equivalent to the hole in `cd 2`, and it is of Eilenberg–Ganea /
  D(2) flavour.
- **Swan induction / finite quotients.** Restricting `σ(G)` to finite-index
  subgroups or pushing to finite quotients sees only information in finite
  group rings or in `K̃_0` of subgroups. Restriction to finite-index subgroups
  need not be injective on `K̃_0`, and no argument was found that forces
  `σ(G) = 0` this way.
- **"1.21 yes ⇒ Serre's conjecture in general."** The hope was to embed an
  arbitrary FP group into a finitely presented FP group with injective
  `K̃_0`. Dies: FP groups need not be recursively presented (Leary's
  uncountably many FP groups), so there is no finitely presented FP host in
  general. The graph's universal tester handles the reverse direction.
- **Pushing a resolution along the retraction `r`.** Dies: the homology of
  `ZG ⊗_{ZΓ} C_*` is `H_*(ker r)`. It works only for acyclic `ker r`, and
  `Z` is not acyclic.
- **Product formula for `K ⋊ G`.** Detects `σ(G)` up to `e(K)`. Dies at
  `e(K) = 0`, the original case.

## Files

- `research/ascending-hnn-of-fp-group-has-zero-k0-euler-class.md` (claim)
- `research/ascending-hnn-zero-k0-euler-class-proof.md` (route)
- `research/f-infinity-fcd-group-with-antipodal-sigma-pair-is-type-f.md` (claim)
- `research/antipodal-sigma-pair-type-f-proof.md` (route)
- `research/retracts-of-type-f-groups-are-of-type-f.md` (claim, OPEN)
- `research/retract-closure-from-f-infinity-fcd-type-f.md` (route)
- `research/f-infinity-fcd-type-f-from-retract-closure.md` (route)
- `research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md`
- this note

## What remains

The hole is untouched in the non-fibred, non-splitting, one-ended,
Σ-asymmetric regime. The single class `σ(G)` has no known specific vanishing
mechanism. A weakest-link audit should target:

- the import of the homological Bieri–Renz criterion and openness (recalled,
  not fetched; the homotopical version is verified from 2505.18826);
- the cone argument's claim `H_1(C) = ker ∂`. This is standard, but it is
  load-bearing for Theorem A.

## Referee (2026-09-16)

What I checked:

- **Theorem A** (`ascending-hnn-zero-k0-euler-class-proof`). I rechecked the
  Bass–Serre tree of `B*_φ`: `gbt⁻¹B = gt⁻¹φ(b)B`, and the edge stabilizer sits
  inside both endpoint stabilizers because `tBt⁻¹ ⊆ B`. For the cone, the long
  exact sequence gives `H_k(C) = 0` for `k ≥ 2`, `H_1(C) = ker ∂ = 0` and
  `H_0(C) = coker ∂ = Z`. The alternating sum telescopes to `0`, and FL, F and
  the fibred corollary follow. No gap found. The Bestvina–Brady model test is
  consistent.
- **Theorem B** (`antipodal-sigma-pair-type-f-proof`).
  - Openness plus density of rational rays gives a discrete `χ` with
    `χ(G) = Z`. The Bieri–Renz criterion gives `ker χ` of type `FP_d`, and
    the dimension shift `Ext^1(K,M) ≅ H^{d+1}(N;M) = 0` gives FP. Theorem A
    finishes. Correct.
  - Automorphism case: `Σ = −Σ` gives `U = Σ`. Correct.
  - The claim that this "extends Ershov–Zaremsky from `e(G)` to `χ_G`" has
    content only for non-type-F groups: for type F groups `χ_G = e(G)[ZG]`.
    Not an overclaim, since the claim is stated for `F_∞` groups of finite cd.
- **Lemma C0 / Theorem C.**
  - Normal-closure argument, including closure under inverses: checked.
  - Bieri–Eckmann retract argument: the same as the established
    `g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`.
  - `retracts-of-type-f-groups-are-of-type-f` is a new hole equivalent to
    the existing hole through two routes (Cairn's "equivalence" pattern). It
    has `## Attempts` and a recorded `distinct_from`. `check.sh` exits 0.
  - The special cases were checked: free factors via `(r_A)_* ind_B` landing
    in free modules, and the product formula `σ(G×H) = e(H)·ind σ(G)`.
- **Proposition D and Corollary D1 (artifact only).**
  - The Grushko one-ended reduction is correct: torsion-free freely
    indecomposable groups are trivial, `Z` or one-ended.
  - `cd(G × F_2) = d+1` for FP `G`: correct.
  - The `cd 2` sign `σ = −[π_2 X]` was re-derived from
    `0 → π_2 → C_2 → im → 0` splitting.
  - The splitting Remark rests on a recalled fact, is flagged as such, and no
    route uses it.
- **Duplicates.** I ran `bin/cairn search --similar` on all three new claims.
  The nearest neighbours are the Wall criterion, `G×Z`, `G×H`,
  `nonzero-euler-characteristic-blocks-symmetric-sigma` and the Stallings
  mapping torus. All are covered by `distinct_from`, and none states these
  results. Id lengths are ≤ 56. No route targets the root.
- **Literature spot-checks.**
  - Zaremsky's list PDF, re-fetched: the latest addition is dated 7/12/26,
    and Problem 21 is posed verbatim with no answer recorded.
  - arXiv:2505.18826v3 (HTML), re-fetched:
    - openness of `Σ^m(G)` is cited to [BNS87, Ren88];
    - Renz's characterization is stated;
    - Remark 3.2 says the Proposition 3.1 argument "applies equally well to
      the homological BNSR-invariant".
  - Lück, arXiv:2507.11337v1: Conjecture 2.1 (`K̃_0(ZG) = 0`, torsion-free)
    and Conjecture 2.4 (Serre, FP ⇒ FF) confirmed.
  - Leary, arXiv:1512.06609v4: my text extraction of the PDF decoded only page
    1, so I could NOT locate the quoted sentence "No examples are known that
    distinguish…". Treat that quote as unverified by the referee. Nothing
    load-bearing depends on it.
  - Bieri–Renz, Comment. Math. Helv. 63 (1988): still recalled and not
    fetched. The referee's web-search budget was exhausted. It is the same
    import already carried by the established
    `nonzero-euler-characteristic-blocks-symmetric-sigma-proof`, and it is the
    one remaining trust point of Theorem B in its homological form.

What I changed:

- In artifact §4, Proposition D proof step 1, I replaced "Finite
  presentation of `Γ` is clear" with the one-line reason.
- In this note, I softened the "Swan induction" dead-end line, which had said
  it "never forces `σ(G) = 0`", to "no argument found".

Verdict: sound and honestly labelled, landed with the minor fixes above. The
established nodes are standard Wall / Bass–Serre / BNSR bookkeeping (no
novelty claimed). Problem 1.21 and `f-infinity-groups-of-finite-cd-are-of-type-f`
remain open.
