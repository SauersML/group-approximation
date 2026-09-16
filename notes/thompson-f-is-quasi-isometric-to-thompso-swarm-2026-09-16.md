# Swarm attack: is Thompson's group F quasi-isometric to T? (2026-09-16)

Agent: swarm-thompson-f-is-quasi-isometric-. Hole locked:
`thompson-f-is-quasi-isometric-to-thompson-t` (the yes-answer to part (c) of
Zaremsky Problem 2.4). The negation is `thompson-f-is-not-quasi-isometric-to-thompson-t`.

## 1. Status gate (dated sources)

- Zaremsky, *Some open problems*, https://zaremsky.github.io/open_problems.pdf,
  fetched 2026-09-16. The latest dated addition in Section 1 is item 25 "(Added
  7/12/26)". Section 2, item 4 still reads (text extracted from the PDF, spacing
  lost in extraction): "(Bridson) Is F quasi-isometric to F × Z? (Related:) Is F
  quasi-isometric to F × F? Is F quasi-isometric to T? (Surely not, but why not?)
  “Easier”: Does F quasi-retract onto F × Z or F × F? Does T quasi-retract onto
  F?" There is no update note attached to item 2.4. Item 2.5 carries the update
  that Migliorini proved T has quadratic Dehn function (arXiv:2410.23088).
- M. Migliorini, *Thompson's group T has quadratic Dehn function*,
  arXiv:2410.23088 (v1 2024-10-30, v2 2024-11-19), Forum Math. Sigma 13 (2025)
  e109. Abstract fetched 2026-09-16: T and all Higman–Thompson T_n have quadratic
  Dehn function. So the Dehn function no longer separates F (quadratic, Guba 2006)
  from T.
- A web search on "Thompson's group F quasi-isometric to Thompson's group T"
  (2026-09-16) returned only older embedding results (Burillo, Cleary–Stein–Taback,
  Shen arXiv:1803.00866 on quasi-isometric embeddings T_n -> T) and no resolution.
- **Verdict:** open as of the July 2026 version of the list. No resolution was
  found in 2024–2026 sources that could be reached. (The session's web-search
  budget ran out partway through, so the 2025–2026 sweep was not exhaustive; see
  Section 5.)

## 2. Setup, and what a yes-answer would force

Notation: `F ⊂ T ⊂ V` are the standard Thompson groups (Cannon–Floyd–Parry). An
element of `T` is given by a tree pair diagram `(S, R, k)`. Here `S` and `R` are
binary trees with `n+1` leaves each, and leaf interval `i` of `S` maps affinely
onto leaf interval `i+k mod (n+1)` of `R`. `c(g)` denotes the number of carets
per tree in the reduced diagram. `R_θ` is rotation of `R/Z` by a dyadic angle
`θ`.

- **Yes forces non-amenability of F.** The committed route
  `thompson-f-nonamenable-if-qi-to-thompson-t` gives this, because `T` is not
  amenable and amenability is a QI invariant. So a proof of the target would
  settle von Neumann's question for `F` negatively. A frontal attack on the
  yes-side is therefore at least as hard as that problem. Every realistic
  contribution is on the no-side, or is a fence that tells the no-side which
  invariants are useless.
- **Quasi-action reformulation.** Suppose `φ: T → F` is a QI with quasi-inverse
  `ψ`. Then `t ⋅ x := φ(t ψ(x))` is a quasi-action of `T` on `F` that is proper
  and cobounded. The converse also holds (Švarc–Milnor for quasi-actions). So the
  target says exactly that `T` quasi-acts properly and coboundedly on `F`. This
  reformulation is standard, and nothing new is claimed.

## 3. Obstructions to natural constructions (easy, but they kill the obvious maps)

**(a) No coarsely F-equivariant QI.** Let `θ: F → F` be a homomorphism whose
image has finite index. Then there is no QI `ψ: T → F` with
`d_F(ψ(f x), θ(f) ψ(x)) ≤ D` for all `f ∈ F` and `x ∈ T`.

*Proof.* `[T : F] = ∞`, because `T/F` is in bijection with the dyadic points of
the circle via `g ↦ g(0)`. Pick representatives `y_1, y_2, …` of pairwise distinct
right cosets `F y_i`, and let `t_1, …, t_m` be representatives of the right
cosets of `θ(F)` in `F`. Write `ψ(y_i) = θ(h_i) t_{j(i)}` with `h_i ∈ F`. Then
`ψ(h_i^{-1} y_i)` lies within `D` of
`θ(h_i^{-1}) θ(h_i) t_{j(i)} = t_{j(i)}`. The points `h_i^{-1} y_i` are pairwise
distinct, because they lie in distinct cosets, and all of them are mapped into
the `D`-neighbourhood of a finite set. This is impossible for a QI between
locally finite graphs. The same argument with left cosets rules out right
equivariance `ψ(x f) ≈ ψ(x) θ(f)`. ∎

So any QI `T → F` has to absorb the coset direction `T/F` (the "rotation
coordinate") non-equivariantly. No extension of `id_F` along `F`-cosets can work.

**(b) Cut-type maps collapse the rotation subgroup.** Let `p` be any rule
assigning a dyadic point to each `g`. A map of the form
`g ↦ R_{-g(p(g))} ∘ g ∘ R_{p(g)}` lands in `F`, since it fixes `0`. It sends every
rotation `R_θ` to `R_{-θ-p} R_θ R_p = id`, where `p = p(R_θ)`. The dyadic rotation
group `Z[1/2]/Z` is infinite, so no such map is a coarse embedding, whatever `p`
is. The one-sided cut `r(g) = R_{-g(0)} ∘ g` also fails to be coarsely Lipschitz.
That failure is recorded in the committed node
`thompson-t-quasi-retracts-onto-f-resolved`, which is why it does not even give
a quasi-retraction.

**(c) What survives.** A QI `T → F` would have to encode the rotation coordinate
`g(0) ∈ Z[1/2]/Z` as coarse data in `F`. That coordinate is unbounded but only
logarithmically costly: a dyadic point of depth `m` costs about `m` carets.
Every construction I tried (padding the diagram with a spine of carets encoding
`g(0)`, or re-rooting the tree at `g^{-1}(0)`) runs into one of three problems:
it is not coarsely Lipschitz under right multiplication by the rotation
generator `C` of order 3; it collapses rotations as in (b); or it respects cosets
as in (a). None of these attempts reached a statement worth a node.

## 4. Main contribution: Hilbert space compression does not separate F from T

New nodes (checked with `check.sh`, exit 0; all three claims are ESTABLISHED
in the check worktree):

- `thompson-t-has-hilbert-space-compression-one-half` (claim): `α*(T) = α(T) = 1/2`.
- `thompson-t-compression-one-half-via-cylinder-charts` (route). It requires:
  - `thompson-v-standard-cylinder-charts-are-commensurated` (already
    ESTABLISHED in the repo, by a direct proof);
  - `thompson-f-word-length-is-comparable-to-caret-count` (new claim, imported
    from Burillo–Cleary–Stein arXiv:math/9809185 by the route
    `thompson-f-word-length-is-comparable-to-caret-count-citation`);
  - `thompson-f-has-hilbert-space-compression-one-half` (new claim, imported
    from Arzhantseva–Guba–Sapir arXiv:math/0411605 by the route
    `thompson-f-has-hilbert-space-compression-one-half-citation`).

Proof outline (the full proof is in the route body):

1. **One caret count.** The reduction criterion for a caret pair is the same in
   F, T and V. A V pair with no removable caret pair has domain internal node set
   `N_g` (the non-canonical words of the chart proof). So the caret count `c` is
   the same whether `g` is read in `F`, `T` or `V`.
2. **Cocycle.** `b(g) = 1_{gA} - 1_A ∈ ℓ²(X)` is a 1-cocycle for `T ⊂ V`, with
   `‖b(g) - b(h)‖² = 2c(h^{-1}g)`. Its subadditivity gives `c(x) ≤ M|x|_T`.
3. **Word length in T is linear in carets.** If `g = (S, R, k)` with `k ≠ 0`,
   then `g = (P', R, 0) ∘ R_{1/2} ∘ (S, P, 0)`. Here `P` splits its leaves
   `n+1-k | k` at the root, and `P'` is `P` with the two root subtrees swapped.
   The outer factors are elements of `F` with at most `n` carets. Burillo–Cleary–
   Stein then give `|g|_T ≤ K(c(g) + 1)`.
4. **Lower bound.** Hence `‖b(g) - b(h)‖ ≥ (2/K)^{1/2} d_T(g,h)^{1/2} - √2`, and
   `α*(T) ≥ 1/2`.
5. **Upper bound.** `F` is undistorted in `T`, from step 2 plus Burillo–Cleary–
   Stein, and it also follows from the BCST abstract. Restricting a compression
   embedding to `F` gives `α(T) ≤ α(F) = 1/2`.

Consequence for the target: compression is a QI invariant (Guentner–Kaminker),
and `α(F) = α(T)`. So compression cannot refute the target. Two variants fail
in the same way:

- **Equivariant exponent.** Restricting `b` to `F` gives `α*(F) = 1/2` as well.
- **ℓ¹ version** (derived here, not made a node). In `ℓ¹(X)`,
  `‖b(g) - b(h)‖_1 = |gA Δ hA| = 2c(h^{-1}g)`, which lies between
  `(2/K)d_T - 2` and `2M d_T`. So `T`, and by restriction `F`, admits an
  equivariant quasi-isometric embedding into `ℓ¹`. Coarse `ℓ¹`-embeddability
  and `ℓ¹`-compression (`= 1` for both) cannot separate them either.

Novelty: I found no statement of `α(T) = 1/2` (arXiv searches "Thompson
compression Hilbert", "equivariant compression Thompson" and "compression
diagram groups cube complex", 2026-09-16). It is very likely folklore: it follows
at once from Farley-type proper actions together with the BCST caret estimate.
It is recorded as a checked fence, not as a new theorem.

Weakest points:

- The Burillo–Cleary–Stein constants were reconstructed from PDF text with the
  inequality signs lost. Only the verbatim qualitative abstract is load-bearing.
- The AGS body (its definition of compression) was not read. Only the abstract
  was.
- Step 1 relies on the committed chart proof's description of `N_g`.

## 5. Literature consulted (2026-09-16)

Fetched, with verbatim text recorded in the citation routes:

- Zaremsky, *Some open problems* (PDF, latest item "Added 7/12/26"). Item 2.4 is
  still open.
- Migliorini, arXiv:2410.23088 (abstract): T has a quadratic Dehn function.
- Burillo–Cleary–Stein, arXiv:math/9809185:
  - abstract, verbatim;
  - Theorems 1 and 3, read from extracted PDF text with the symbols lost.
- Burillo–Cleary–Stein–Taback, arXiv:math/0503670: abstract, verbatim ("the
  number of carets in a reduced representative of an element of T estimates the
  word length, and that F is undistorted in T").
- Arzhantseva–Guba–Sapir, arXiv:math/0411605: abstract, verbatim (`α(F) = 1/2`).
- Guentner–Kaminker, arXiv:math/0309166: abstract, verbatim (compression is a QI
  invariant).
- Belk–Brown, arXiv:math/0305412 (PDF text extracted). The length formula is
  Theorem 4.2.2. It was checked but not used, because its forest carets are not
  tree carets (e.g. `x_0^k` has no forest carets).
- arXiv searches on compression and Thompson groups found only AGS, plus
  Campbell–Niblo arXiv:math/0403456 and Genevois arXiv:1712.01618. Neither is
  about T.

Not fetched, or unverified (do not cite as checked):

- The journal version of AGS. The arXiv abstract page shows no journal
  reference.
- Divergence of F and T. Golan–Sapir is recalled as proving linear divergence
  for both. Not fetched.
- `H^*(T; ZT)`. The committed negation node records the Brown–Geoghegan
  announcement at p. 368. A Farley 2005 paper on picture groups was not located.
- ℓ²-Betti numbers of `T`. No source located. The Sauer–Thumann results found
  earlier concern V-like groups.
- Burillo–Cleary–Röver, and Cleary–Taback 2008, came up during searches but were
  not read.
- Web-search budget: exhausted at 200 queries earlier in the session. Later
  checks used arXiv listing pages through WebFetch only, so the 2025–2026 status
  sweep relies on Zaremsky's July 2026 list plus the arXiv title searches.

## 6. Where each approach dies, and what remains

| Approach | Side | Where it dies |
|---|---|---|
| Construct a QI `T → F` | yes | Implies `F` non-amenable, via the committed route. Coarsely `F`-equivariant maps are impossible (3a), and cut-type maps collapse the rotations (3b). |
| Amenability | no | Conditional on `thompson-f-is-amenable` (committed route). |
| Dehn function | no | Both quadratic (Guba; Migliorini 2024). |
| Asymptotic dimension | no | Both infinite. |
| Hilbert space compression (`α`, and `α*`) | no | Both `1/2`. **This session**, node `thompson-t-has-hilbert-space-compression-one-half`. |
| Coarse `ℓ¹`-embeddability / `ℓ¹`-compression | no | Both embed quasi-isometrically and equivariantly in `ℓ¹`, via the chart cocycle (Section 4). |
| QI embedding `T → F` by monotone invariants | no | Asymptotic dimension (monotone under coarse embeddings), `α` and `ℓ¹`-compression (monotone under QI embeddings) all agree for `F` and `T`. |
| `H^*(G; ZG)` | no | Live only if some `H^k(T; ZT) ≠ 0`. Not computed, and the Brown–Geoghegan announcement may indicate vanishing (the group it refers to is not identified). |

What remains plausible for the no-side:

- An invariant that is sensitive to the *circle* rather than the interval, and
  is not implied by non-amenability. Candidates:
  - Poincaré or separation profiles (Benjamini–Schramm–Timár; Hume–Mackay–Tessera).
    These are monotone under coarse embeddings, so an upper bound on `sep_F`
    below a lower bound on `sep_T` would refute a coarse embedding `T → F`.
  - Coarse topology at infinity (`H^*(G; ZG)`, or proper homotopy invariants
    beyond it).
- None of these was computed here. I found no computation of separation profiles
  for `F` or `T`. This is an untested idea, not a claim.
- Any such invariant must agree on everything that the chart cocycle sees
  metrically: square-root Hilbert growth and linear `ℓ¹` growth for both groups.
  It also must not depend only on amenability.

Outcome of this session: an obstruction-type fence (compression), recorded as
three ESTABLISHED claims, plus two elementary construction obstructions (3a, 3b)
kept in notes. The target `thompson-f-is-quasi-isometric-to-thompson-t` remains
OPEN, and so does its negation.


## Referee (2026-09-16)

What I checked.

- **Status gate.** I re-fetched Zaremsky's *Some open problems* PDF on
  2026-09-16 and extracted its text. The latest item is "25. (Added 7/12/26)".
  Section 2, item 4 still reads "Is F quasi-isometric to T ? (Surely not, but
  why not?)" with no update note. The target and its negation remain OPEN, and no
  node claims otherwise.
- **Citations.** I spot-checked the arXiv abstract pages for math/9809185 (BCS;
  Trans. AMS 353 (2001) 1677–1689), math/0503670 (BCST; Trans. AMS 361 (2009)
  631–652) and math/0411605 (AGS). The quoted abstracts match. For AGS I also
  extracted the body text:
  - Definition 1.2 (cf. Guentner–Kaminker Def. 2.2) uses lower control `C n^α`
    and linear upper control.
  - Theorem 1.3 states that `F` has compression 1/2.

  This was the solver's flagged weak point. The citation route now records the
  body definition and why it matches the claim's "`C d^a - D`, Lipschitz" form,
  in place of the solver's "Unverified item" paragraph. AGS p. 5 also quotes
  Guentner–Kaminker: equivariant compression `> 1/2` implies amenability. So
  `α*(T) ≤ 1/2` also follows independently from non-amenability of `T`, which
  corroborates Step 6.
- **Theorem 0 (caret counts agree).** I re-derived it. The V-reduction criterion
  (a caret `w0, w1` of `S` whose images are the ordered children of one caret of
  `R`) is the T/F criterion, and the maximal-length argument against `I ⊋ N_g`
  is correct. A reduced T-diagram of an element of `F` has `k = 0`, because leaf
  `k` of `R` must start at `0`.
- **Factorisation through `R_{1/2}` (Step 3).** I checked the leaf bookkeeping
  by hand. Script `scratchpad/ref/fact.py` (not landed) also tested it on 300
  random `(S, R, k)` with 2 to 9 leaves: I built `P` and `P'`, composed
  `(P',R,0) ∘ R_{1/2} ∘ (S,P,0)`, and compared with `g` on 40 dyadic points
  each. There were 0 mismatches.
- **Cocycle and estimates (Steps 1, 2, 4, 5, 6 and the α*(F) addendum).** I
  rechecked them line by line:
  - the cocycle identity;
  - `‖b(g)-b(h)‖² = |h^{-1}gA Δ A|`;
  - subadditivity of `c`;
  - `√(u-v) ≥ √u - √v`;
  - the undistortion bound `d_T ≥ (d_F - K_0)/(K_0 M)`;
  - the subadditivity of `t^a` used in restricting to `F`.

  No gaps. The only literature inputs are the two citation imports, whose
  qualitative statements are exactly what the sources state.
- **Duplicates.** `bin/cairn search --similar` on the three new claims found no
  near-duplicates. A `git grep` found no committed node on caret counts versus
  word length, undistortion of `F` in `T`, or compression.
- **Novelty.** Not claimed, and correctly so. The claim is labelled probable
  folklore. Its Step 3/5 ingredients are in the BCST abstract. I could not run
  further web searches (search budget exhausted), so prior statements of
  `α(T) = 1/2` cannot be excluded.
- **Notes Section 3.** (a) The coset-pigeonhole argument is correct: a QI has
  bounded preimages of bounded sets. (b) `R_{-(p+θ)} R_θ R_p = id` is correct.
  Both stay in notes, which is appropriate.

What I changed: only the AGS citation route (definition checked, equivalence of
the two forms of the definition justified). No mathematical content was
withdrawn or downgraded.

Verdict: sound. The work lands with that small fix. It is a fence: Hilbert space
compression (ordinary and equivariant) and `ℓ¹` compression cannot separate
`F` from `T`. Zaremsky 2.4(c) is still open in both directions.
