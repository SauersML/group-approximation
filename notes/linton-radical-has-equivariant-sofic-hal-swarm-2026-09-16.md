# Linton halos: a contraction obstruction and stage sensitivity, swarm attack, 2026-09-16

- **Lane:** `swarm-linton-radical-has-equivariant`.
- **Hole locked and worked:** `linton-radical-has-equivariant-sofic-halo`.
- **Full proofs:** `research/artifacts/linton-halo-contraction-obstruction-2026-09-16.md`.
- **Scripts:** `experiments/linton-halo-contraction-obstruction-2026-09-16/check_words.py`,
  output in `output.txt` in the same directory (ALL PASS).
- **Outcome:** an obstruction.
  - A necessary condition holds for every set-halo presentation of a
    semidirect product.
  - Explicit sofic one-relator groups violate it at shallow derived stages and
    satisfy the target beyond them.
  - The target is false under the least-stage and every-stage readings.  Under
    the existential reading it is not refuted.
- **New nodes:**
  - `halo-shell-invariant-conjugations-are-virtually-inner` (claim), with
    route `-proof` (`requires: []`);
  - `linton-halo-conclusion-fails-at-shallow-derived-stages` (claim), with
    route `-proof`.

## Setup

The target asks for a set-theoretic halo `L`, an `F0`-set `X` and an
`F0`-equivariant isomorphism `theta : L(X) -> R`, with sofic finite pieces.
Here `E = R semidirect F0` is "the finite rational-derived shell" of a
one-relator group.  The landed tame case is
`permuted-free-product-linton-radical-gives-sofic-shell`: radicals that are free
products of isomorphic factors permuted freely by `F0`.

Two facts about the shell were not previously recorded as relevant.

- `one-relator-soficity-localizes-at-rational-derived-stage` asserts only that
  *some* `n <= |w|` is valid, meaning `G_Q^(n)/R` is free.  Its lemma gives
  `G_Q^(n)/R = (G/R)_Q^(n)`, so the valid stages form an up-set.  The target
  does not say which stage it means.
- Soficity of `G` is equivalent to soficity of `G_Q^(n)` at every valid `n`.
  So the downstream routes `linton-halo-gives-radical-sofic`,
  `linton-halo-gives-action-sofic` and `linton-shell-sofic-via-sofic-action`
  may use any valid stage.

## What was proven

1. **Theorem 1 (virtually inner).**  In any halo presentation, if `e` in `E`
   conjugates a finitely generated `H <= R` into itself, then some `e^N` acts
   on `H` as conjugation by an element of `R`.
   - Proof: `H` lives in one finite piece `L(Y)`.
   - Replace the site permutation `pi(f)` by a finitary permutation `sigma`
     agreeing on `Y`.  Functoriality makes `L(sigma)` and `L(pi(f))` agree on
     `L(Y)`.
   - Compute in `L(X) semidirect Sym(X)`, where `(r, sigma)^ord(sigma)` lies
     in `L(X)`.
   - Uses neither the intersection axiom nor soficity, and does not depend on
     the complement.
   - Corollary 2: `N_E(H)/(N_R(H) C_E(H))` is torsion.
2. **Lemma 3.**  In a locally free group, `rho H rho^-1 <= H` with `H` finitely
   generated forces equality.
   - If the inclusion is strict, `<H, rho>` is the ascending HNN extension.
   - That extension is free, so rational Mayer--Vietoris forces rank 1, a
     contradiction.
   - Corollary 4: if `R` is locally free, no element of a shell with a halo
     presentation contracts a finitely generated subgroup of `R`.
3. **`G0 = <a,s | s a s^-1 = [a, s^-1 a s]>`**, relator length 11.
   - `G0` is the ascending HNN extension of `F(x,y)` along `x -> y`,
     `y -> [y,x]`, which is injective but not onto.
   - `R = <<a>>` is perfect, nontrivial and locally free.
   - At stage 0 (`F0 = Z`) there is no halo presentation for any complement.
   - At every stage `n >= 1` (`F0 = 1`) the target's conclusion holds.
   - `G0` is sofic.
4. **`G_u = <a,p,q | u a u^-1 = [a, u^-1 a u]>`**, with
   `u in F(p,q)^(d) \ F(p,q)^(d+1)`.
   - `R` is the free product of the `g R0 g^-1` over `F/<u>`, by Bass--Serre.
   - Every stage is valid.
   - For `n <= d` there is no halo presentation.
   - For `n >= d+1` there is a sofic halo presentation, by part 3 of the
     permuted-free-product claim, because the stabilizers
     `F^(n) cap g<u>g^-1` are trivial.
   - `G_u` is sofic.
   - So the least stage with a halo presentation is not universally bounded.

## Approaches and where each dies

- **Prove the target at the least valid stage.**  Dies on `G0`: the stable
  letter contracts the rank-2 base inside the locally free radical (Corollary 4).
- **Prove it at every valid stage.**  Dies on `G0` and on `G_u` for `n <= d`.
- **Refute the existential reading.**  Not achieved.  It would need, at every
  valid stage, an element of `G_Q^(n)` violating Corollary 2 on some finitely
  generated `H <= R`.
  - Amalgams along a single word `u` fail, since the contraction depth is the
    derived depth of `u`.
  - Composites of contractions of one subgroup are positive words in the
    contracting letters, and positive words never lie in `F'`.  So iterating
    one contraction does not reach deeper stages.
  - An infinite-order outer action on a fixed noncyclic `H` by a non-solvable
    subgroup of `F0` would survive at every depth.  No one-relator example was
    found.
- **Graph halos.**  Theorem 1 needs finitary permutations of `X` in the domain
  of `L`, so it does not constrain graph halos.  That refinement (Attempt 3 of
  the target) is untouched.

## Recommendation (not applied; the target is not source-owned)

Restate the target at a sufficiently deep valid stage, or quantify it
existentially over valid stages.  The least valid stage is refuted by `G0`.
Any proof must choose the stage after the relator.  The downstream routes lose
nothing.  The new claim `linton-halo-conclusion-fails-at-shallow-derived-stages`
records the counterexamples.  No `refuted_by` was added, because the target's
stage reading is ambiguous.

## Literature gate (2026-09-16)

No 2024--2026 source on halo presentations of one-relator Linton radicals, or
on this obstruction, was found.  Web search quota was exhausted.  The
export.arxiv.org API returned 429/503, so coverage is arXiv abstract and listing
pages only.

- V. Alekseev, H. Bradford, *Sofic actions, halo products, and metric
  approximations of groups*, arXiv:2601.18742v1 (submitted 2026-01-26; abstract
  page fetched 2026-09-16, still v1).  Definitions 2.1 and 2.4 via the audited
  quotations in `research/artifacts/or-linton-halo-2026-09-12.md`.
- M. Linton, *Residually rationally solvable one-relator groups*,
  arXiv:2407.09272 (v1 2024-07-12, v2 2025-09-19; abstract page fetched
  2026-09-16).
- A. Borisov, M. Sapir, arXiv:math/0309121, Invent. Math.,
  DOI 10.1007/s00222-004-0411-2 (abstract page fetched 2026-09-16).  Residual
  finiteness of mapping tori of free-group endomorphisms.  Used only as an
  alternative soficity argument for `G0`.
- F. Berlai, *A new family of sofic one-relator groups*, arXiv:2502.05064
  (seen in an arXiv listing 2026-09-16; calibration only).
- G. Elek, E. Szabo, arXiv:1010.3424, Theorem 1.  Cited through the landed
  route `permuted-free-product-linton-radical-gives-sofic-shell-proof`; not
  re-fetched.
- arXiv listing searches on 2026-09-16: "sofic one-relator", "halo products
  sofic", "rational derived series one-relator", "ascending HNN free group
  sofic".  No relevant new hits.
- Classical, not re-fetched, unverified here: Takahasi's chain condition,
  Schreier's index formula, virtual torsion-freeness of `Out(F_r)`.  They are
  used only in an unused remark.  Lemma 3 is proved without them.

## Referee (2026-09-16)

Checked, adversarially:

- **Definition.**  Alekseev--Bradford Definition 2.4, via the audited
  quotation in `research/artifacts/or-linton-halo-2026-09-12.md`: a
  set-theoretic halo is a covariant functor on *all* sets with injections.
  So `L(sigma)` is defined for every finitary permutation `sigma`, and
  `sigma -> L(sigma)` is a homomorphism `Sym(X) -> Aut(L(X))`.  Step 4 of
  Theorem 1 is legitimate.  The target's intertwining condition is exactly
  `theta o L(pi(f)) = c_f o theta`.
- **Theorem 1.**  Rechecked every step.  The finitary extension exists because
  `|Y| = |pi(f)(Y)|`.  The two conjugations agree on `L(Y)`, and by induction
  their powers agree on `H`.  `(r, sigma)^N` lies in `L(X)`.  Sound.  Sanity
  checks against wreath products and freely permuted free products are
  consistent.
- **Corollary 2, Lemma 3, Corollary 4.**  Rechecked.  In Lemma 3 the normal
  form `t^-m h t^k` and the rational Mayer--Vietoris ranks are correct.
  Corollary 4's chain `e^N H e^-N <= e H e^-1 <= H` is correct.
- **`G0`.**  Rechecked the HNN elimination, Nielsen reduction of
  `{y, x y x^-1}`, Hopfian injectivity, non-surjectivity, the directed union,
  perfection via (4.1), `G0^ab = Z`, and validity of all stages.  The stage-0
  contradiction is sound and independent of the complement.  Reran
  `check_words.py` (exit 0, output identical to `output.txt`).
- **`G_u`.**  Rechecked the amalgam presentation, the kernel, the Bass--Serre
  quotient (a star, so trivial edge groups give the free product), perfection,
  local freeness, `G_Q^(n)/R = F^(n)` via the localization lemma,
  `F^(n) <= G_Q^(n)`, and triviality of the stabilizers for `n >= d+1` from
  torsion-freeness of `F^(d)/F^(d+1)`.  Sound.
- **Citations.**  Fetched the arXiv abstract pages of 2601.18742 (v1,
  2026-01-26) and math/0309121 (Borisov--Sapir: every mapping torus of a free
  group endomorphism is residually finite; Invent. Math., DOI as cited).  Both
  match.
- **Duplicates.**  `cairn search --similar` on both new ids found no
  duplicate.  Related but distinct:
  `proper-self-conjugate-subgroups-force-free-subsemigroups`,
  `finite-inclusion-is-free-self-compressor-quotient`.
- **Scope honesty.**  The target is not marked refuted, and the reading
  ambiguity is stated correctly.  The committed target's Attempt 5 already
  uses a stage with `F0 = 1` for `G(1,2)`, which is consistent with the
  deeper-stage reading.

Changed:

- Retitled `linton-halo-conclusion-fails-at-shallow-derived-stages`: "at every
  stage up to" became "at any stage up to".
- Added a stage-independence paragraph to its route.  The landed claim
  `permuted-free-product-linton-radical-gives-sofic-shell` is phrased for "the"
  shell, but its proof uses only `G/E` solvable, `R` normal and a free
  complement, so it applies at every valid stage.

Not claimed, and still open:

- whether the least halo stage `d+1` of `G_u` is always at most `|w|`, which
  matters under the reading "some `n <= |w|`" (it is plausible, but it was not
  checked);
- the existential reading of the target.

Verdict: sound; landed with minor fixes.
