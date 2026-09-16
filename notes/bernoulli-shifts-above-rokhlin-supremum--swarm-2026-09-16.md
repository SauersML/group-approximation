# Swarm attack on bernoulli-shifts-above-rokhlin-supremum-are-isomorphic (2026-09-16)

Agent: swarm-bernoulli-shifts-above-rokhlin. Lock taken on
`bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` (ttl 180m) and released at the end.

## Setup

- `G` countably infinite, `s = h^Rok_sup(G)`, assumed `< ∞`.
- `X_h` = Bernoulli shift over `G` with base Shannon entropy `h`; well defined for `h < ∞` by
  `bernoulli-shifts-with-equal-base-entropy-are-isomorphic` (Seward, arXiv:1805.08279v1, Theorem 1.1).
- `a ~ b` iff `X_a ≅ X_b`. `D(G)` = collapse subgroup, with witness sets `W_d`, as on
  `bernoulli-isomorphism-collapse-set-is-a-subgroup` (items 1–8: translation, subgroup, threshold
  `min(h, h + d) ≥ s`, common thresholds, periodicity and permanence).
- New notation: `S(G) = {h : X_h ≅ X_h × X_h}` (own-square levels), `R(G)` = non-rigid levels
  (`a` with `a ~ b` for some `b ≠ a`), `r(G) = inf R(G)`.
- Target (T1): all `X_h`, `h ∈ (s, ∞)`, isomorphic. No group with `s < ∞` is known, so everything is conditional
  on such a group; sofic groups have `s = ∞` and make the target vacuous.

## Literature gate (2026-09-16)

Web searches run:
1. "Rokhlin entropy supremum Bernoulli shifts non-sofic group isomorphism base entropy 2025"
2. "arXiv Seward "Rokhlin entropy" Bernoulli shifts "POS" "INF" countable groups 2024 2026"
3. ""Rokhlin entropy" Bernoulli shift "different entropy" isomorphic non-sofic question arXiv 2026"
4. ""Rokhlin entropy" "direct product" additivity Bernoulli Seward conjecture 2024 OR 2025 OR 2026 arXiv"
5. "isomorphism classes of Bernoulli shifts analytic set of entropies Steinhaus nonamenable group collapse arXiv
   2025 2026"

Then the WebSearch budget was exhausted; no further queries were possible.

Findings:
- No source found that constructs a group with `s < ∞`, proves isomorphism of Bernoulli shifts of different base
  entropy over any group, or studies the set of base entropies of an isomorphism class descriptively.
- arXiv:2607.11549 ("Positive Rokhlin Entropy Implies Infinite L^1-Orbit Multiplicity: A Negative Answer to
  Thouvenot's Question", July 2026). Seen only as a search snippet (unverified): about free ergodic actions of
  amenable groups. Not relevant to `s < ∞`.
- Imported sources, already used by committed nodes and not re-fetched here:
  - Seward, Krieger's finite generator theorem for actions of countable groups II, arXiv:1501.03367v4
    (Theorem 1.10 `h^Rok(L^G) = min(H(L), s)`; Theorem 1.11: if `P` has arbitrarily large finite subgroups and
    `s(G) < ∞`, then `s(P × G) = 0`; Proposition 6.5
    relative Rokhlin entropy `min(b, s)` of a split Bernoulli factor).
  - Seward, Bernoulli shifts with bases of equal entropy are isomorphic, arXiv:1805.08279v1.
  - Seward, arXiv:1602.06680v2 and arXiv:1804.05269v3 (Theorem 10.1 and Corollary 10.2: approximate extension and
    null Bernoulli factor statements).
  - Bowen, Measure conjugacy invariants for actions of countable sofic groups, arXiv:0812.2718.
- Descriptive set theory: Kechris, Classical Descriptive Set Theory (GTM 156), Sections 9, 14, 21, 29; theorem
  numbers not re-checked (unverified).

## What was proven (ESTABLISHED by check.sh, exit 0)

New claim `bernoulli-collapse-is-null-or-eventually-total`, route
`bernoulli-collapse-is-null-or-eventually-total-proof`, artifact
`research/artifacts/bernoulli-collapse-null-or-eventually-total-2026-09-16.md`.

1. **Analyticity.** `~` is analytic in `(0, ∞)^2`.
   - Geometric laws `γ_m` on `N ∪ {∞}` have entropy `φ(m) = (m+1)log(m+1) − m log m`, a homeomorphism of
     `(0, ∞)`; `h ↦ (γ_(φ^-1(h)))^G` is continuous into `Prob((N ∪ {∞})^G)`.
   - Isomorphism = projection of the Borel set of invariant couplings in which each coordinate σ-algebra is
     contained in the completion of the other; that condition is `G_δ` (approximation of clopen cylinders by
     clopen cylinders of the other coordinate). A coupling with this property is a graph joining.
   - So `D(G)`, `S(G)`, `R(G)`, all classes and witness sets are measurable and have the Baire property.
2. **Dichotomy.** Equivalent: `D(G) = R`; `D(G)` non-null / non-meager; some class non-null / non-meager; `S(G)`
   non-null / non-meager; eventual total collapse (some `M` with all `X_h`, `h ≥ M`, isomorphic). Otherwise
   `D(G)`, `S(G)`, all classes are null and meager.
   - Proof: `D(G) ∩ (0, ∞) = ∪_n {d > 0 : n ~ n + d} ⊆ ∪_n (C_n − n)`; Steinhaus / Pettis on `C_a ∩ (0, n]`
     gives all small differences, translation spreads them to `[n, ∞)`, chaining gives one class. For `S(G)`,
     `b ~ 2b` translates to `u ~ u + b`, so two own-square levels `b_1 < b_2 ≤ n` give
     `u' ~ u' + (b_2 − b_1)` for `u' ≥ 2n`.
3. **Non-rigid levels.** `R(G)` upward closed, `⊆ [s, ∞)`, non-empty iff `D(G) ≠ {0}`; a non-rigid level has an
   unbounded class, so under eventual collapse `R(G)` is one class.
4. **Criteria above the supremum** (`s < ∞`). Equivalent:
   - (T1) the target for `G`;
   - (T2) `D(G) = R` and `r(G) = s`;
   - (T3) `S(G) ∩ (s, s + ε)` non-null (or non-meager) for every `ε > 0`;
   - (T4) `X_h ≅ X_h × X_h` for all `h` in some `(s, s + η)`.
5. **Countable seeds.** The smallest translation-closed equivalence relation containing countably many seed
   pairs is inside `{(a, b) : b − a ∈ Γ_P}`, `Γ_P` countable. So seed-based constructions (finitary codes,
   `2^G ≅ 3^G`, countably many own-squares) never leave the null case.
6. **Formal independence of the halves.** Model A (`a ≈ b` iff `a = b`, or `a, b > s` and `b − a ∈ Γ`, `Γ`
   countable dense) has `r = s`, `D ≠ R`. Model B (`a ≈ b` iff `a = b` or `a, b ≥ M > s`) has `D = R`,
   `r > s`. Both satisfy translation, transitivity, analyticity and Seward's threshold.
7. **Closure principle** (artifact Section 6). If `~` is closed, two rationally independent elements of `D(G)`
   give eventual collapse; a closed `D(G)` is `{0}`, `cZ` or `R`.

## Reduction recorded

- New OPEN hole H1 `eventual-bernoulli-collapse-at-finite-rokhlin-supremum`: some `M < ∞` with all `X_h`,
  `h ≥ M`, isomorphic.
- New OPEN hole H2 `bernoulli-rigidity-threshold-equals-rokhlin-supremum`: every `h > s` is non-rigid.
- New route `above-supremum-collapse-from-eventual-collapse-and-descent`: target ⇐ H1 ∧ H2 (via (T2) ⇒ (T1)).
  Conversely the target implies both halves ((T1) ⇒ (T2)), so the split is lossless; Models A and B show neither
  half follows from the other by the product calculus.

## Side results (notes only, short and standard; not made into nodes)

- **Zero supremum ascends.** If `H ≤ Γ` and `s(H) = 0` then `s(Γ) = 0`: restricted to `H`, the Lebesgue
  Bernoulli shift over `Γ` is a Lebesgue Bernoulli shift over `H`, and an `H`-generating partition is
  `Γ`-generating.
- **Zero supremum descends at finite index.** If `[Γ : H] = k` then `h^Rok_H` of the restricted action is at most
  `k · h^Rok_Γ` (join of translates of a `Γ`-generator over a transversal), so `s(H) ≤ k s(Γ)`; in particular
  `s(Γ) = 0 ⇒ s(H) = 0`.
- **The target at `s = 0` ascends and descends.** Co-induction of `L^H` is `L^Γ`, so collapse over `H` gives
  collapse over `Γ`. Restriction of `X_a ≅ X_b` over `Γ` to `H` gives `X_(ka) ≅ X_(kb)` over `H`, and `ka, kb`
  range over all of `(0, ∞)`. So at `s = 0` the target is a commensurability invariant.
- **IBN obstruction to algebraic own-squares.** A shift-commuting continuous group isomorphism
  `F_q^G ≅ (F_q^2)^G` dualizes to an `F_q[G]`-module isomorphism `F_q[G]^2 ≅ F_q[G]`, impossible because the
  augmentation `F_q[G] → F_q` shows `F_q[G]` has IBN. So own-square witnesses are never algebraic in this sense.
- **Strong infinite-entropy form is not formal.** At `s = 0`, the relation "all finite levels one class, `X_∞`
  alone" satisfies the calculus, so (T1) does not formally give `X_h ≅ X_∞`
  (compare `bernoulli-infinite-power-iff-approximate-half-absorption`).

## Approaches tried and where each dies

1. **Countable seed isomorphisms.** Dies at item 5: the generated relation is planar-null with countable classes,
   so it never reaches the non-null case that H1 and (T1) require.
2. **Closure principle.** Would finish H1 from two rationally independent elements of `D(G)`. Dies at the lack of
   a closedness source: finite determination of Bernoulli measures fails on Thompson's `V` at supremum zero
   (`thompson-v-bernoulli-finitely-determined-iff-pos`).
3. **Baire category on i.i.d. generating partitions.** Density would give total collapse
   (`zero-supremum-collapse-via-dense-iid-generators`); dies at the spectral gap
   (`spectral-gap-refutes-exactification-on-nonamenable-groups`), and Bernoulli classes are meager on
   central locally finite hosts (`bernoulli-classes-meager-on-central-locally-finite-hosts`).
4. **Own-square tower.** Iterating `X_h ≅ X_h × X_h` yields a `G × P` action (freeness not checked), `P` a union of iterated wreath
   products of `Z/2`. Dies at transfer: `s(G × P) = 0` is already Theorem 1.11, nothing returns to `G`-classes,
   and the construction supplies only countably many isomorphisms (approach 1).
5. **Cancellation from a high collapse (for H2).** `X_(M−a) × X_a ≅ X_(M−a) × X_(a+M)` under H1; dies at
   cancelling the Bernoulli factor `X_(M−a)`, known only through entropy classification, unavailable above `s`.
6. **Witness rescaling through other groups (for H2).** Co-induction keeps witness levels; restriction to index
   `k` multiplies them by `k`, while `s(H)` versus `k s(Γ)` is only an inequality (Seward's finite-index formula
   is open, `seward-direct-product-relative-rokhlin-entropy-conjecture`). Dies because no witness moves closer to
   the new supremum by a known amount.
7. **Approximate isomorphisms.** arXiv:1804.05269v3, Theorem 10.1 and Corollary 10.2 give `ε`-approximate
   statements; dies at exactification, refuted on nonamenable groups.
8. **Invariants for a negative answer.** Rokhlin entropy `min(h, s)`, relative Rokhlin entropy `min(b, s)` and
   all semicontinuous invariants are constant above `s`
   (`semicontinuous-invariants-blind-above-rokhlin-supremum`). No obstruction to (T1) at `0 < s < ∞` is known.

## What remains open

- H1 and H2, hence the target; no isomorphism of Bernoulli shifts of different base entropy is produced over any
  group, and no group with `s < ∞` is known.
- Whether a non-trivial null `D(G)` (for instance countable) can occur; whether `r(G) ∈ R(G)`; whether `~` is
  closed.

## Weakest step

The analyticity lemma (artifact Section 1): the `G_δ` encoding of "coordinate σ-algebras agree mod `ρ`" and the
passage from such a coupling to an isomorphism, together with the unverified Kechris theorem numbers. Everything
else is elementary Steinhaus / Pettis plus translation.

## Files

- `research/bernoulli-collapse-is-null-or-eventually-total.md` (claim, established)
- `research/bernoulli-collapse-is-null-or-eventually-total-proof.md` (route)
- `research/artifacts/bernoulli-collapse-null-or-eventually-total-2026-09-16.md` (artifact)
- `research/eventual-bernoulli-collapse-at-finite-rokhlin-supremum.md` (open hole H1)
- `research/bernoulli-rigidity-threshold-equals-rokhlin-supremum.md` (open hole H2)
- `research/above-supremum-collapse-from-eventual-collapse-and-descent.md` (route to the target)

## Referee (2026-09-16)

**What I checked.**
- Read all six research files, the artifact and this note in full. I also read the committed nodes they lean on:
  `bernoulli-isomorphism-collapse-set-is-a-subgroup` (items 1, 3 and 6 are exactly (F1)–(F3)),
  `bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square`, `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`,
  `spectral-gap-refutes-exactification-on-nonamenable-groups`, `thompson-v-bernoulli-finitely-determined-iff-pos`,
  `bernoulli-classes-meager-on-central-locally-finite-hosts`, `bernoulli-entropy-counterexample-constraints` and
  `zero-rokhlin-supremum-forces-bernoulli-collapse`. Every id the new files cite exists and is committed.
- `git status` shows no unlisted files from this solver.
- **Lemma 1 (analyticity), line by line.**
  - `J` is Borel: (J1), (J2) are closed and (J3) is `G_δ`, because `ρ ↦ ρ(U)` is continuous for clopen `U`.
  - (⇒) is standard.
  - (⇐): `Σ̄_1` is a σ-algebra closed under `ρ`-limits (Borel–Cantelli step checked), so it contains all
    `Ω × E`. The graph map `T = Ψ^-1 ∘ Φ` via Lusin–Souslin is correct, and `T` is measure-preserving,
    a.e. invertible and a.e. equivariant for each of the countably many `g`.
  - `β` is continuous. `~ = (β × β)^-1(Iso)` is analytic, and so are the derived sets.
- **Theorem 2.** Checked every implication. This includes the countable-union step `D ∩ (0, ∞) = ∪ E_n`, which
  needs `h ≠ 0` for witnesses (true because `X_0` is a point), the Steinhaus/Pettis step with `b_1 ≤ n ≤ z`, and
  the own-square step giving `z ~ z + e` for `z ≥ 2n`. All correct.
- **Proposition 3 and Theorem 4.** Checked every implication. In particular (T3) ⇒ every `a > s` is non-rigid,
  and (T2) ⇒ (T1) via upward closure plus the single class `C_M`. Correct.
- **Section 5 models.** Both are equivalence relations. They satisfy (F1) and the threshold, and they separate
  the halves as stated. The countable-seed containment is correct.
- **Route to the target.** The logic is correct and the split is lossless.
- **Citations.** I fetched arXiv:1501.03367v4 and read Theorem 1.10, Theorem 1.11 and Proposition 6.5 from the PDF
  text. They match the imports: 1.11 is "`P` with arbitrarily large finite subgroups, `h^Rok_sup(G) < ∞` ⇒
  `h^Rok_sup(P × G) = 0`". I could not recheck the Kechris theorem numbers (web budget exhausted). They cover
  textbook facts (Lusin measurability and Baire property of analytic sets, Pettis, Lusin–Souslin), so the
  unverified label stays.
- **Side results in this note.** Ascent and finite-index descent of zero supremum, commensurability invariance
  of the target at `s = 0`, and the IBN argument all check out. They stay notes, not nodes.
- **Duplicates.** `bin/cairn search --similar` on the three new claims and a grep for Steinhaus, Pettis and
  eventual collapse found no duplicate. The `distinct_from` entries are adequate.

**What I changed.**
- **Artifact.**
  - Section 5 said the models satisfy "Items 1–8". Corrected to Items 1–4 and 6, since 7 and 8 concern other
    groups.
  - Section 6 called (T1) at `s = 0` "the finite-entropy strong form" of
    `zero-rokhlin-supremum-forces-bernoulli-collapse`. That strong form is `X_h ≅ X_∞`. Reworded: (T1) at `s = 0`
    is the finite-level part, between the weak and the strong form.
  - Added the Lusin–Souslin source section, marked unverified.
- **Both holes.** "Satisfies the whole product calculus" becomes the exact list: translation, transitivity,
  analyticity and the threshold.
- **H1 and this note.** Removed the unchecked word "free" from the own-square tower attempt, and quoted Theorem
  1.11 as read.

**Verdict.**
- Sound. `bernoulli-collapse-is-null-or-eventually-total` is an honest established claim, based on a complete
  argument that imports only committed claims and textbook descriptive set theory.
- The two new holes are correctly stated open halves, each with a genuine '## Attempts' section. The target
  remains OPEN.
- Landed with small fixes.
