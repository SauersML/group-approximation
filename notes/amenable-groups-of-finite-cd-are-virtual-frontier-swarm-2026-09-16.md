# Kropholler's question: frontier swarm lane, 2026-09-16

- **Lane:** `hi-fron-amenable-groups-of-finite-cd-a` (FRONTIER angle).
- **Root:** `amenable-groups-of-finite-cd-are-virtually-solvable`.
- **Proof artifact:** `research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md`.

## Angle

The root had no routes and one deferral in its Attempts section. The frontier angle was to find the
current edge of what is known, which is Degrijse's dimension-2 theorem under a zero-divisor
hypothesis. From there:

- split the root at that hypothesis;
- push the dimension-2 proof into dimension 3;
- record where it stops.

## State of the art as of 2026-09-16

Details and dates are in artifact Section 8.

- **Degrijse, arXiv:1609.07635 (Math. Ann. 386 (2023)).**
  - Theorem A: an amenable group with domain `Z[G]`, `cd n` and type `FP_{n-1}` is of type FP.
  - Theorem B: an amenable group of cd 2 with domain `Z[G]` is solvable, hence `BS(1,m)` or a
    noncyclic subgroup of `Q`.
  - The introduction states the question ("brought to the authors attention by Peter Kropholler").
- **The elementary amenable case is settled:** Hillman, Lemma 2, together with Hillman–Linnell,
  Corollary 1.
- **Hillman, arXiv:2102.02947 (J. Group Theory 27 (2024)),** as rendered by ar5iv. It classifies
  torsion-free elementary amenable groups of Hirsch length 3, and its Corollary 9 gives the cd-3,
  finitely presented ones. It is about groups already known to be elementary amenable.
- **Kropholler–Linnell–Lück, math/0401312:** finitely generated elementary amenable groups of
  cd at most 2 have a finite 2-dimensional model.
- **Emmanouil–Golfis–Ren, arXiv:2608.22386 (v2, 8 Sep 2026):** Gorenstein dimensions and Hirsch
  length. The abstract does not touch the question.
- **Status.** Web searches on 2026-09-16 found no resolution. The query strings were not preserved,
  and the search budget ran out mid-gate. This is evidence of openness, not proof.

## What was established

All statements are proved in the artifact from cited theorems. No novelty is claimed.

1. **The split (Section 1).**
   - The root is equivalent to H1 ∧ H2:
     - H1 = `amenable-finite-cd-integral-group-rings-are-domains`;
     - H2 = `amenable-finite-cd-domain-groups-are-virtually-solvable`.
   - Only the direction H1 ∧ H2 ⇒ root is a route (`kropholler-question-via-zero-divisor-split`).
   - Kaplansky over `Q` gives H1 (route `amenable-finite-cd-domains-via-kaplansky`).
   - In cd 2 the root is equivalent to H1.
2. **Reduction to finitely generated groups (Section 2).**
   - Each of the root, H1 and H2 reduces to finitely generated groups.
   - Linear amenable groups of finite cd are virtually solvable, via Tits.
3. **Anatomy of Degrijse's proof (Section 3),** with verbatim quotes and the dimension-specific steps
   B1, B2 and B4 marked.
4. **Proposition 4.1 (fibred cd 3).**
   - Statement: `G` amenable of cd 3 with domain `Z[G]`, and some map onto `Z` with kernel of type
     `FP_2`. Then the kernel is `BS(1,m)` and `G` is solvable of derived length at most 3.
   - Key Lemma 4.2: if `N` is of type FP with cd `m`, then `cd(N ⋊ Z) = m + 1`. The proof uses LHS
     and an induced-module computation of `H^1(Z; H^m(N; ZG))`.
5. **Proposition 5.1 (`PD_3`).** An amenable `PD_3` group with domain group ring and positive
   virtual `b_1` is virtually solvable (Strebel plus Theorem B plus Hillman–Linnell). Hillman's Q16
   asks whether every `PD_3` group has positive virtual `b_1`.
6. **Proposition 6.3.** For cd 3, type `FP_2` and `b_1 > 0`, if the Bieri–Strebel base has cd at
   most 2, then `G` is solvable.
7. **Proposition 7.1.** A torsion-free group acting faithfully and micro-supportedly on a Hausdorff
   space without isolated points has infinite cd. This generalizes the line version already in the
   graph, and it excludes torsion-free weakly branch groups and Thompson-type actions as
   counterexamples.

## Approaches tried, and exactly where each stops

- **Transplanting Degrijse's proof to cd 3.**
  - **B1.** Finite generation is not `FP_2`. Counterexample: `Z[1/6] ⋊_{2/3} Z` is finitely
    generated, cd 3, solvable, and not `FP_2` (Section 6.1, proved directly).
  - **B2.** A vanishing Euler characteristic does not give `b_1 > 0`. Counterexample: the
    Hantzsche–Wendt group.
  - **B4.** In an ascending HNN extension with cd-3 base `K`:
    - (G1) the MV argument needs `α` onto `H^2(K; ZG)`, and one-endedness says nothing in
      degree 2;
    - (G2) `K` is only finitely generated.
  - A grading argument proves `cd(K *_φ) = cd K + 1` for a type-FP base, but only when `β`
    (restriction to `φ(K)` followed by conjugation) is injective in the top degree. Question
    **(Q-a)** asks whether this holds in general.
- **Fibred case with a finitely generated, non-`FP_2` kernel of cd 3.** Lemma 4.2 needs type FP.
  `BS(1,2) ⊇ Z[1/2]` shows a non-FP kernel can have `cd(N ⋊ Z) = cd N`, although that kernel is not
  finitely generated. This subcase is open.
- **H1 directly.** Every positive mechanism found needs elementary amenability, linearity, or full
  Kaplansky. Amenability gives only an Ore condition once the ring is known to be a domain. There is
  no attack.

## Next steps, most promising first

1. **(Q-a), and whether the Bieri–Strebel base can be taken of type `FP_2`.** Read Brown–Geoghegan,
   Comment. Math. Helv. 60 (1985), Theorem 0.1, for the degree in which `α` is injective. Answering
   both would close case 4 of H2 (cd 3, `FP_2`, `b_1 > 0`) without assumptions on the base.
2. **A cd-3 analogue of Theorem A from finite generation plus something weaker than `FP_2`.** Section
   6.1 shows finite generation alone is not enough.
3. **Hillman's Q16 for amenable `PD_3` groups.** With Proposition 5.1 it would give H2 for all
   amenable `PD_3` groups with domain group ring.
4. **Fibred case with a finitely generated kernel.** Is `cd(N ⋊ Z) = cd N + 1` for finitely
   generated `N`?

## Files

- `research/amenable-finite-cd-integral-group-rings-are-domains.md` (claim, OPEN)
- `research/amenable-finite-cd-domain-groups-are-virtually-solvable.md` (claim, OPEN)
- `research/kropholler-question-via-zero-divisor-split.md` (route to the root)
- `research/amenable-finite-cd-domains-via-kaplansky.md` (route from Kaplansky to H1)
- `research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md`
