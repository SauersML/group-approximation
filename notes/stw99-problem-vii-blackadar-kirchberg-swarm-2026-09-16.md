# STW Problem VII (Blackadar--Kirchberg): the type I case, swarm notes 2026-09-16

Agent: `swarm-stw99-problem-vii-blackadar-ki`.  Lock on
`stw99-problem-vii-blackadar-kirchberg` held during the session and released at
the end.  `check.sh` on the 10 research paths (9 nodes plus the artifact)
exited 0 against landed `8e8413bb1`.  Outcome: **reduction**.  The type I
case of Problem VII is equivalent to the K_0-embedding property for separable
QD type I algebras.  Long proofs are in
`research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md`.

## Setup

- **Problem VII.**  Is every separable nuclear stably finite C\*-algebra QD?
- **What the graph already had.**
  - The T_1 case is equivalent to the simple case.
  - The fibrewise theorem: QD-or-traceless primitive quotients force QD.
  - The QD radical criterion.
  - Brown--Dadarlat and Moutzouris imports.
  - Cor 10 of `bk-radical-projection-quotients-are-toeplitz-infinite`: a type I
    counterexample sees positivity failures only at Toeplitz-like points.
- **What was missing.**  No node isolated the *type I* case of Problem VII.  In
  that case every simple subquotient is elementary, so the entire difficulty is
  the gluing of CCR layers along singular boundary maps.

## What was proved (complete arguments in the artifact)

1. **Lemma 1 (§1), new node `separable-ccr-algebras-are-quasidiagonal`,
   ESTABLISHED.**  Let `A` be separable, with a countable faithful family of
   representations into compact operators.  Then `A` is QD.  So separable CCR
   algebras are QD, and so are type I algebras with T_1 spectrum.  The
   projections are block-diagonal finite-rank truncations.
2. **Lemma 3 (§2), per-subgroup gluing.**
   - Statement: take `0 → K⊗A → E → B → 0` with `A` QD and `B` separable,
     nuclear, QD and UCT.  If some embedding of `A` into a QD algebra kills
     `∂(K_1(B))`, then `E` is QD.
   - This re-reads the second half of BD's proof of Proposition 4.6, which uses
     the K_0-embedding property for only that one subgroup.
3. **Theorem A (§3).**  The following are equivalent:
   - (a) every separable stably finite type I algebra is QD;
   - (b) every separable QD type I algebra has the K_0-embedding property;
   - (c) circle extensions of QD type I algebras are QD iff stably finite;
   - (e) singular cyclic classes of QD type I algebras are killed by QD
     embeddings;
   - (d), via BD Theorem 4.12: the K_0-Hahn--Banach property for QD type I
     algebras.

   The new direction is (b) ⇒ (a).
   - Climb a composition series with CCR subquotients.
   - Each quotient is QD (Lemma 1), nuclear and UCT.
   - Each ideal `I_{α+1}` inherits stable finiteness from `E`.
   - Spielberg makes the boundary singular, and BD 4.6 glues.
4. **Corollary B (§4).**
   - **Single-algebra form.**  If every successive singular boundary is killed
     by a QD embedding of the ideal, then `E` is QD, with no finiteness needed.
   - **Known cases.**
     - All boundaries zero, e.g. finitely many ideals, recovering the type I
       part of `bk-projection-generated-ideals-with-uct-quotients-force-qd`
       without stable finiteness.
     - Every ideal in the series stably commutative, AF, or locally in
       Moutzouris' class `Y`.
     - T_1 spectrum.
5. **Proposition C (§5), new node
   `toeplitz-pair-algebra-is-qd-with-non-qd-irreps`, ESTABLISHED.**
   - `T' = C*(S ⊕ S*)` is the pullback of two Toeplitz algebras over
     `C(T)`, with the conjugated symbol.
   - It is QD, since `S ⊕ S*` is a rank-one perturbation of the bilateral
     shift, and it is type I.
   - Every faithful family of irreducible representations contains the two
     Toeplitz representations.
   - Consequences:
     - the fibrewise theorem does not cover all QD type I algebras;
     - quotients of stably finite type I algebras need not be stably finite;
     - `T'` should not be inner QD (Blackadar--Kirchberg abstract only);
     - Toeplitz-like points are not by themselves an obstruction.

## New graph state

- Claims:
  - `bk-type-i-stably-finite-algebras-are-qd` (OPEN);
  - `type-i-qd-algebras-have-k0-embedding-property` (OPEN);
  - `separable-ccr-algebras-are-quasidiagonal` (ESTABLISHED via direct route
    `separable-ccr-algebras-are-quasidiagonal-proof`);
  - `toeplitz-pair-algebra-is-qd-with-non-qd-irreps` (ESTABLISHED via direct
    route `toeplitz-pair-algebra-is-qd-with-non-qd-irreps-proof`).
- Routes:
  - `bk-type-i-case-via-k0-embedding`: (b) + BD imports + Lemma 1 ⇒ (a);
  - `type-i-k0-embedding-from-type-i-case`: (a) + BD imports ⇒ (b);
  - `bk-type-i-case-from-uct-quotient-extensions`:
    `blackadar-kirchberg-for-uct-quotient-extensions` + Lemma 1 ⇒ (a).

The two OPEN claims form an equivalence cycle.  Neither feeds upward to the
root, since the type I case does not imply Problem VII.  They are recorded as
the canonical formulation of the type I sub-question.

## Approaches to (b) and where they die (artifact §6)

- **Reductions that work.**
  - Stable isomorphism invariance.
  - Unitization.
  - Finitely generated subgroups, and local approximation
    (`moutzouris-k0-killing-is-local`).
- **Lemma 4 (sketch).**  Let `A` be CCR and `x ∈ K_0(A)`, and put
  `r_x(π) = π_*(x) ∈ Z` on `Â`.
  - If `r_x` takes both signs, the semigroup generated by its values is a group.
    Direct sums of compressions of irreducibles, which are asymptotically
    multiplicative because the images are compact, then kill `x`.
  - The same holds if `r_x` vanishes on a dense set.
  - BD Theorem 4.12 converts this into a killing QD embedding.
  - The rank identification `(Q π Q)_*(x) = r_x(π)` is only sketched.
- **Death (α).**  Take `A = C(S²) ⊕ C` and `x = (β, 1)`.
  - `x` is singular, `r_x ≥ 0`, and the zero set `S²` is not dense.
  - Every norming sum of compressions gives a positive integer.
  - Killing needs fuzzy-sphere almost-representations with negative Bott index
    (folklore, Loring; not checked).
  - BD assert the commutative case, so `x` is killable, but not by rank
    functions.
  - The first genuinely open test case is a continuous-trace algebra with
    non-torsion Dixmier--Douady class.  It was not analysed.
- **Death (β).**  At Toeplitz points compressions are not almost multiplicative
  (defect `1`).  By Proposition C such points occur in QD type I algebras.
- **Death (γ).**  Permanence of the K_0-embedding property under extensions is
  exactly the gluing problem, so the attempt is circular.
- **Death (δ).**  Top-down induction fails, because quotients lose stable
  finiteness (Proposition C).

## Weakest points (for the referee)

1. **Lemma 3.**  It re-reads BD's proofs of Proposition 4.6 and Theorem 3.4.
   - The algebra `E(η)` over the σ-unital hereditary `J ⊆ Π M_n + K` need not
     be separable.  BD's Proposition 2.5 is quoted as needing only a σ-unital
     ideal and a separable quotient.
   - The route `bk-type-i-case-via-k0-embedding` does not need Lemma 3.  It uses
     BD 4.6 as a black box.
   - Corollary B (single-algebra form) and (e) ⇒ (b) do need Lemma 3.
2. **(U1), the UCT realisation of a prescribed boundary.**  It is quoted
   verbatim from BD's proof of 4.6, and not re-derived.
3. **Textbook facts.**
   - Type I algebras are nuclear and UCT; composition series with CCR
     subquotients; permanence of type I.
   - The Weyl--von Neumann--Berg theorem.
   - Irreducible representations of an algebra containing `K ⊕ K`.
   - Theorem numbers were not re-checked.
4. **Addendum (d).**  It uses BD Theorem 4.12 (individual algebra), which is not
   an imported node.
5. **The "not inner QD" remark.**  It rests on the Blackadar--Kirchberg abstract
   only.

## Literature (gate done 2026-09-16)

- **Brown--Dadarlat, arXiv:math/0008182.**  The TeX source was read.  Section 4
  lists commutative, AF, AF ⋊ Z and unique-trace simple algebras as having the
  K_0-embedding property, with no type I statement.
- **N. P. Brown, survey arXiv:math/0008181.**  TeX and ar5iv were read.  It has
  no type I quasidiagonality results.  Proposition 10.10 quotes Spielberg's
  criterion.
- **Moutzouris, arXiv:2112.03224v3.**  The HTML was read; the PDF was
  unparseable.  Its known cases of the conjecture are simple UCT, traceless,
  and AH real rank zero crossed by `Z`.  Its class `Y` covers ASH algebras and
  minimal crossed products.  It does not mention type I.
- **Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Only the abstract page
  was read (v2, 8 May 2026).
- **Ozawa, arXiv:2609.08892 (8 Sep 2026).**  The abstract was read.  It concerns
  MF algebras and the hyperfinite II_1 factor, and does not touch this case.
- **Blackadar--Kirchberg, arXiv:0711.4949.**  The abstract was read: inner QD
  iff a separating family of QD irreducible representations exists.  An
  automated query over the ar5iv body found no type I or residually stably
  finite statements.  The PDF text could not be extracted locally.
- **H. Yao, Canad. Math. Bull. 59 (2016).**  The abstract page was read.  It is
  about stably finite extensions of real rank zero algebras; not relevant.
- **Not fetched (unverified).**
  - Spielberg, JFA 81 (1988): ScienceDirect returned 403.
  - Berg, Trans. AMS 160 (1971).
  - Rosenberg--Schochet, Duke 55 (1987).
  - Dixmier; Pedersen; Brown--Ozawa.
  - Loring on fuzzy spheres.
- **Prior-art risk.**  Spielberg's JFA 81 (1988) paper (title recalled as
  *Embedding C\*-algebra extensions into AF algebras*, unverified) could not be
  reached: ScienceDirect returned 403
  and the Semantic Scholar API returned 429.  It may contain AF-embeddability
  results for type I extensions, which would be special cases of (b).  The OPEN
  status of `bk-type-i-stably-finite-algebras-are-qd` rests on four things:
  - Moutzouris' 2021 list of known cases does not mention type I;
  - Brown--Dadarlat do not mention it;
  - Brown's survey does not mention it;
  - the graph records no such result.

  It does not rest on a full literature sweep.
- **Search result.**  No 2024--2026 source found in this session settles Problem
  VII or its type I case.  The WebSearch budget ran out before an exhaustive
  arXiv sweep for "type I quasidiagonal stably finite", so this negative search
  is not exhaustive.
