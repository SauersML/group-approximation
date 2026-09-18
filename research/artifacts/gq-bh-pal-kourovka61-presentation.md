# bh-pal-kourovka61: toward an explicit finite presentation of CT_P(Z) (Kourovka 17.61)

Lane bh-pal-kourovka61, 2026-09-18. The target is an explicit finite presentation of
`CT_P(Z)`, for finite `P`, with a literature-free proof suitable for Lean (bh-pal-scope item T8).
No priority is claimed.

## 1. What was landed

- **`class-transposition-presentation-has-central-kernel`** (ESTABLISHED, lane proof, no cited
  theorem).
  - The presentation `Γ_P`: generators `t(A,B)` for disjoint boxes, relations (R1) squares,
    (R2) conjugation when both boxes are regular, and (R3) splitting into corresponding
    `p`-children.
  - It maps onto `CT_P(Z)` with central kernel, and `Γ_P` is perfect.
  - Every `Sym(R)`, for `R` a box partition, embeds.
  - Corollary: `CT_P(Z)` is perfect, with no appeal to Matui or Li.
- **`class-transposition-relations-present-ct-p-z`** (OPEN). The kernel is trivial. This follows
  from `H_2(CT_P(Z)) = 0`; the literature pointer (Li) was not read at source.
- **`ct-p-z-has-a-finite-class-transposition-presentation`** (OPEN). A bounded-modulus truncation
  of the infinite presentation, plus the Martínez-Pérez–Matucci–Nucinkis route.

## 2. Correction to the scope artifact

`gq-bh-pal-scope.md` (T8) recommends "a direct finite presentation, generalizing Brown's
presentation of V", and says `GroupTheory/HigmanThompson/BrownPresentation.lean` exists to extend.
That file is Brown's finite presentation of `F_{m+2,∞}` (generalized Thompson `F`), per its
module docstring. It is not a presentation of `V`, and it does not present groups of cone or
box transpositions. It can still help with the `F`-part of an argument, but the repo has no Lean
presentation of `V` to extend.

## 3. Martínez-Pérez–Matucci–Nucinkis, arXiv 1609.07058 (TeX read on MSI; local copy `gq/src/mmn/`)

Line numbers refer to `mmn-1609.07058.tex`.
- l.370, Definition `sigmadef`. Colours `i` with arities `n_i > 1`, expansions `α_i` and
  contractions `λ_i`. The laws `Σ_2^{i,i'}` identify, via a bijection `φ`, the length-two
  descendants `⋃_j α_i^j α_{f(j)}` with `⋃_{j'} α_{i'}^{j'} α_{f'(j')}`.
- l.415, Definition `groups`. `V_r(Σ)` is the automorphism group of the valid Cantor algebra
  `U_r(Σ)`.
- l.1037, Theorem `finitegeneration` (valid and bounded). Finite generation by strict generators
  `(i,k,t)` and permutations `(i,σ)`.
- l.1092, Definition `complete`. Every `Σ_2^{i,i'}` is non-empty, with `f ≡ i'` and `f' ≡ i`.
- l.1118, Theorem `fp` (valid, bounded, complete; `Z^n` simply connected). This is an explicit
  finite presentation by truncating the infinite presentation `infinitepresentation`. The `Z^n`
  input comes from their Section 3 and 1309.7858 via Bestvina–Brady.

**The box model satisfies the complete laws `Σ_P`.** For a box `A = r(m)`:
- `p`-child `j`, then `q`-child `l`, is `(r + (j + p l) m)(pq m)`;
- `q`-child `j'`, then `p`-child `l'`, is `(r + (j' + q l') m)(pq m)`.

Take `φ` to match equal residues `j + p l ≡ j' + q l' (mod pq)`. Then `f ≡ q` and `f' ≡ p` for
every pair `p ≠ q`, so the laws are complete.

**Not checked here:**
- validity and boundedness of `U_1(Σ_P)` (defined in 1105.0189);
- that the box algebra is the free `U_1(Σ_P)`;
- that class transpositions generate its full automorphism group.

**If these hold**, MMN Theorem `fp` gives `CT_P(Z)` finitely presented, independently of Li. The
Kourovka answer's novelty then reduces to the identification.

## 4. Why the infinite presentation is the right intermediate step

- Relations (R1)–(R3) are local. Every relation involves at most four boxes and their children.
  The group `CT_P(Z)` acts transitively on configurations of disjoint boxes of each fixed shape,
  by canonical maps.
- So once the infinite presentation is known to present the group, a truncation to bounded
  moduli is the standard next step. The argument conjugates any relation to one among shallow
  boxes, provided the conjugation relations (R2) for deep boxes follow from shallow ones. That is
  the analogue of Bleak–Quick's passage from their infinite to their finite presentation of `V`.
- A literature-free proof of the whole chain would give a formalizable answer to Kourovka 17.61.

## 5. Handoff

Nothing is ready for a Lean lane yet. The one elementary, fully proved piece is the central-kernel
theorem (items 1–3 of its node); it is formalizable as it stands. Whether the full T8 target is
worth formalizing depends on closing `class-transposition-relations-present-ct-p-z`. A Lean lane
would formalize the MMN route only if the swarm decides to formalize literature.
