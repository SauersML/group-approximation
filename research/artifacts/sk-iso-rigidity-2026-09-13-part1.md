# sk-iso-rigidity part 1: standardness is Peirce root recognition (2026-09-13)

Lane sk-iso-rigidity (ROSTER-H). Plan: `research/artifacts/sk-iso-rigidity-plan-2026-09-13.md`. Everything below is
UNREVIEWED and queued with sk-verify-13.

## 1. Results

**Theorem P** (`peirce-root-homomorphisms-of-e3-are-standard`, route `-proof`).
- *Setting.*
  - `R`, `M` unital rings, and `1 = E_1 + E_2 + E_3` in `M` with orthogonal idempotents `E_k` and `M E_k M = M`.
  - `α: E_3(R) → M^×` a homomorphism that maps each root subgroup `A_ij(R)` bijectively onto `P_ij = 1 + E_iME_j`.
- *Conclusion.*
  - The elements `a_ij = α(e_ij(1)) − 1` and `a_ii = E_i` form a full system of `3×3` matrix units.
  - `θ(r) = (α(e_12(r)) − 1) a_21` is a ring isomorphism `R ≅ E_1ME_1`.
  - `α` is the restriction of the ring isomorphism `Θ: M_3(R) → M`, `Θ(rE_ij) = a_i1θ(r)a_1j`.

**Corollary S** (`peirce-root-preserving-subshift-el3-isos-force-orbit-equivalence`, route
`peirce-root-preserving-subshift-el3-isos-soe-proof`).
- *Hypothesis.* An isomorphism `α: G_X → G_Y` maps the set of root subgroups onto the set of Peirce root groups of
  some decomposition `I = E_1 + E_2 + E_3` in `M_3(R_Y)` into nonzero idempotents.
- *Conclusion.* `α` is standard, possibly composed with the graph automorphism. So `M_3(R_X) ≅ M_3(R_Y)`, and `X` and
  `Y` are strongly orbit equivalent.
- *Converse.* Standard isomorphisms satisfy the hypothesis.

## 2. What this changes on the map

- **Direct finiteness is not needed.** In `root-preserving-el3-isomorphisms-give-ring-isomorphisms` (PASS) the units
  came from direct finiteness of the target. Here they come from `a_ik a_ki = E_i`, proved with fullness alone:
  - `φ_ij = a_ik a_ki φ_ij`, so `c = E_i − a_ik a_ki` kills `E_iME_j`;
  - so `cME_jM = 0`, and `cM = 0`.

  For the standard decomposition `E_k = E_kk` of `M_3(S)` fullness is automatic, so that theorem holds for every
  unital `S`.
- **The open standardness question** (`subshift-el3-isomorphisms-are-standard-over-f2`) is exactly this: an isomorphism
  `G_X → G_Y` maps each root subgroup to a Peirce root group `I + E_iME_j` of SOME decomposition of `I`, not
  necessarily a standard root subgroup.
  - The target family is closed under conjugation by `GL_3(R_Y)` and by ring automorphisms of `M_3(R_Y)`, so it is
    the natural invariant family.
  - Recognition no longer has to single out the standard matrix units.
- **What recognition must produce.**
  - Three pairwise commuting "rigid supports" `G_{E_k} = G ∩ (I + E_kME_k)`.
  - From them, the radicals `U_{E_k} = I + E_kM(I−E_k)` and `U_{I−E_k}`.
  - The roots `P_ij = U_{E_i} ∩ U_{I−E_j}`. This holds for all Peirce decompositions: `U_{E_i} ∩ U_{I−E_j}` is
    `I + (E_iM(I−E_i)) ∩ ((I−E_j)ME_j) = I + E_iME_j`.

## 3. Model tests (details in the routes)

- Identity and conjugation by `h ∈ GL_3(S)`: `a_ij = hE_ijh^{-1}`, `Θ = ` conjugation.
- The flip `fu^j ↦ fu^{-j}`, `X = (Y,S^{-1})`: standard with `E_k = E_kk`.
- **Hexagon.** For nonzero full idempotents the Peirce root groups have the same commuting hexagon as the root
  subgroups. Non-commutation uses `E_iME_l ≠ 0`, which follows from fullness.
- **Fullness is used once** (Step 1 of the Theorem P route). A vanishing Peirce space is excluded by bijectivity.
  Whether bijectivity forces fullness in general is not settled; for simple `M` it is automatic.

## 4. Credit and novelty (bounded)

- Recovering a ring from a full set of matrix units (`M ≅ M_n(E_1ME_1)`) is classical. No book locator was checked
  in this lane.
- Coordinatizing from the Steinberg relations is the sk-rigidity-f2 argument (PASS).
- The step that replaces direct finiteness by fullness, and allowing arbitrary Peirce decompositions, were not found
  in a grep of main. No literature search was run for this folklore-level step, so the credit should read
  "standard matrix-unit argument".

## 5. Next (part 2)

- **Rigid supports for all idempotents.**
  - Show `C_G(G_E) = G_{I−E}` for idempotents `E ∈ M_3(R_Y)`, `0 ≠ E ≠ I`.
  - Tool: `diag(1,1,1+n) = [e_13(n), e_31(e)] ∈ E_3(R)` for `n ∈ eR(1−e)`, valid for every idempotent `e ∈ R`.
- **Recognition candidates.**
  - Odd-order elements `x` give idempotents `ε(x) = Σ_{i<|x|} x^i`.
  - The direct factor `G_{ε(x)}` of `C_G(x)` may be recoverable from `x`.
- **Radical test.** Are the maximal abelian subgroups normalized by `G_E × G_{I−E}` exactly `U_E` and `U_{I−E}`?
