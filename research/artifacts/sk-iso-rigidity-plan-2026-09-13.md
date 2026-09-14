# sk-iso-rigidity: plan and map (2026-09-13, wave 10)

Lane sk-iso-rigidity (ROSTER-H). The note's question (rev3 on main, §4): does `G_X ≅ G_Y` force `X` and `Y` to be flip
conjugate, or at least strongly orbit equivalent? This file is a plan. Nothing here is a new established claim yet.

## 1. What main already has (review status as of tip f67054736b)

| step | node | status |
|---|---|---|
| diagonal-preserving iso ⇒ flip conjugacy | `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy` | PASS (sk-verify-3) |
| root-preserving iso ⇒ `R_X ≅ R_Y` | `root-preserving-el3-isomorphisms-give-ring-isomorphisms` | PASS (sk-verify-5) |
| root-preserving iso ⇒ SOE | `root-preserving-subshift-el3-isos-force-orbit-equivalence` | PASS (sk-verify-5) |
| `M_m(R_X) ≅ M_m(R_Y)` (or anti) ⇒ SOE | `cantor-crossed-product-matrix-ring-iso-forces-soe` | PASS (sk-verify-3) |
| every iso standard (char 2, `n = 3`) | `subshift-el3-isomorphisms-are-standard-over-f2` | OPEN |
| Cartan uniqueness in `R_X` | `subshift-crossed-product-algebraic-cartans-are-conjugate` | OPEN |

Firewalls already recorded: F-PET (Petechuk: `n = 3` exceptional in characteristic 2), F-GL (`K_1(R_X) ≅ Z`), F-MIN (no
minimal idempotents), F-EA (maximal elementary abelian 2-subgroups miss the radicals), FW-MAXAB (rows and columns
are the maximal abelian bicommutant-closed subgroups, not the roots).

So the SOE form of the question is exactly **root recognition**: show that an isomorphism carries root subgroups to
root subgroups. The flip form needs Cartan uniqueness as well, except in families where SOE already forces flip
conjugacy.

## 2. Plan

**Step 1 (Peirce coordinatization, no direct finiteness).** Let `M` be a unital ring with an orthogonal decomposition
`1 = E_1 + E_2 + E_3` into nonzero idempotents with `M E_k M = M` for each `k`, and let `R` be a unital ring. Suppose
`α: E_3(R) → M^×` is an injective homomorphism with `α(A_ij(R)) = 1 + E_i M E_j` for all `i ≠ j`. Target: then
`E_1 ~ E_2 ~ E_3` (Murray–von Neumann) and `R ≅ E_1 M E_1`. This removes the direct-finiteness hypothesis of the
reviewed root theorem, and it allows arbitrary Peirce decompositions instead of the standard matrix units. For
`M = M_3(R_Y)` it gives a Morita equivalence `R_X ~ R_Y` sending `[1]` to `[1]` in torsion-free `K_0`, hence SOE.

**Step 2 (rigid supports for every idempotent).** For an idempotent `E ∈ M_3(R_Y)`, `0 ≠ E ≠ I`, put
`G_E = G ∩ (I + E M_3(R_Y) E)`. Extend sk-rigidity-intrinsic Lemma C from diagonal `E_U I_3` to all `E`:
`span(G_E − I) = E M E`, `C_G(G_E) = G_{I−E}`, `N_G(G_E) = C_G(E)`.

**Step 3 (recognition, the crux).** Recognise the images of the three standard supports `G_{E_ii}` as rigid supports
`G_{E'_i}` of some decomposition in `G_Y`. Candidate mechanism: odd-order elements. For `x` of odd order `m`,
`ε(x) = Σ_{i<m} x^i` is an idempotent (the projection onto the fixed vectors, since `m` is odd). The centralizer
`C_G(x)` sits in `GL(εMε) × GL((1−ε)M(1−ε))^x`, and the constant elements `x_k` of order 3 on two coordinates give
`ε(x_k) = E_kk`. The question is whether the factor `G_{ε(x)}` is recoverable from `x` group-theoretically
(common refinements of direct decompositions of centerless groups).

**Step 4 (radicals and roots from rigid pairs).** Claim to test: the maximal abelian subgroups normalized by
`G_E × G_{I−E}` are `U_E = I + EM(I−E)` and `U_{I−E}`, and then `A_ij = U_{E_i} ∩ U_{I−E_j}` (as `A_ij = Row_i ∩ Col_j`).

**Step 5 (payoff).** Steps 1–4 give SOE for every isomorphism `G_X ≅ G_Y`. For Sturmian subshifts the unital ordered
`K^0` is `Z + αZ`, and SOE between two Sturmian subshifts is flip conjugacy
(`subshift-crossed-product-algebraic-cartans-are-conjugate`, Attempts), so the Sturmian family used by the note's
corollary would be classified up to flip conjugacy.

## 3. Where it can die
- Step 3: direct factors of unit groups of corners, and order-3 elements with no fixed vectors (`ε(x) = 0`).
- Step 4: twisted abelian subgroups normalized by the Levi.
- Stated honestly in part 1 if either fails.

## 4. Deliverables
- part1: Step 1 and Step 2 with complete proofs as claim nodes, queued with sk-verify-13.
- part2: Step 3 and Step 4 attempts with results or firewalls; the open nodes get Attempts.
- A proposal for the note only if the classification changes (the question paragraph belongs to sk-questions-section).
