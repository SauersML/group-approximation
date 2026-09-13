# The unit-group face of the UN dichotomy: MF quotients of GL_n over Steinberg algebras

Lane `un-k1-homology`, 2026-09-13. Everything here is unreviewed. Inputs already on main are cited by node id.

## 1. The question

The non-MF paper's Theorem l.1218 says: for a countable purely infinite simple ring `R`, every homomorphism from
`GL_n(R)` to an MF group factors through `κ_n : GL_n(R) → K_1(R)`. The Pestov answer's ring `LC(X,F_q) ⋊ ℤ` embeds
in a matrix ultraproduct. What does MF approximation see of the full general linear groups over Steinberg
algebras, on each side, and how does it read in terms of the groupoid?

## 2. Paradox extreme: the MF quotient is K_1

`purely-infinite-steinberg-gl-max-mf-quotient-is-k1`. The dynamical hypothesis is **(PI) local
compressibility**: every nonempty compact open `A ⊆ X` is the source of two compact open bisections with disjoint
ranges inside `A`.
- For minimal effective 𝒢, (PI) makes every `1_A` properly infinite.
- Larki's Thm `thm3.4` turns that into a purely infinite Steinberg algebra. Minimality makes strongly effective
  the same as effective, and Steinberg's theorem makes the algebra simple.
- `purely-infinite-canonical-k1-all-ranks` then gives `Rad_MF(GL_n) = [GL_n, GL_n]`, with quotient `K_1`.

## 3. Finite graphs: an explicit formula

`irreducible-sft-leavitt-gl-max-mf-quotient-formula`. For finite, cofinal, sink-free graphs with condition (L),
ABC Cor 7.7 gives the maximal MF quotient of `GL_n(L_k(E))`:

`(Coker(1 − N^t | ℤ^(E^0)) ⊗ k^×) ⊕ Ker(1 − N^t | ℤ^(E^0))`.

| graph | `1 − N^t` | maximal MF quotient of `GL_n` |
|---|---|---|
| rose `R_d` | `1 − d` | `k^×/(k^×)^(d−1)` (Cor l.1297; 0 for `d = 2`) |
| golden mean `[[1,1],[1,0]]` | det −1 | 0: perfect, no nontrivial MF quotient |
| `[[2,1],[1,2]]` | rank 1 | `k^× ⊕ ℤ` |

For the SFT groupoid `G_A` of an irreducible non-permutation 0–1 matrix, Matui's Thm `CKHomology`
(`matui-sft-groupoid-homology-is-k-theory`) plus Cuntz's `K_*(O_A)` (recalled) read this as
`(H_0(G_A) ⊗ k^×) ⊕ H_1(G_A)`. So MF approximation of `GL_n` detects groupoid homology in degrees 0 and 1, with
`H_0` carrying the coefficient units. Whether this holds for every locally compressible minimal groupoid is the
open claim `steinberg-gl-max-mf-quotient-is-low-degree-homology`.

## 4. Measure extreme: nothing is lost

`exactly-matricial-rings-have-lef-general-linear-groups` (un-converse) gives `GL_n(R)` LEF whenever `R` embeds
unitally in a matrix ultraproduct over fields. Examples: the Pestov ring, the residually finite crossed products
of `residually-finite-actions-give-matricial-crossed-products`, and the Toeplitz free-group family. So
`Rad_MF(GL_n) = 1`.

## 5. The two extremes as one statement

`steinberg-gl-mf-radical-is-commutator-or-trivial`. The MF radical of `GL_n(A_k(𝒢))` is the whole commutator
subgroup under (PI), and trivial under exact matricial embeddability, and the hypotheses exclude each other.
The contrast is sharp:
- **Paradox side.** MF approximations of `GL_n` factor through an abelian group: `K_1`, pure homological data.
- **Measure side.** They see all of `GL_n`.

The elementary groups `EL_n` sit inside `[GL_n, GL_n]` on the paradox side and have no MF quotient at all
(Cor l.1016 and `no-invariant-measure-steinberg-elementary-no-mf-quotient`). On the measure side they are LEF.

## 6. Boundaries and open ends

- **Not exhaustive.** Groupoids with neither (PI) nor matricial models form the middle. The decider in the UN
  graph is Labbé's ℤ²-SFT crossed product (`labbe-wang-shift-crossed-product-is-exactly-matricial` and its
  negation; `matricial-aperiodic-sft-rings-are-not-quantum-rigid`). There the MF radical of `GL_n` is
  undetermined.
- **(PI) vs no invariant measure.** (PI) is stronger than having no invariant probability measure. Minimal
  groupoids with no invariant measure but without (PI) at every compact open set need un-middle's rank threshold
  instead of the ring classification.
- **General homological formula.** It is open; attempts and firewalls are in
  `steinberg-gl-max-mf-quotient-is-low-degree-homology`.

## 7. Sources read verbatim this lane

- Matui arXiv:0909.1624, TeX `htfgeg.tex` lines 1043–1110 (Thm `CKHomology` and its setting).
- Larki arXiv:1901.07094, TeX line 120, the definition of strongly effective. The theorem is already imported by
  un-prior-art.

Recalled only: Cuntz's `K_0(O_A) = Coker(1 − A^t)` and `K_1(O_A) = Ker(1 − A^t)`; Scarparo and Deeley on
failures of HK.
