# Swarm attack on subshift-crossed-product-algebraic-cartans-are-conjugate (2026-09-16)

Agent: swarm-subshift-crossed-product-algeb. Lock held on the target claim during the attack.

## Setup

- Target (U): every algebraic Cartan subalgebra of `R_X = LC(X,F_2) ⋊ Z` is `β(D_X)` for a ring automorphism `β`.
- Established reduction (`cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity`): (U) iff (D1) every Cartan model
  carries a fibre-bijective `Z`-cocycle, and (D2) ring rigidity among subshifts.
- The claim file listed three deciders: (a) a non-spatial isomorphism between SOE non-flip-conjugate subshifts,
  (b) prove (D1) and (D2), (c) decide whether the dihedral Sturmian groupoid algebra
  `LC(X_α × Z/2, F_2) ⋊ D_∞` is isomorphic to some `R_Y` (a yes refutes (U) at `Y`).
- Hole attacked: decider (c), plus the general orientation obstruction it suggests.

## Result (decider (c) settled negatively)

Details and full proofs: `research/artifacts/dihedral-cantor-k1-exponent-four-2026-09-16.md`.
Answer: no. The dihedral Sturmian groupoid algebra `LC(X_α × Z/2, F_2) ⋊ D_∞` is isomorphic to no matrix ring over any
`R_Y` with `Y` infinite minimal Cantor. So this test object gives no counterexample, and the target stays OPEN.

## What was proven

- **Lemma 1 (artifact §1).** Let `A ⊇ A′` be `F_2`-algebras and `v` a unit with `vA′v^(−1) = A′`, `v² ∈ A′` and
  `A = A′ ⊕ A′v`. Then `i_* ∘ tr = 2` on `K_1(A)`.
  - The kernel of `A ⊗_(A′) A → A` is `A(1⊗v + v⊗1)`. It is twisted by the inner automorphism `Ad v`, hence
    isomorphic to `A` as a bimodule, and additivity of `K_1` does the rest.
  - Exact bimodule identities were checked on `F_2^(Z/n) ⋊ D_n`: `experiments/dihedral-cantor-k1-exponent-four-2026-09-16/bimodule_check.py`.
- **Theorem 2 and Corollary 3 (claim `dihedral-cantor-crossed-product-k1-has-exponent-four`).** Let `(Y,S)` be infinite
  minimal Cantor and `P` an involution with `PSP = S^(−1)`.
  - `4·K_1(LC(Y,F_2) ⋊ D_∞) = 0`: the reflection inverts the generator `[δ_S]` of `K_1(A′) ≅ Z`
    (`binary-subshift-ring-k1-is-half-orbit-index`).
  - So `M_m(A) ≇ M_n(R_X)` for every infinite minimal Cantor `X`.
- **Lemma 4a, Corollary 4, Lemma 4b (claim `dihedral-sturmian-groupoid-algebra-is-no-subshift-ring`).**
  - If `T²` is minimal, the doubled rotation `T′` on `X × Z/2` is minimal, so Corollary 3 applies to the dihedral
    groupoid algebra.
  - For Sturmian `X_α`, self-contained proofs by uniform recurrence of rotation by `α` and `2α` show:
    `(X_α,T)` is an infinite minimal Cantor system, the reversal preserves `X_α`, and `T²` is minimal.
- **Proposition 5 (artifact §5).** Let `G ⊇ H` be clopen and wide, with a compact open full bisection `B`
  (`G = H ⊔ HB`, `BHB^(−1) = H`, `BB ⊆ H`). If `Ad(1_B)` acts by `−id` on `K_1(A_(F_2)(H))`, then
  `4·K_1(A_(F_2)(G)) = 0`.
  - For `H = Z ⋉ Y` the action is `I(γ_B)`, the Giordano–Putnam–Skau index of the full-group element of `B C_S B^(−1)`.
  - So no Cartan model of `M_n(R_X)` has an index-two structure `(H, B)` with `Ad(1_B)_* = −id` on `K_1(A_(F_2)(H))`;
    for `H = Z ⋉ Y` this is exactly the orientation-reversing case `I(γ_B) = −1`.
- **Weak points flagged for the referee.** The argument depends on the established but unreviewed input
  `binary-subshift-ring-k1-is-half-orbit-index` (`K_1(R_X) ≅ Z`). Inside Lemma 1, the step to check most carefully is
  the identification of `i_* tr(α)` with `id ⊗ α` on `(A ⊗_(A′) A) ⊗_A A^n`, followed by additivity along the
  right-split bimodule sequence.
- **Edit to the target claim.** Its "Test object for (D1)" bullet and decider (c) now record the negative answer,
  pointing to the new claim.

## Approaches tried and where they die

- **Free-product / Pimsner–Voiculescu computation of `K_1(LC(X′,F_2) ⋊ D_∞)`** through `D_∞ = Z/2 * Z/2`. This dies,
  or at least becomes expensive.
  - The algebraic analogue needs Waldhausen's free-product K-theory with Nil terms.
  - The coefficient rings `LC(X′,F_2) ⋊ Z/2` are not regular crossed products at the palindromic (fixed) points.
  - It was abandoned for the transfer argument, which needs no computation of `K_1(A)` at all.
- **Characteristic `≠ 2`.** The transfer gives `x + θ′_*(x)` rather than `2x`, so there is no torsion bound. The
  argument is specific to `F_2`, which is the target's field.
- **Toward (D1) in general.** The obstruction only sees a global clopen index-two subgroupoid with a full bisection.
  - A hypothetical Cartan model with isotropy on a nowhere dense set, but no such global structure, is untouched.
    Lemma 1 has nothing to act on there.
  - Orientation-preserving extensions (`I(γ_B) = +1`) give no `K_1` obstruction. The commuting case is a `Z`-action
    groupoid anyway (sketch, artifact §5 remark).
- **(D2)** was not attacked.

## Literature consulted (2026-09-16)

- WebSearch was unavailable (session search budget exhausted).
- The arXiv API (`export.arxiv.org`) returned connection resets and HTTP 429 during the final pass. The queries made
  before a context compaction produced nothing decisive, and their result lists were not retained, so none of them is
  cited.
- **arXiv listing search (`arxiv.org/search`)**, fetched 2026-09-16:
  - "Cartan Steinberg algebra crossed product" and "Cartan subalgebras Steinberg algebras uniqueness isomorphism":
    only arXiv:2101.09730 and arXiv:2411.15924.
  - "algebraic Cartan pair ring": includes arXiv:2411.15924 and arXiv:2301.04459 (Bruce–Li, title only).
  - "K-theory crossed product infinite dihedral group": no results.
- **Abstracts fetched and read** (2026-09-16):
  - B. Steinberg, *Diagonal-preserving isomorphisms of étale groupoid algebras*, arXiv:1711.01903 (Nov 2017). This is
    reconstruction from diagonal-preserving isomorphisms, which says nothing about non-conjugate Cartans.
  - T. M. Carlsen, E. Ruiz, A. Sims, M. Tomforde, *Reconstruction of groupoids and C*-rigidity of dynamical systems*,
    arXiv:1711.01052, Adv. Math. 390 (2021) 107923. This is graded or equivariant diagonal-preserving rigidity.
  - J. H. Brown, L. O. Clark, A. H. Fuller, *Intermediate subalgebras of Cartan embeddings in rings and C*-algebras*,
    arXiv:2411.15924 (Nov 2024). It gives a lattice isomorphism between wide open subgroupoids and intermediate
    quasi-Cartan subalgebras, which is consistent with using `A_(F_2)(H) ⊆ A_(F_2)(G)` in Proposition 5.
- **Recalled, not fetched, and not used as proof inputs:** Giordano–Putnam–Skau (1995), Bass–Heller–Swan,
  Stallings/Gersten/Waldhausen free-product K-theory, Natsume-type sequences for `C*(Z/2 * Z/2)`.
- **Verdict.** No source found treats Cartan uniqueness for `LC(X,F_2) ⋊ Z` or `K_1` of dihedral Cantor crossed
  products over `F_2`. The arguments here are elementary and appear new in this form.

## Next steps suggested

- Decider (a), a non-spatial ring isomorphism between strongly orbit equivalent non-flip-conjugate subshifts, and (D2)
  remain the live routes to a counterexample.
- For (D1), the natural extension is the homomorphism `ind ∘ (C ↦ 1_C): [[G_B]] → Z` on the topological full group of a
  Cartan model. Is it given by a continuous cocycle, and is that cocycle fibre-bijective?
- Also for (D1): can a Cartan model of `R_X` have nontrivial isotropy at all? Proposition 5 excludes only the
  orientation-reversing global index-two case.
