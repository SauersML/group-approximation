# EX review, groups: part 15. Eighteen-relator tests, exclusions from amenable orbit full groups, Lodha–Moore orders, Serre atoms

Lane `ex-verify-groups`, 2026-09-13, ~02:35 CDT. Index: `ex-review-groups-2026-09-12.md`. These are the
remaining established claims of the original lanes with nontrivial proofs. Citation-only imports are left
for a later part.

## 15.1 ex-free-objects: `eighteen-relator-system-is-hamming-rigid`. PASS

- **Compactness.** If the claim fails for `ε`, there are degrees `n_k` and permutations with relator defects
  `<= 1/k`. Some fixed generator `g_0` has `d_H > ε` along a subsequence.
- **Ultraproduct.** The relators die in `G_ω = ∏_ω Sym(n_k)/N_ω`, so `Q -> G_ω` exists, and the image of
  `g_0` is nontrivial. `Q` is simple, so the map is injective. Elek–Szabó then makes `Q` sofic, which
  contradicts `openai-leavitt-unit-nonsofic`.
- **Bounded degrees** need no separate case. Then `G_ω` is a finite symmetric group, and an infinite simple
  group has no nontrivial finite image.
- **Exact solutions in a sofic group.** The image is a quotient of a simple group, so it is trivial or `≅ Q`,
  and `Q` is not sofic.
- **Not re-derived.** Completeness of the Thompson–Steinberg presentation, owned by ex-verify-presentation.

## 15.2 `leavitt-hyperlinearity-eighteen-relator-unitary-test`. PASS

- **(2 ⇒ 1).** The classes kill the relators in `U_ω`, the image of `x` is nontrivial, and simplicity makes
  the map injective.
- **(1 ⇒ 2).** `lim_ω ||X_k - I||_2 = c_0 > 0`, and a diagonal extraction over `ω`-large sets gives condition 2.
- **Variants.** Every generator is nontrivial in `Q`, so any one of them, or all four at once, can be kept
  away from `I`.
- **Scope.** The node claims the equivalence only, and says which side holds is open. The word-length
  count 322 was not checked.

## 15.3 `eighteen-relator-kazhdan-group-with-full-mf-radical`. PASS

- It transfers isomorphism invariants through the presentation isomorphism. The import
  `binary-leavitt-all-ranks-full-mf-radical` is cited in part 1.
- **Finite-dimensional representations.** This item also follows directly. A nontrivial representation
  would be injective, and Malcev makes a finitely generated linear group residually finite.
- **Note on the closing remark, not the claim.** It says eliminating `c` by Tietze would keep "the same
  eighteen relators". The count depends on how `c` is expressed. The graph's three-generator presentation
  has sixteen relators (`thompson-steinberg-three-generator-presentation`).

## 15.4 ex-fp-simple-sofic: `irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups` (requires: []). PASS

- **Item 1, action on `Z`.**
  - `c_(gh)(y) = c_g(hy) c_h(y)` gives `(gh).z = g.(h.z)`.
  - Each fibre map is a bijection of `{λ : λx ∈ Y}`, so `m` is preserved.
- **Følner vectors.** The escape set of `ξ_Q` under `k` has measure at most `Σ_(e ∈ E) |eQ \ Q|`.
- **Freeness on `Z`.** Fixed points of `g` project to `Fix g ∩ Y`, a null set.
- **Fundamental domain.**
  - The orbit of `(x, λ)` is `{(x, λ') : λ'x ∈ Γλx}`, and least index picks one point.
  - Then `L^2(Z) ≅ L^2(D) ⊗ ℓ^2(Γ)` with `π ≅ id ⊗ λ_Γ`. The fibre norms `f_n` are almost invariant by the
    reverse triangle inequality, and Hulanicki–Reiter makes `Γ` amenable.
- **Item 2.**
  - `Stab` is Borel and equivariant, and ergodic components push forward to ergodic IRSs.
  - Both allowed values give `μ_e(Fix g ∩ Y) = 0`.
- **Not checked.** The Elek–Monod model-test remark.

## 15.5 `stabilizer-rigid-groups-avoid-amenable-orbit-full-groups`. PASS

- **Step 1.** Positive definiteness follows from `Σ_y |Σ_i c_i [g_i x = y]|^2 >= 0`.
- **Step 2.**
  - The GNS space of `s 1 + (1-s) δ_1` sits inside `1 ⊕ λ`.
  - The differences `δ_g - δ_h` span a dense subspace because `Γ` is infinite, so the GNS space has an
    invariant vector.
  - An invariant `ℓ^2` function on orbits forces finite orbits, and simplicity turns them into fixed points.
- **Step 3.** On `Y` the character is `φ_0`. **Step 4** is 15.4, item 1.
- **V is not amenable.** The two named elements suffice.
  - `00 -> 0, 01 -> 10, 1 -> 11` gives `μ[0] = μ[00]`, so `μ[01] = 0`.
  - The first-letter flip gives `μ[11] = μ[01] = 0`.
  - The first element gives `μ[1] = μ[11] = 0`, and the flip gives `μ[0] = μ[1] = 0`.
  - The node's sentence skips the middle step.
- **Topological full groups.** With full support, a nontrivial homeomorphism moves a set of positive measure.
- **Not re-checked.**
  - The scope sentence that every SFT full group listed in `fp-infinite-simple-amenable-group` contains `V`.
    The purely infinite ones are covered by 15.6, item 3.
  - The Dudko–Medynets reading of `thompson-v-character-simplex` (Corollary 3.6(2)). It agrees with the
    lane's independent TeX reading of Theorem 2.9 in 15.6.

## 15.6 `no-proper-character-groups-avoid-amenable-orbit-full-groups`. PASS

- **Item 1.** On the weak*-compact character set with two extreme points, Krein–Milman gives (CR).
- **Item 3, non-amenability.** Import `amenable-full-group-forces-invariant-measure`, checked here:
  - `abab` on `E -> U(E) -> VU(E)` is the 3-cycle restricting to `U`;
  - Markov–Kakutani gives an invariant measure;
  - fixed germs go through `U = (UW^-1) W`;
  - minimality gives full support, and then `μ(A) >= 2 μ(A)`.
- **Item 4, Thompson's `T`.**
  - `R = F'` is the subgroup supported in closed arcs avoiding `0`.
  - Hypothesis (ii): the conjugates `h_i g h_i^-1`, with `h_i ∈ R` supported in `I` and `I ∩ g(I) = ∅`, have
    differences supported in `I ∪ g^-1(I)`.
  - They are distinct, because a commuting `c` supported in `I` has support in `I ∩ g(I) = ∅`.
  - Non-amenability: the dyadic rotations force Lebesgue measure through Fourier coefficients, and
    slope-2 elements do not preserve it.
- **Item 5.** A nontrivial realization of a simple group is injective, so it restricts to one of `T`.
- **Trust surface.** The Dudko–Medynets, Gardella–Tanner and Lodha TeX line readings were done by the lane
  on MSI and not re-read here. Nekrashevych simplicity is an import.

## 15.7 ex-left-orderable-nonsofic: `lodha-moore-group-is-bi-orderable-and-not-lea` (requires: []). PASS

- **Germ order at the leftmost moved point.**
  - The semigroup cases `m_f < m_h`, `m_h < m_f` and `m_f = m_h`, including `m = -∞`, all check.
  - So do trichotomy and conjugation invariance, via `m_(gfg^-1) = g(m_f)`.
  - Elements of Monod's `H` are piecewise `PSL_2(R)`, hence orientation preserving.
- **Chain of order properties.** Bi-orderable ⇒ locally indicable ⇒ left-orderable ⇒ unique products.
- **Not LEA.**
  - For a finitely presented group, LEA gives residual amenability through a window of relator prefixes.
  - Burillo–Lodha–Reeves (every proper quotient is abelian) prevents separating any `c ≠ 1` in `G_0'`.
- **Trust surface.** Abstracts only, as the node says.

## 15.8 ex-determinant-monster: `serre-class-admits-non-integral-atoms`. PASS

- **Convention.** The class integrates `log|Q|` off the zero set of `Q`, as in
  `integer-root-limits-are-galois-balanced-serre-measures` (parts 5 and 6).
- **Potential.** Rescaling `[-2,2]` gives `U_R(ζ) = log(R/2) + log|u| >= log(max(R, |ζ|)/2)`. So
  `I_R(Q) >= deg Q · log(R/2)`.
- **`μ_1`.** `2^(deg Q) Q(1/2)` is a nonzero integer, which cancels the `log 2` exactly.
- **`μ_2`.**
  - The sup bound is `log|Q(z)| <= I_6(Q) + 2 deg Q · log 2` on `|z| <= 3`.
  - `φ^2` and `φ^-2` are conjugate, so `u + v` is the log of a nonzero norm, hence `>= 0`.
  - `0.3u + 0.1v = 0.3(u+v) - 0.2v >= -0.2v`. The node's middle term `0.1(u+v) + 0.2u` is the same number.
  - The final bound is `0.4 deg Q · log(3/2) >= 0`.
- **Not integer-matrix limits.** Import, reviewed in parts 5 and 6.
