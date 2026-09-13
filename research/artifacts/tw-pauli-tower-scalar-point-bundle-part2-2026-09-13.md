# Pauli towers, part 2: orthogonal pairs, every prime, and what strict comparison would demand (2026-09-13)

Lane `ex2-tw-unsplittable-tails`. **Unreviewed.** Continues
`research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md` (part 1), whose notation is used:
`A = lim A_m`, `X̂ = Π_k Y_k`, `M` its uniform tracial completion, `π_λ` the fibre maps.

**Outcome.**
1. **Theorem C (orthogonal pairs).** For any two orthogonal positive elements `a, b ∈ M`, one of them
   vanishes in some fibre. So every c.p.c. order zero `φ: M_N → M` (`N ≥ 2`) has a point `λ` with
   `π_λ ∘ φ = 0`, and every projection `p ∈ M` has a point with `τ_λ(p) ∈ {0, 1}`. The capacity
   `sup_φ min_λ τ_λ(φ(1))` for order zero `M_2` is `0`, the worst possible.
2. **Theorem D (every prime).** For each prime `p`, a tower of flat `M_p`-bundles over products of lens
   spaces with Weyl (clock–shift) holonomy has the scalar point property. So nontrivial R-fibre bundles
   arise from `C(X̂)`-algebras with `M_{p^∞}` fibres for every `p`.
3. **Heuristic constraints** for a simple algebra with strict comparison carrying this mechanism
   (Section 3), and for vector-bundle towers (Section 4). Not theorems.

## 1. Theorem C

**Theorem C.** Let `a, b ∈ M` be positive with `ab = 0`. Then there is `λ ∈ X̂` with `π_λ(a) = 0` or
`π_λ(b) = 0`.

*Proof.* By Theorem B(2) of part 1 the self-adjoint element `a − b` has a point `λ` with
`π_λ(a) − π_λ(b) = μ1`. In the fibre, `π_λ(a)π_λ(b) = 0`.
- If `μ > 0`, then `π_λ(a) = μ1 + π_λ(b) ≥ μ1` is invertible, so `π_λ(b) = 0`.
- If `μ < 0`, symmetrically `π_λ(a) = 0`.
- If `μ = 0`, then `π_λ(a) = π_λ(b)`, so `π_λ(a)² = π_λ(a)π_λ(b) = 0` and both vanish. ∎

**Corollary C1 (order zero maps vanish somewhere).** Let `φ: M_N → M` be c.p.c. order zero with
`N ≥ 2`.
- Apply Theorem C to `a = φ(e_{11})`, `b = φ(e_{22})`, which are orthogonal. One of them vanishes at
  some `λ`.
- In the fibre `R`, with supporting homomorphism `π` and `c = φ(1)` commuting with it,
  `φ(e_{ii}) = π(e_{i1}) φ(e_{11}) π(e_{1i})`. So all `π_λ(φ(e_{ii}))` vanish together, and
  `π_λ(φ(1)) = Σ_i π_λ(φ(e_{ii})) = 0`. ∎
- This sharpens `pauli-tower-bundle-has-no-uniform-order-zero-m2` from `‖E(1 − φ(1))‖ < 1/4` to
  `min_λ τ_λ(φ(1)) = 0` for every such `φ`.

**Corollary C2 (projections).** For a projection `p ∈ M`, apply Theorem C to `p` and `1 − p`: some
fibre has `π_λ(p) ∈ {0, 1}`. So every projection of `M` is `0` or `1` in some fibre (and `A` has no
projection other than `0` and `1`, part 1). ∎

**Remark (what the property is).** In `C_σ(K, R)` constant orthogonal projections `e`, `1 − e` are
nowhere zero. So Theorem C is a second nontriviality certificate, and it is monotone. It passes to
any W*-subbundle containing `C(K)`, and it forbids every partition of the unit into two nowhere-vanishing
pieces. It is an existence gap in the strongest form: the unit admits no nowhere-degenerate
orthogonal decomposition at all, although every fibre `R` admits one.

## 2. Theorem D: every prime

**Setup.** Fix a prime `p`, `ω = e^{2πi/p}`, shift `S e_i = e_{i+1}` and clock `C e_i = ω^i e_i` on
`C^p`.
- `E = (Z/p)²` acts on `M_p` by `Ad S`, `Ad C`, which commute since `CS = ωSC`.
- The Weyl operators `S^a C^b`, `(a, b) ≠ 0`, span `M_p ⊖ C1` and are eigenvectors with pairwise
  distinct nonzero characters.
- For `r` factors, `E^r` acts on `M_{p^r}`, and each nonzero character of `E^r ≅ F_p^{2r}` occurs
  exactly once.

**Real form.** `Herm_0(C^{p^r})` is the direct sum, over nonzero characters `χ` modulo `±`, of the real
2-planes `Re/Im` of `W_χ + W_χ*`. For `p` odd, each plane is the complex line bundle `L_χ` associated to
`χ`, with `c_1(L_χ) = χ(y)` mod `p`. For `p = 2` this is part 1.

**The tower.**
- `L^{2d+1} = S^{2d+1}/(Z/p)` is a lens space, with `H*(L^{2d+1}; F_p) = Λ(t) ⊗ F_p[y]/(y^{d+1})` and
  `y` the mod-`p` first Chern class of the tautological line.
- `d_j = (p − 1)p^{j−1}/2`, `Y_k = L^{2d_{2k−1}+1} × L^{2d_{2k}+1}`.
- `B_k` is the flat `M_p`-bundle with the two generators acting by `Ad S`, `Ad C`.

**Theorem D.** For all `n < m`, every self-adjoint section of `⊠_{n<k≤m} B_k` is somewhere scalar.
Hence the uniform tracial completion of `lim C(Π_{k≤m} Y_k, ⊠_{k≤m} B_k)` has the scalar point
property, and it is a nontrivial R-fibre W*-bundle.

*Proof sketch.*
1. **Euler class.** The traceless self-adjoint bundle is `⊕_{χ ≠ 0 mod ±} L_χ`, oriented, with mod-`p`
   Euler class `Π_{χ mod ±} χ(y)` (sign ambiguity irrelevant).
2. **Moore power.** Over `F_p`, `Π_{c∈F_p^*/±} (cℓ) = u·ℓ^{(p−1)/2}` with `u ∈ F_p^*`. So the Euler class is
   a unit times `L(y)^{(p−1)/2}`, where `L(y) = det[y_j^{p^i}]` is the Moore determinant: the product of
   one representative of each projective point.
3. **Leading monomial.** In the lexicographic order with later variables larger, `L` has leading
   monomial `Π_j y_j^{p^{j−1}}` with coefficient `±1`. Leading monomials multiply over a domain, so
   `L^{(p−1)/2}` has leading monomial `Π_j y_j^{(p−1)p^{j−1}/2}` with coefficient `±1`.
4. **Survival.** With the tail coordinates relabelled from `j = 1`, those exponents are
   `≤ d_{j+2n}`. The monomial basis of `F_p[y]/(y_j^{d_j+1})` keeps its coefficient, so the Euler class is
   nonzero on the tail base.
5. **Conclusion.** A nowhere-zero section of an oriented bundle kills its Euler class, hence its mod-`p`
   reduction. The passage to `M` is Theorem B of part 1 verbatim. ∎
- **Degree check.** `Σ_j 2d_j = p^{2r} − 1` equals the real rank.

## 3. What a strict-comparison witness of this type would need (heuristic)

- **Rank windows kill the gap.** Let `A'` be unital, simple and exact with strict comparison. If some
  `x ∈ M_∞(A')_+` has `d_τ(x) ∈ (1/(n+1), 1/n)` at every trace, then `n x ≤ [1] ≤ (n+1)x`. So the unit is
  tracially divisible (`strict-comparison-unit-divisibility-equivalences`), and Corollary C1 fails in the
  face bundles.
- **The gap is unit-only.** `e_{11} ⊗ 1 ∈ M_2(M)` has constant trace `1/2` (part 1, C5). A witness must
  exclude constant rank windows at `[1]` in every amplification `M_k(A')`.
- **Rank windows are nested local subprojections.** A positive element of `M_k(C(Z, B))` has rank
  everywhere in `[a, b]` iff there is a finite open cover `V_i`, ordered, with twisted subprojections
  `P_i` of `M_k ⊗ B` over `V_i`, nested on overlaps (`P_j ≤ P_i` for `i < j`), and ranks in `[a, b]`.
  - **If.** `Σ_i f_i P_i` for a subordinate partition of unity has rank equal to the largest active
    `P_i`.
  - **Only if.** Use spectral projections at `k + 1` thresholds and pigeonhole, as for soft
    splittings.
  - So excluding windows is a relative Hermitian degeneracy problem in `M_k ⊗ B`, one for each `k`.
- **Why the part-1 obstruction does not give it.** In `M_k ⊗ B_{0,n}` the complement of `M_k ⊗ 1` has
  rank `k²(4^n − 1)`, which exceeds `dim Z_n`. Diagonal elements `diag(h_1, h_2)` with differently
  placed scalar points are nowhere in `M_k ⊗ 1`. So windows at early stages with large `k` are not
  excluded by Euler classes of the given tower.
- **A period–index lever.** Projections of `M_k ⊗ B` have rank divisible by the index of the
  Dixmier–Douady class. If the index at stage `m` were `2^m`, projection windows would be excluded. But
  positive-element windows come from local projections on small open sets, where the index restricts
  to `1`. The soft (positive element) version is the real question.
- **Verdict.** A Toms–Winter counterexample from twisted towers must defeat rank windows in all
  amplifications while keeping strict comparison. Nothing here suggests how. This mechanism settles the
  bundle question, not the crux.

## 4. Vector-bundle towers (heuristic)

- **Primary obstruction.** It vanishes for `End(W)` (part 1, Proposition D).
- **Genuine lifts and their fixed points.** Genuine lifts of the Pauli holonomy (`D_8` or `Q_8` in
  `U(2)`) act irreducibly on `(C²)^{⊗m}`. So `G = D_8^m` fixes no soft half projection, and the generalized
  Sullivan conjecture (finite `p`-groups, finite-dimensional targets) excludes sections over all of
  `BG`.
- **Why Borel cohomology gives nothing coarse.**
  - An elementary abelian subgroup of `D_8^m` projects to commuting elements in each factor, so it acts
    by simultaneously diagonalizable operators and fixes a soft half projection.
  - By Quillen stratification, `H*(BG; F_2) → H*_G(X_ε; F_2)` then has nilpotent kernel.
  - So only nilpotent classes can obstruct on finite skeleta. Whether any does, at every depth, is open.
- This is why `ah-face-bundles-are-trivial` and the vector-bundle form of
  `some-tensor-tower-has-unsplittable-tails` stay open.

## 5. Mechanical check of the combinatorics (MSI, 2026-09-13)

**The script.** A small Python script (`/scratch.global/sauer354/ex/ex2-tw-unsplittable-tails/moore_check.py`)
multiplies all nonzero `F_2`-linear forms in the tail variables `t_{2n+1}, …, t_{2m}` and truncates by
`t_j^{d_j+1}`, with `d_j = 2^{j−1}`.

**Output, quoted.**

```text
n=0 m=1 terms=1 monomials=[(1, 2)]
n=0 m=2 terms=1 monomials=[(1, 2, 4, 8)]
n=1 m=3 terms=18 monomials=[(1, 2, 4, 8), (1, 2, 8, 4), (1, 4, 2, 8), (1, 4, 8, 2)] ...
n=0 m=3 terms=1 monomials=[(1, 2, 4, 8, 16, 32)]
control (0,2) with d_4=7: terms=0
```

**What it confirms.**
- For `n = 0` the truncated Moore determinant is exactly the top monomial `Π_j t_j^{2^{j−1}}`.
- For a tail it is nonzero.
- Lowering one dimension by one kills it. So the base dimensions of the tower are sharp for this
  argument.

**Theorem D, same check.** `weyl_check.py` multiplies one linear form per nonzero `c ∈ F_p^s` modulo
`±`, and truncates by `y_j^{d_j+1}` with `d_j = (p−1)p^{j−1}/2`. Output, quoted:

```text
p=3 s=2 forms=4 dsum=4 terms=1 sample=[((1, 3), 2)]      control last d-1: terms=0
p=3 s=4 forms=40 dsum=40 terms=1 sample=[((1, 3, 9, 27), 1)]   control: terms=0
p=5 s=2 forms=12 dsum=12 terms=1 sample=[((2, 10), 4)]   control: terms=0
p=7 s=2 forms=24 dsum=24 terms=1 sample=[((3, 21), 6)]   control: terms=0
```

In each case the truncated Euler class is the single top monomial with a unit coefficient, and the
controls vanish. This checks the leading-monomial step of Theorem D for these cases. The general
statement remains a sketch.

## Trust surfaces

- Theorem C and Corollaries C1–C2 are elementary consequences of Theorem B of part 1, plus the
  Winter–Zacharias structure theorem (standard, not re-read). Unreviewed.
- Theorem D uses the standard cohomology of lens spaces, the Moore determinant over `F_p`, and
  leading-monomial multiplicativity. Sketch-level, unreviewed.
- Sections 3–4 are analysis, not theorems.
