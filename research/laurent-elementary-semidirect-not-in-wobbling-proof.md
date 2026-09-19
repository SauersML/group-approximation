---
rg: 2
id: laurent-elementary-semidirect-not-in-wobbling-proof
kind: route
title: Relative (T) makes every base orbit finite, (τ) of SL_2(F_p[t,t^-1]) over its finite-index subgroups bounds every finite orbit, and exponential unipotent growth against linear Schreier growth makes a nonzero congruence submodule act trivially on the at most 2r infinite orbits
target: laurent-elementary-semidirect-product-is-not-in-wobbling-group
requires:
  - elementary-linear-semidir-pair-relative-t
---

Notation as in the target. `S` is a finite symmetric generating set of `Γ`, and `r` is the largest
displacement of `ρ(s)` for `s ∈ S`. `B_S(n)` is the ball of radius `n` in `Γ`. All actions are via
`ρ`, and `gx` means `ρ(g)(x)`.

## Imports (verbatim)

- **Congruence kernel (Serre 1970).** Mason–Premet–Sury–Zalesskii, arXiv:0710.4009, for `k` a global
  field: "The principal result in [S1] is that, for the case G = SL2, the congruence kernel
  C(S, G) is finite if and only if card S ≥ 2." Here [S1] is Serre, Ann. of Math. 92 (1970). For
  `R = F_p[t, t^{-1}]` = `O_S` in `k = F_p(t)` with `S = {v_t, v_∞}`, we have `card S = 2`.
- **Selberg property (Drinfeld).** Lubotzky, arXiv:1105.2389, §2.4: "Analogous results for
  arithmetic groups in positive characteristic such as SL2(Fp[t]) or SL2(Fp[t,t−1]) (when this
  time a result of Drinfeld replaces the Theorem of Selberg) can make, for a fixed p, the family
  {SL2(Fpα)|α∈N} into a family of expanders."
  - Definition 2.14 there: "We say that Γ has the Selberg property if it has property (τ) with
    respect to the congruence subgroups {Γ(I)}0≠I◁θS".
  - It continues: "Again, if true for Γ, then it is true for all the arithmetic groups in its
    commensurability class."
- **Independent adelic backup.** Mohammadi–Tamam, arXiv:2202.03470, Theorem 1.2: "Let v ∈ Σ be such
  that G is isotropic over Fv. Then L2_0(G(A)/G(F)), the orthogonal complement of G(A)-invariant
  functions, is isolated from the trivial representation as a representation of G(Fv)."
  - For `G = SL_2`, strong approximation and continuity of induction from the lattice `E` in
    `SL_2(k_t) × SL_2(k_∞)` turn this into the Selberg property of `E`. This is the standard
    deduction that the Lubotzky quote summarizes.
- **Relative (T)**, from `elementary-linear-semidir-pair-relative-t`: `(E ⋉ R², R²)` has relative
  (T).

## Step 0: uniform relative Kazhdan pair

Relative (T) gives a finite `Q ⊂ Γ` and `κ > 0` such that the following holds for every unitary
representation `π` of `Γ` and every `η ⊥ π^H`:

`max_{g ∈ Q} ‖gη − η‖ ≥ κ‖η‖`.   (0)

- Suppose not. Take `π_k` and unit vectors `η_k ⊥ π_k^H` with `max_{g ∈ Q_k} ‖gη_k − η_k‖ < 1/k`,
  where `Q_k` increases to `Γ` (a countable group). Since `H ⊴ Γ`, the space `(π_k^H)^⊥` is
  `Γ`-invariant, so we may restrict `π_k` to it.
- Then `⊕ π_k` has almost invariant vectors and no nonzero `H`-invariant vector. That contradicts
  relative (T).
- Since `H` is normal, the projection `P_H` onto `π^H` commutes with `π(Γ)`. So
  `‖g(1 − P_H)ξ − (1 − P_H)ξ‖ ≤ ‖gξ − ξ‖` and `‖gP_Hξ − P_Hξ‖ ≤ ‖gξ − ξ‖` for all `ξ`.   (0')

## Step 1: at most 2r infinite orbits (item 1)

- Let `B` be a `Γ`-orbit, and suppose `a < b` are consecutive points of `B` with `b − a > r`.
  Each `s ∈ S` moves points by at most `r`, so `s` maps `B ∩ (−∞, a]` into itself. Then
  `B ∩ (−∞, a]` is a nonempty proper `Γ`-invariant subset of `B`, which is impossible. So every
  orbit has gaps of length at most `r`.
- An infinite orbit is unbounded above or unbounded below.
  - If `B` is unbounded above, it meets every window `[N, N + r)` with `N ≥ min(B ∩ [0, ∞))`.
  - Distinct orbits are disjoint, so for `N` large at most `r` orbits are unbounded above.
  - Likewise at most `r` orbits are unbounded below.

## Step 2: every H-orbit is finite (item 2)

Let `r_Q` be the largest displacement of `ρ(Q)`. Take `π` to be the permutation representation on
`ℓ²(Z)`. Then `ℓ²(Z)^H` consists of the `ℓ²` functions constant on `H`-orbits, which vanish on
infinite `H`-orbits.

Take an interval `J` and `f = 1_J`, and let `f_1 = (1 − P_H) f`. Here `P_H f` equals
`(|B ∩ J| / |B|) 1_B` on each finite `H`-orbit `B`, and `0` on each infinite one. So

`‖f_1‖² = Σ_{B finite} |B ∩ J| |B \ J| / |B| + Σ_{B infinite} |B ∩ J|`.

- For `g ∈ Q`, only points within `r_Q` of an endpoint of `J` can leave or enter `J`. So
  `‖gf − f‖² = |gJ Δ J| ≤ 4 r_Q`.
- By (0) and (0'), `κ² ‖f_1‖² ≤ 4 r_Q`.
- So `Σ_{B infinite} |B ∩ J| ≤ 4 r_Q / κ²` for every interval `J`. Letting `J` grow, the union of
  the infinite `H`-orbits has at most `4 r_Q / κ²` points. A finite union of infinite orbits is
  empty.
- A finite `H`-orbit meeting both `J` and `Z \ J` contributes at least
  `min(|B∩J|, |B\J|) / 2 ≥ 1/2`. So at most `8 r_Q / κ²` `H`-orbits straddle `J`.

**Normality.** For `x` in a `Γ`-orbit `O` and `g ∈ Γ`, the stabilizers satisfy
`H_{gx} = g H_x g^{-1}`. So all `H`-orbits in one `Γ`-orbit have the same size `m_O`. Since `H` is
abelian (in our case), `H_y = H_x` for all `y ∈ Hx`.

## Step 3: finite orbits are bounded (item 3)

Assume `Γ/H` has (τ) for all finite-index subgroups. So there is `κ_E > 0` with
`max_{s ∈ S} ‖sη − η‖ ≥ κ_E ‖η‖` for every finite transitive `Γ/H`-set `Y` and every
`η ∈ ℓ²_0(Y)`. For `Γ_p` this is Step 6.

Let `O = {o_1 < … < o_n}` be a finite `Γ`-orbit. Put `a = ⌊n/2⌋`, `A = {o_1, …, o_a}` and
`ξ = n 1_A − a 1_O ∈ ℓ²_0(O)`. Let `r' = max(r, r_Q)`.

- `‖ξ‖² = n a (n − a) ≥ n² (n − 1) / 4`.
- Take `g ∈ S ∪ Q`, and let `c` be a cut point between `o_a` and `o_{a+1}`. A point of `A` that `g`
  moves out of `A` lies in `[c − r', c]`, and a point `g` moves into `A` lies in `[c, c + r']`. So
  `|gA Δ A| ≤ 2(r' + 1)`, and `‖gξ − ξ‖² = n² |gA Δ A| ≤ 2 n² (r' + 1)`.
- So `max_{g ∈ S ∪ Q} ‖gξ − ξ‖ ≤ δ_n ‖ξ‖`, with `δ_n = (8 (r' + 1) / (n − 1))^{1/2}`.

Split `ξ = ξ_0 + ξ_1` with `ξ_0 = P_H ξ ∈ ℓ²(O)^H`.

- By (0) and (0'), `‖ξ_1‖ ≤ (δ_n / κ) ‖ξ‖`. So once `δ_n < κ`, `ξ_0 ≠ 0` and
  `‖ξ_0‖ ≥ (1 − δ_n²/κ²)^{1/2} ‖ξ‖`.
- `ξ_0` has mean zero, because `P_H` is self-adjoint and `1_O` is `H`-invariant.
- `‖sξ_0 − ξ_0‖ ≤ ‖sξ − ξ‖` for `s ∈ S`, by (0').

All `H`-orbits in `O` have size `m_O` (Step 2). So `ξ_0 ↦ ξ_0|_{O/H}` identifies `ℓ²(O)^H` with
`ℓ²(O/H)`, scaling norms by `m_O^{1/2}` and preserving mean zero. `Γ/H` acts transitively on the
finite set `O/H`, and `H` acts trivially on `ℓ²(O)^H`.

So `η = ξ_0|_{O/H} ∈ ℓ²_0(O/H)` is nonzero and satisfies
`max_{s ∈ S} ‖sη − η‖ ≤ δ_n (1 − δ_n²/κ²)^{-1/2} ‖η‖`. The (τ) bound forces
`δ_n (1 − δ_n²/κ²)^{-1/2} ≥ κ_E`, which fails once `n` is large. So `n ≤ M`, where `M` depends
only on `r', κ, κ_E`.

The kernel of `Γ` on a finite orbit is an intersection of point stabilizers of index at most `M`,
so it contains `Γ_M`. Since `Γ` is finitely generated, it has finitely many subgroups of index at
most `M`, so `Γ_M` has finite index. So `Γ_M` acts trivially on `Z_fin`.

## Step 4: congruence lemma for Γ_p (item 4)

**Generators.**
- Put `u_s = [[1, s], [0, 1]]`, `l_s = [[1, 0], [s, 1]]` and `d = diag(t, t^{-1}) ∈ E`.
- Then `d u_s d^{-1} = u_{t² s}` and `d l_s d^{-1} = l_{t^{-2} s}`.
- `R = F_p[t^{±2}] ⊕ t F_p[t^{±2}]` and `E = EL_2(R)`. So `E` is generated by `u_1, u_t, l_1, l_t, d`,
  and `Γ_p` by these together with `e_1 ∈ H`.
- We may take `S` to contain them. Changing `S` only changes `r`.
- Let `V_N = span_{F_p} {t^{2k} : |k| ≤ N}`. For `s = Σ a_k t^{2k} ∈ V_N`, the Horner word
  `u_s = Π_k d^k u_{a_k} d^{-k}` has length at most `C N`, with `C` depending only on `p`. The same
  holds for `l_s`, with `t^{-2k}` in place of `t^{2k}`.

**Characters.**
- Every character of `H = R ⊕ R` has the form `χ(a, b) = χ_1(a) χ_2(b)` with `χ_i ∈ Hom(R, μ_p)`.
- `E` acts on characters by `(e·χ)(h) = χ(e^{-1} h)`.
- `Ann(ψ) = {c ∈ R : ψ(cR) = 1}` is an ideal of `R`, and `(c·ψ)(b) = ψ(cb)`.
- We have `(u_s·χ)(a, b) = χ_1(a) χ_1(−sb) χ_2(b)`. So `u_s·χ = u_{s'}·χ` iff `s − s' ∈ Ann(χ_1)`.
- Similarly `l_s·χ = l_{s'}·χ` iff `s − s' ∈ Ann(χ_2)`.

**Counting.**
- Fix `x` in an infinite `Γ`-orbit `O`, and let `m = m_O`, finite by Step 2.
- Let `χ ∈ H_x^⊥`, the set of characters trivial on `H_x`. It has `m` elements.
- For `e ∈ E`, `e·χ ∈ H_{ex}^⊥`, since `H_{ex} = e H_x e^{-1}`.
- If `e ∈ B_S(n)`, then `|ex − x| ≤ rn`. So `|(E ∩ B_S(n))·χ| ≤ (2rn + 1) m`.
- Suppose `Ann(χ_1) = 0`. Then the `u_s·χ` for `s ∈ V_N` are pairwise distinct, so
  `p^{2N+1} ≤ (2rCN + 1) m` for every `N`. This is false for large `N`.
- So `Ann(χ_1) ≠ 0`, and likewise `Ann(χ_2) ≠ 0`, using `l_s`.

**The ideal.**
- `R` is a domain, so `I_x = ∩_{χ ∈ H_x^⊥} (Ann χ_1 ∩ Ann χ_2)` contains a finite product of nonzero
  ideals. So `I_x ≠ 0`.
- For `(a, b) ∈ I_x R²` and `χ ∈ H_x^⊥`, `χ(a, b) = χ_1(a) χ_2(b) = 1`.
- `H/H_x` is finite abelian, so `H_x = ∩_{χ ∈ H_x^⊥} ker χ`. Hence `I_x R² ⊆ H_x`.
- `I_x R²` is an `E`-submodule, so it is normal in `Γ_p`.
- A normal subgroup fixing `x` fixes every `gx`. So `I_O := I_x` works for all of `O`.

## Step 5: conclusion (item 5)

- Let `O_1, …, O_k` be the infinite orbits, with `k ≤ 2r` by Step 1.
- `J = I_{O_1} ⋯ I_{O_k}` is a nonzero ideal, and `N = J R² ⊆ ∩_i I_{O_i} R²` is normal and acts
  trivially on `Z_∞`.
- By Step 3, whose (τ) input is Step 6, `N ∩ Γ_M` acts trivially on `Z_fin`.
- `J ⊇ cR ≅ R` for some `c ≠ 0`, so `N` is infinite. `N ∩ Γ_M` has finite index in `N`, so it is an
  infinite subgroup of `H ∩ ker ρ`.
- Every `f ∈ [[X]]` acts on the orbit of a point `z` with dense `σ`-orbit by
  `σ^n z ↦ σ^{n + c(σ^n z)} z`, where `c` is continuous, hence bounded.
  - This gives a homomorphism `[[X]] → W(Z)`.
  - It is injective: an `f` trivial on a dense set is trivial.
- So neither `Γ_p` nor any group containing it embeds in `W(Z)` or in `[[X]]`.

## Step 6: E has (τ) for all its finite-index subgroups

Write `Γ(I) = ker(E → SL_2(R/I))`, `Ê` for the profinite completion and `Ē` for the congruence
completion. `π: Ê → Ē` has kernel `C`, which is finite by the Serre import, since `|S| = 2`.

**(a) Every finite-index subgroup contains a congruence subgroup of a fixed `E_0`.**
- `Ê` is profinite and `C` is finite, so there is an open normal `U ⊴ Ê` with `U ∩ C = 1`.
- Put `E_0 = E ∩ U`, a normal subgroup of finite index.
- `π|_U` is a continuous injection from a compact space, so it is a homeomorphism onto the open set
  `π(U)`.
- Let `Δ ≤ E_0` have finite index. Then its closure `Δ̄ ⊆ U` is open in `Ê`, so `π(Δ̄)` is open in
  `π(U)`. Hence `π(Δ̄)` contains `π(U) ∩ \overline{Γ(I)}` for some nonzero ideal `I`.
- Take `γ ∈ N_I := E_0 ∩ Γ(I)`. Then `π(γ) = π(δ)` for some `δ ∈ Δ̄`, and injectivity on `U`
  gives `γ = δ ∈ Δ̄ ∩ E = Δ`. So `N_I ⊆ Δ`, and `N_I ⊴ E`.

**(b) Uniform gap on `ℓ²_0(E/N_I)`.** For an arbitrary finite-index `Δ ≤ E`, part (a) gives
`N_I ⊆ Δ ∩ E_0`. So `ℓ²_0(E/Δ)` embeds `E`-equivariantly in `ℓ²_0(E/N_I)`, and it suffices to
bound `ℓ²_0(E/N_I)` uniformly in `I`. Split it into two `E`-invariant pieces.

- **Piece `W_0 = ℓ²_0(E/N_I)^{E_0} = ℓ²_0(E/E_0)`.** This is a representation of the fixed finite
  group `E/E_0` with no invariant vectors. By compactness of its unit sphere it has a gap
  `κ_1 > 0` with respect to `S_E`, independent of `I`.
- **Piece `W^⊥`, the orthocomplement of all `E_0`-invariant vectors.**
  - Restricted to `E_0`, `ℓ²(E/N_I)` is the sum over coset representatives `γ` of `E/E_0` of the
    spaces `ℓ²(γE_0/N_I)`.
  - Each is `ℓ²(E_0/N_I)` twisted by the automorphism `c_γ` of `E_0`, since `N_I` is normal.
  - `W^⊥` is the sum of their mean-zero parts.
  - By the Drinfeld/Selberg import, `E` has the Selberg property. By the quoted
    commensurability remark, so does `E_0`, with respect to `{E_0 ∩ Γ(I)} = {N_I}`, with a gap
    `κ_2` for a finite generating set `S_0` of `E_0`.
  - Each twist changes `S_0` to `c_γ(S_0)`, and there are finitely many `γ`. Writing these in
    words of bounded length in `S_E` gives a gap `κ_3 > 0` for `E` on `W^⊥`, uniform in `I`.
- For `η = w + w'` with `w ∈ W_0`, `w' ∈ W^⊥`, orthogonality and invariance give
  `max_s ‖sη − η‖² ≥ |S_E|^{-1} Σ_s (‖sw − w‖² + ‖sw' − w'‖²) ≥ |S_E|^{-1} min(κ_1, κ_3)² ‖η‖²`.

So `κ_E = min(κ_1, κ_3) |S_E|^{-1/2}` works, and Step 3 applies with `Γ/H = E`. ∎

## Why this is not the Cornulier FW route

- Cornulier, arXiv:1308.1318, Theorem 1.18: "Let Γ be a finitely generated group with Property FM
  or FW. Then any action of Γ on Z by permutations of bounded displacement factors through a
  finite group."
- `E` lacks FW: it is dense in `SL_2(F_p((t)))` and acts on the Bruhat–Tits tree with `d`
  hyperbolic. This is the analogue of Cornulier, Remark 6.21: "for every I, SL 2(Z[I −1]) does not
  have Property FW’: if p ∈ I just use its dense embedding into SL 2(Qp)".
- Here only the finite orbits are controlled, via (τ) and relative (T). The infinite orbits are
  handled by the exponential-growth argument of Step 4, which uses the base.

