---
rg: 2
id: dyadic-affine-germ-groupoids-are-not-k-graph-groupoids-proof
kind: route
title: Nakayama on the FKPS Koszul complex gives the prime-support theorem; the LHS spectral sequence over the unit group, with translation homology Z[1/2] (row 0) and Z[1/m] twisted by odd parts (row 1), puts nonzero 2-primary homology above an odd H_0
target: dyadic-affine-germ-groupoids-are-not-k-graph-groupoids
requires:
  - basilica-rn-group-is-not-a-k-graph-full-group
  - s-arithmetic-affine-rn-groups-are-k-graph-full-groups
  - finite-k-graph-boundary-groupoid-standard-facts
  - torsion-germ-rn-groups-are-not-k-graph-full-groups
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/dyadic_affine_homology.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-dyadic-affine-homology.txt
---

Conventions follow `basilica-rn-group-is-not-a-k-graph-full-group-proof` (cited as **[B]**). Homology of an ample
groupoid is Crainic–Moerdijk/Matui homology. It is invariant under isomorphism and under Kakutani (Morita)
equivalence, and it commutes with the flat base change `- ⊗ Z_(ℓ)`, since it is the homology of a complex of free
abelian groups. For `ℓ = 0`, `Z_(0) = Q`.

## 1. The prime-support theorem (part 1)

**Import (FKPS)**, as in [B] Step 3. For a row-finite `k`-graph with no sources, `H_*(G_Λ)` is the homology of the
Koszul complex `K(1 - M_1^t, ..., 1 - M_k^t; Z^{Λ^0})`. The adjacency matrices commute.

**Lemma N.** Let `A` be a commutative ring, `N` a finitely generated `A`-module, and `f_1, ..., f_k ∈ A`, with
`I = (f_1, ..., f_k)`. If `H_0(K(f; N)) = N/IN = 0`, then `H_n(K(f; N)) = 0` for every `n`.

*Proof.*
- **An annihilator.** By Nakayama in the form of Atiyah–Macdonald Cor. 2.5, `N = IN` with `N` finitely generated
  gives an `a ∈ I` with `(1 - a)N = 0`. Then `1 - a` kills every chain module `Λ^n(A^k) ⊗ N`, and hence the homology.
- **Multiplication by `f_i` is null-homotopic on `K(f; N)`.** Let `h = e_i ∧ -`. Then `∂h + h∂` is multiplication
  by `f_i`, because `∂` is contraction with `(f_1, ..., f_k)` and is a graded derivation. So every element of `I`,
  and in particular `a`, kills `H_*(K(f; N))`.
- **Conclusion.** `1 = (1 - a) + a` kills `H_n`, so `H_n = 0`. ∎

*Proof of part 1.* Fix `ℓ`. Take `A = Z_(ℓ)[x_1, ..., x_k]`, acting on `N = Z_(ℓ)^{Λ^0}` by `x_i ↦ M_i^t`. This
is well defined because the matrices commute. Take `f_i = 1 - x_i`.
- `N` is finitely generated, even over `Z_(ℓ)`, because `Λ^0` is finite.
- `K(f; N) = K ⊗ Z_(ℓ)`, where `K` is the FKPS complex. So `H_*(K(f; N)) = H_*(G_Λ) ⊗ Z_(ℓ)`.

Lemma N gives part 1. For a finite `H_0`, the prime statement is the case of primes `ℓ ∤ |H_0|`. Kakutani
equivalence preserves homology, which gives the last bullet. For `ℓ = 0`, this is [B] Lemma K, with no eigenspace
decomposition needed. ∎

*Calibration* (script part C). Koszul homology is computed with Smith forms for 2,500 random commuting tuples of
nonnegative matrices, and for all 743 commuting pairs of `2×2` matrices with entries in `{0,1,2}`. There is no
violation. The known `k`-graph groupoids, the lamplighter `(2,2)` and `F_3(t)` with `(3,9)`, satisfy part 1.

## 2. The groupoid as a transformation groupoid

Fix a prime `p`, an integer `m ≥ 1` prime to `p`, and `R = Z[1/pm]`. Let `U ≤ R^×` be torsion-free with
`v_p(U) = gZ`, `g ≥ 1`. Put `Γ = R ⋊ U`, acting on `Q_p` by `x ↦ ux + b`. Let `𝒢` be the groupoid of germs of
elements of `Γ` at points `ω ∈ Z_p` with image in `Z_p`.

- **The germ determines the element.** If `g, g' ∈ Γ` have the same germ at `ω`, then two affine maps agree on an
  open set, so `g = g'`. Hence `𝒢 = (Γ ⋉ Q_p)|_{Z_p}`, with the same topology: basic sets `{g} × W`.
- **`Z_p` meets every orbit.** Translations by `R` are dense in `Q_p`, because `R ⊇ Z[1/p]`. So `Z_p` is a
  compact open full subset, and `𝒢` is Kakutani equivalent to `Γ ⋉ Q_p`.
- **So** `H_*(𝒢) ≅ H_*(Γ ⋉ Q_p) ≅ H_*(Γ; C_c(Q_p, Z))`. The second isomorphism is the standard identification of
  transformation-groupoid homology with group homology.
- **Properties.** `𝒢` is ample, Hausdorff, effective (a non-identity affine map fixes at most one point) and
  minimal, and its unit space is a Cantor set.

## 3. The translation subgroup

Let `M = C_c(Q_p, Z)`, with `(γf)(x) = f(γ^{-1}x)`, and put `L_n = R ∩ p^nZ_p = p^n Z[1/m]`.

**Levels.** Let `M_n` be the functions that are constant on cosets of `p^nZ_p`. Then `M = colim_n M_n`.
- Density gives `Q_p/p^nZ_p = R/L_n`. So `M_n = Z[R/L_n] = Ind_{L_n}^R Z`.
- Under Shapiro's isomorphism, the inclusion `M_n ⊂ M_{n+1}` becomes the transfer `L_n → L_{n+1}`. This holds
  because `1_{p^nZ_p} = Σ_{j<p} 1_{jp^n + p^{n+1}Z_p}`.

**Homology.** `L_n ≅ Z[1/m]` is torsion-free of rank one. So `H_0(L_n) = Z`, `H_1(L_n) = L_n` and
`H_{≥2}(L_n) = Λ^{≥2}L_n = 0`. Homology commutes with filtered colimits. The transfer is:
- multiplication by `p` on `H_0`;
- `x ↦ px` on `H_1`. For `x ∈ L_{n+1}`, the transfer of an abelian group is the `p`-th power, and `L_n/L_{n+1}` is
  torsion while `L_{n+1}` is torsion-free.

Hence:
- `H_0(R; M) = colim(Z --p--> Z --p--> ...) ≅ Z[1/p]`, sending `[1_{p^nZ_p}] ↦ p^{-n}` (the Haar integral);
- `H_1(R; M) = colim(L_n, x ↦ px) ≅ Z[1/m]`, sending `x ∈ L_n` (at level `n`) to `p^{-n}x`;
- `H_{≥2}(R; M) = 0`.

**The `U`-action.** `u ∈ U` acts on `R` by multiplication and on `M` by `f ↦ f(u^{-1}·)`. Write `v = v_p(u)` and
`u' = up^{-v}`.
- **On `H_0`.** It sends `1_{p^nZ_p}` to `1_{p^{n+v}Z_p}`, so it multiplies by `p^{-v} = |u|_p`.
- **On `H_1`.** The Shapiro class of `x ∈ L_n` is `[x] ⊗ 1_{p^nZ_p}`, and `u` sends it to
  `[ux] ⊗ 1_{p^{n+v}Z_p}`. That is the class of `ux ∈ L_{n+v}`, and it has coordinate `p^{-n-v}ux = u'·p^{-n}x`. So
  `u` acts on `Z[1/m]` by multiplication by `u' ∈ Z[1/m]^×`.

## 4. The spectral sequence (parts 2 and 4)

`Γ = R ⋊ U` with `U ≅ Z^s`. The LHS spectral sequence reads
`E^2_{a,q} = H_a(U; H_q(R; M)) ⇒ H_{a+q}(𝒢)`.
- Only the rows `q = 0` and `q = 1` are nonzero.
- `H_a(U; -)` is the Koszul homology of the operators `1 - u_i` on a basis `u_1, ..., u_s`.

**Row 0** is `K(1 - |u_i|_p; Z[1/p])`. The ideal of `Z[1/p]` generated by the `1 - p^{-v_p(u)}` is
`(p^g - 1)`. Over the principal ideal domain `Z[1/p]`, a `GL_s` change of basis reduces the row of operators to
`(p^g - 1, 0, ..., 0)`, up to a unit. So:
- `E^2_{a,0} = (Z/(p^g - 1))^{C(s-1,a)}`;
- the whole row is killed by `p^g - 1`.

**Row 1** is `K(1 - u'_i; Z[1/m])`. Put `J = (u' - 1 : u ∈ U) ⊆ Z[1/m]`. Then `E^2_{0,1} = Z[1/m]/J`.

**`H_0`.** `H_0(𝒢) = E^2_{0,0} = Z/(p^g - 1)`.

**Localising at a prime `ℓ ∤ m(p^g - 1)`.**
- Row 0 dies: it is killed by `p^g - 1`, which is invertible in `Z_(ℓ)`.
- So `H_1(𝒢) ⊗ Z_(ℓ) = E^2_{0,1} ⊗ Z_(ℓ) = Z_(ℓ)/J Z_(ℓ)`. No differential reaches `(0,1)` from a nonzero term.
- `Z[1/m] ⊗ Z_(ℓ) = Z_(ℓ)`, since `ℓ ∤ m`. The quotient `Z_(ℓ)/JZ_(ℓ)` is nonzero exactly when `ℓ` divides the
  numerator of every `u' - 1`, or when `J = 0`.
- At such an `ℓ`, also `H_0(𝒢) ⊗ Z_(ℓ) = 0`. So part 1 is violated at `ℓ`, and `𝒢` is not Kakutani equivalent to
  any finite `k`-graph groupoid. This is part 4. The prime `ℓ = p` is allowed, since `p ∤ p^g - 1`.

**Part 2 (`p = 2`).** Every `u' ∈ Z[1/m]^×` is a quotient of odd integers, and `m` is odd. So `u' - 1` has even
numerator, and `JZ_(2) ⊆ 2Z_(2)`. With `ℓ = 2 ∤ m(2^g - 1)`:
- `H_1(𝒢) ⊗ Z_(2) = Z_(2)/JZ_(2) ≠ 0`;
- `H_0(𝒢) = Z/(2^g - 1)` is odd. ∎

Script part B evaluates these rows for 12 choices of `(m, U)` at `p = 2`; part E evaluates the `ℓ`-criterion for six
odd-`p` cases.

## 5. The exact computation for `BS(1,r)` (part 3, homology)

Take `p = 2`, `m = |r|` and `U = ⟨2, r⟩`, with `r` odd and `|r| ≥ 3`.
- **The setup applies.** `U ≅ Z^2` is torsion-free, because `2^a r^b = ±1` forces `a = b = 0`. Also `g = 1`.
- **Row 0 is exact integrally.** It is `K(1 - 1/2, 1 - 1; Z[1/2]) = K(1/2, 0; Z[1/2])`, and `1/2` is a unit.
- **Row 1.** Here `2' = 1` and `r' = r`. So row 1 is `K(0, 1 - r; Z[1/r]) = K(1 - r; Z[1/r]) ⊗ Λ(Z)`, where the
  second exterior factor has zero differential.
- **`K(1 - r; Z[1/r])`.** Multiplication by `1 - r` is injective. Its cokernel is `Z[1/r]/(r - 1) = Z/|r-1|`,
  because `r ≡ 1` is already a unit modulo `r - 1`.
- **So** `E^2_{0,1} = E^2_{1,1} = Z/|r-1|`, and every other `E^2` term is zero.

The spectral sequence has one nonzero row, so it collapses:
- `H_0(𝒢) = 0`;
- `H_1(𝒢) = H_2(𝒢) = Z/|r-1|`;
- `H_{≥3}(𝒢) = 0`.

For `r = 3` this is `(0, Z/2, Z/2)`, which confirms the sketch in §9 of
`s-arithmetic-affine-rn-groups-are-k-graph-full-groups-proof`.

**An independent check** (script part A). `Γ = N ⋊ ⟨2⟩` with `N = Z[1/2r] ⋊ ⟨r⟩`. On `Z_2`, `N` restricts to
`BS(1,r) ⋉ Z_2`, a colimit over the level stabilisers `S_n = 2^n Z[1/r] ⋊ ⟨r⟩`.
- Each `S_n` has `H_1(S_n) = Z ⊕ Z/|r-1|`.
- Coset enumeration gives transfer `[[2,0],[(r-1)/2,1]]` and conjugation action `1`, for 12 values of `r` and
  `n ≤ 6`.
- The Pimsner–Voiculescu (Wang) sequence then gives the same homology.

## 6. The germ groupoid of `V_p(Z[1/m] ⋊ U')` is `𝒢` (Lemma D analogue)

Let `p`, `m` be as in §2, and let `U' ≤ Z[1/m]^×` be torsion-free. Put `H = Z[1/m] ⋊ U'`, acting on `Z_p`. Write
`ω ∈ Z_p` by its digits in `{0, ..., p-1}`, so `Z_p = X^ω` with `|X| = p`. The prefix map of a word `w` of length
`n` is `λ_w(y) = w + p^n y`, where `w` is read as an integer.

**`H` is self-similar and faithful.** Take `h(y) = u'y + c` and a digit `i`. Then `u'i + c ∈ Z[1/m] ⊂ Z_p`, so
`u'i + c = j + pc'` with `j` a digit and `c' ∈ Z_p ∩ Z[1/pm] = Z[1/m]`. Hence `h(i + py) = j + p(u'y + c')`, and
the section `h|_i = u'y + c'` lies in `H`. Faithfulness holds because distinct affine maps differ on a dense set.
- For `p = 2`, `m = |r|` and `U' = ⟨r⟩`, this is `BS(1,r)` with `x + 1 = (1, x+1)σ`, `rx|_0 = rx` and
  `rx|_1 = rx + (r-1)/2`.

**Germs.** `V_p(H)` is generated by `H` and the Higman–Thompson group `V_p`. Every germ of `V_p(H)` is the germ of
some `λ_v h λ_w^{-1}`, and every such map is affine with multiplier in `⟨p⟩ × U'` and translation part in `Z[1/pm]`.
So `𝒢_H ⊆ 𝒢_{m, ⟨p⟩×U'}`.

Conversely, let `γ(x) = ux + b` with `u = p^a u'` and `γ(ω) ∈ Z_p`.
- Choose `n ≥ max(0, -a)`. Let `w` be the length-`n` prefix of `ω`, and `v` the length-`(n+a)` prefix of `γ(ω)`.
- Then `λ_v^{-1} γ λ_w (y) = u'y + c`, with `c = (γ(w) - v)/p^{n+a}`.
- `γ(w) - γ(ω) = u(w - ω) ∈ p^{n+a}Z_p`, and `γ(ω) - v ∈ p^{n+a}Z_p`. So `c ∈ Z_p ∩ Z[1/pm] = Z[1/m]`, and
  `h = u'y + c ∈ H`.
- So `γ = λ_v h λ_w^{-1}` on the cylinder `wZ_p`, and the germ of `γ` at `ω` lies in `𝒢_H`.

Hence `𝒢_H = 𝒢_{m, ⟨p⟩ × U'}`. Script parts D and E verify the decomposition on 681 random germs.

## 7. The full-group conclusion (part 3)

Suppose `V_2(H) ≅ F(G_Λ)` for a finite `k`-graph `Λ` with (H), where `H = BS(1,r)`, or more generally
`H = Z[1/m] ⋊ U'` with `m` odd.
- Part 1 (rigidity) of [B] gives `𝒢_H ≅ G_Λ`.
- §6 gives `𝒢_H = 𝒢_{m, ⟨2⟩ × U'}`.
- §4 gives `H_0(G_Λ) ⊗ Z_(2) = 0` and `H_1(G_Λ) ⊗ Z_(2) ≠ 0`. For `BS(1,r)`, §5 gives `H_0 = 0` and
  `H_1 = Z/|r-1| ≠ 0` integrally.

This contradicts part 1. ∎

Part 1 applies more widely than rigidity. The groupoid `𝒢` is also not Kakutani equivalent to any `G_Λ`, which
excludes stable and corner models as well.

**Hypothesis (H)** is the standing hypothesis of `torsion-germ-rn-groups-are-not-k-graph-full-groups`, used in [B].
`𝒢` is Hausdorff and effective (§2), so the torsion-germ obstruction does not apply, and this node is needed.

## 8. Consistency checks and tier

- **Function fields.** In `s-arithmetic-affine-rn-groups-are-k-graph-full-groups`, `H_j = (Z/(q-1))^{C(k-1,j)}`.
  - All torsion is `(q-1)`-primary, so part 1 holds, as it must for a genuine `k`-graph groupoid.
  - For `q = 2`, every group is `0`.
  - There the analogue of `u' - 1` is a unit of `F_q[t]` localised, so row 1 dies. Over `Q` at `2`, `u' - 1` is
    always even, and row 1 survives 2-locally.
- **Lamplighter `(2,2)` and `F_3(t)` with `(3,9)`** satisfy part 1 in script part C.
- **Basilica and odometer.** [B] excludes these rationally. Part 1 at `ℓ = 0` is that argument without the
  eigenspace step.
- **Odd `p`.** The table in script part E records the excluded cases and the cases with no obstruction
  (claim, part 4).

**Tier.** Parts 1–3 are ESTABLISHED as a lane proof (w13-101), not independently reviewed. Part 4 is ESTABLISHED
for the stated prime condition. It is not an iff: `V_3(BS(1,2))` is open.
