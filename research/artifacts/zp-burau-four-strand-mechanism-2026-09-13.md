# Four-strand Burau faithfulness: independent check of the mechanism (part 1)

Lane z3-05-burau-theory, 2026-09-13. Subject: arXiv:2607.05283v1, V. Bharathram, J. S. Birman,
T. E. Brendle, "The Burau representation of the braid group is faithful for n = 4" (submitted
6 July 2026, 26 pages, no journal reference, no withdrawal). The preprint is unrefereed.
Nothing here says it is correct. This note rebuilds the architecture of its proof from first
principles and checks that every implication points the right way. The combinatorial core
(Sections 5 and 6 of the preprint) is not checked here; lane z3-05-burau-search checks it line by
line.

Extraction status: the statements quoted in §1 come from the arXiv HTML render of the preprint,
read through a summarizing tool. They are not yet verbatim. A PDF text check is in progress
(part 2 will record differences).

## 0. Conventions

- `D_n` is the disk with punctures `p_1, ..., p_n` and a boundary base point `p_*`;
  `B_n = MCG(D_n rel boundary)`.
- The unreduced Burau representation `ρ̃_n : B_n → GL_n(Z[t,t^{-1}])` sends `σ_i` to
  `I_{i-1} ⊕ [[1-t, t],[1, 0]] ⊕ I_{n-i-1}`. `ρ_n` is the reduced (rank `n-1`) representation.
- `Brun_n ⊂ P_n` is the Brunnian subgroup: pure braids that become trivial when any one strand
  is deleted.
- `K_i ≅ π_1(D_{n-1}, p_i)` is the point-pushing subgroup of `B_n` for the puncture `p_i`
  (the kernel of forgetting `p_i` on the pure braid group, via the Birman exact sequence).

## 1. Architecture of the preprint (as extracted)

- **Step A** (Proposition 1.2, from Long's theorem, preprint reference [18]): if `ρ_4` is
  faithful on `Brun_4`, then `ρ_4` is faithful. Long's theorem as quoted: `ρ_n` is faithful on
  `B_n` if it is faithful on any nontrivial noncentral normal subgroup of `B_n`.
- **Step B** (Theorem 6.6): no nontrivial `Φ ∈ Brun_4` lies in `ker ρ_4`. Sub-steps:
  - B1: every nontrivial element of `Brun_4` is pseudo-Anosov (cited to Whittlesey);
  - B2: after conjugating, `Φ` is a proper product `Φ'·Γ_1` with `ι(α, (β_*^3)Φ) > 0`
    (Lemma 6.3), where `α` is the arc from `p_1` to `p_2` and `β_*^3` the arc from `p_*` to `p_3`;
  - B3 (Proposition 6.4, Corollary 6.5): for the inclusion `f : B_4 → B_5` that adds a puncture
    `p_5`, there is a push map `Γ ∈ K_5 ≅ π_1(D_4, p_5)` such that `f(Φ)·Γ` is a proper product,
    `f(Φ)·Γ` and `Γ` both satisfy the parity condition, and their intersection numbers with `α`
    differ;
  - B4 (Lemma 4.2, Proposition 5.1): the parity condition means the Moody polynomial has no
    cancellations, and a proper product puts the arcs in minimal position, so different
    intersection numbers force different Moody polynomials;
  - B5 (Moody, Theorem 2.3): if `𝕄_{Ψ·Γ} ≠ 𝕄_Γ` for some `Γ ∈ B_n`, then `Ψ ∉ ker ρ_n`;
    applied with `n = 5` and `Ψ = f(Φ)`;
  - B6: `f(Φ) ∉ ker ρ_5` implies `Φ ∉ ker ρ_4`.
- **Step C** (Corollary 1.1): the Jones representation of `B_4` is faithful.

## 2. Independent checks

### 2.1 Burau detects the center

`Z(B_n) = ⟨Δ²⟩` for `n ≥ 3` (Chow). Each `ρ_n(σ_i)` has determinant `-t`, so
`det ρ_n(Δ^{2k}) = (-t)^{k n(n-1)} = t^{k n(n-1)} ≠ 1` for `k ≠ 0`. So `ρ_n` is injective on the
center. (By hand for `n = 3`: `ρ_3(σ_1σ_2) = [[0,-t],[t,-t]]` and `(σ_1σ_2)^3 = Δ²` maps to `t³ I`.)

### 2.2 Long's theorem: reconstruction for n ≥ 4

**Lemma L1.** Let `ρ` be a representation of a group `G` that is injective on `Z(G)`, and let
`N ⊴ G` with `C_G(N) = Z(G)`. Then `ρ` is faithful iff `ρ|_N` is faithful.

Proof. `K = ker ρ` is normal. If `K ∩ N = 1`, then `[K, N] ⊂ K ∩ N = 1`, so
`K ⊂ C_G(N) = Z(G)`, and `K ⊂ Z(G) ∩ ker ρ = 1`. ∎

**Lemma L2.** For `n ≥ 4` and `N ⊴ B_n` not contained in `Z(B_n)`: `C_{B_n}(N) = Z(B_n)`.

Proof, with standard inputs named:

- (i) `B_n / Z(B_n)` is isomorphic to `M`, the stabilizer of one marked point in
  `MCG(S_{0,n+1})` (Birman).
- (ii) Ivanov: a subgroup of a mapping class group with no pseudo-Anosov element is finite or
  has a nonempty canonical reduction system, and the canonical reduction system is natural under
  conjugation.
- (iii) Mapping class groups are virtually torsion-free, so torsion subgroups are finite.
- (iv) For `S_{0,m}` with `m ≥ 5`, `MCG` acts faithfully on `PML`. Stable laminations of
  pseudo-Anosov elements of any finite-index subgroup are dense in `PML`.
- (v) The centralizer of a pseudo-Anosov mapping class is virtually cyclic (McCarthy).

Step 1: `M` has no nontrivial finite normal subgroup. If `T ⊴ M` is finite, a finite-index
`M' ⊂ M` centralizes `T`. Any `c ∈ T` fixes the stable lamination of every pseudo-Anosov in `M'`,
a dense set in `PML`, so `c` acts trivially on `PML` and `c = 1` by (iv).

Step 2: `N̄ = N Z / Z ≠ 1` contains a pseudo-Anosov element. Otherwise, by (ii), `N̄` is finite,
hence trivial by Step 1, or `N̄` has a nonempty canonical reduction system that `M` permutes.
`M` contains pseudo-Anosov elements, which fix no curve system. Contradiction.

Step 3: take pseudo-Anosov `g ∈ N̄` and `h ∈ M` with `g` and `h g h^{-1}` independent (no common
power). If `c ∈ C_{B_n}(N)`, its image `c̄` centralizes both. By (v), `c̄` has finite order, since
an element of infinite order would have a power in both cyclic groups. So `C_{B_n}(N)/Z` is a
normal torsion subgroup of `M`. It is finite by (iii) and trivial by Step 1, so
`C_{B_n}(N) = Z(B_n)`. ∎

With 2.1 this gives Long's theorem for `n ≥ 4`: `ρ_n` is faithful iff it is faithful on any normal
noncentral subgroup. It is only applied with `n = 4`.

### 2.3 Brun_4 is a nontrivial, noncentral normal subgroup, and free

- **Normal.** Conjugating by `g ∈ B_n` permutes the strand-deletion maps up to conjugation in
  `B_{n-1}`. So their common kernel on `P_n` is normal.
- **Inside `K_4`.** Deleting `p_4` kills a Brunnian braid, and the kernel of `P_4 → P_3` is
  `K_4 = push(π_1(D_3, p_4))` (Birman exact sequence, push map injective).
- **Description.** Let `y_1, y_2, y_3` be the free basis of `π_1(D_3, p_4)` given by loops
  around `p_1, p_2, p_3`. Deleting `p_i` sends `push(γ)` to the push along `π_i(γ)`, where
  `π_i : F(y_1,y_2,y_3) → F(y_j : j ≠ i)` kills `y_i`, and that push map is injective too. Hence
  `Brun_4 = push( ∩_{i=1}^{3} ker π_i )`, a subgroup of the free group `K_4`, so it is free.
- **Nontrivial.** `push([[y_1, y_2], y_3])` is in it, and `[[y_1,y_2],y_3] ≠ 1` in `F_3`.
- **Noncentral.** `Δ^{2k}` deletes to `Δ_3^{2k} ≠ 1`, so `Brun_4 ∩ Z(B_4) = 1`.

So Step A follows from 2.2. **Agreement with the preprint.**

### 2.4 Step B1: every nontrivial Brunnian 4-braid is pseudo-Anosov

Independent proof via Nielsen–Thurston on `S_{0,5}` (points `p_1..p_4` and `∞`). Let
`1 ≠ Φ ∈ Brun_4`.

- **Periodic.** `Φ^k` is central for some `k ≥ 1`. Central Brunnian braids are trivial (2.3),
  so `Φ^k = 1`, and `B_4` is torsion-free, so `Φ = 1`.
- **Reducible.** Some power `Φ^k`, still Brunnian and nontrivial, fixes an essential curve `c`.
  Up to swapping sides, `c` encloses two or three of the punctures `p_i`, with `∞` outside.
  - *`c` encloses two punctures, say `p_1, p_2`.* `Φ^k` is a 3-braid `ψ` on the strands
    (tube, `p_3`, `p_4`), times a twist `σ_1^j` inside the tube. Deleting `p_1` collapses the tube
    to `p_2` and gives `ψ ∈ B_3`, so `ψ = 1`. Then `Φ^k = σ_1^j`; deleting `p_3` gives `σ_1^j`, so
    `j = 0`.
  - *`c` encloses three punctures `p_1, p_2, p_3`.* `Φ^k = ψ · η`, where `ψ = (p_4` circling the
    tube`)^m` and `η ∈ B_3` acts inside `c` (twisting of the tube included). Deleting `p_4` gives
    `η = 1` in `B_3`. Then `Φ^k = ψ`, and deleting `p_1` gives `(σ_2σ_1²σ_2)^m ∈ B_3` on
    `(p_2, p_3, p_4)`, so `m = 0`.

  Both cases contradict `Φ^k ≠ 1`. So `Φ` is pseudo-Anosov. **Agreement with the preprint** (its
  citation to Whittlesey is not needed for `n = 4`).

### 2.5 Step B6: the detour through B_5 points the right way

For the standard inclusion `f : B_4 → B_5` (`σ_i ↦ σ_i`, `i ≤ 3`),
`ρ̃_5(f(Φ)) = ρ̃_4(Φ) ⊕ 1` on the nose. Any other embedding of `D_4` in `D_5` missing `p_5` is
conjugate to it, and kernel membership is invariant under conjugation.

Reduced and unreduced Burau have the same kernel:

- `v = (1, ..., 1)^T` is fixed by every `ρ̃_n(σ_i)` (each row of `[[1-t,t],[1,0]]` sums to 1);
- `w = (1, t, ..., t^{n-1})` satisfies `w ρ̃_n(σ_i) = w`;
- `w v = 1 + t + ... + t^{n-1} ≠ 0`, so over `Q(t)` the representation splits as `Q(t)v ⊕ ker w`,
  that is, `ρ̃_n ≅ 1 ⊕ ρ_n`. Since `Z[t^{±1}] ⊂ Q(t)`, the kernels agree.

Hence **`f(Φ) ∈ ker ρ_5 ⟺ Φ ∈ ker ρ_4`**, and B6 is valid. The detour needs no faithfulness of
`ρ_5`, which is false (Bigelow, arXiv:math/9904100, Geom. Topol. 3 (1999) 397–404). It is also
consistent with the known kernel elements for `n = 5`: none can lie in `f(B_4)` unless `ρ_4` is
unfaithful. **Agreement.**

### 2.6 Step B5: why kernel elements preserve the Moody polynomial

`𝕄(α, β) = Σ_ℓ (t^ℓ α̃, β̃) t^ℓ` is the equivariant algebraic intersection number of lifts to the
infinite cyclic cover of `D_n` given by total winding number around the punctures.

- This cover is preserved by every mapping class fixing the boundary, and lifts are normalized
  at the lift of `p_*`. So `𝕄((x)g, (y)g) = 𝕄(x, y)`.
- The pairing depends on the arcs only through classes on which `B_n` acts through `ρ̃_n`
  (Moody; Long–Paton). This is imported, not re-proved here.
- If `Ψ ∈ ker ρ_n`, then `(β)Ψ = β` in that module, so
  `𝕄_{Ψ·Γ} = 𝕄(α, ((β)Ψ)Γ) = 𝕄((α)Γ^{-1}, (β)Ψ) = 𝕄((α)Γ^{-1}, β) = 𝕄_Γ`.

Theorem 2.3 is the contrapositive. **Direction agrees.** Still to confirm from the PDF: the
convention `𝕄_Γ := 𝕄(α, (β_*^3)Γ)` and the relative homology module used.

### 2.7 Step B4: no cancellation means the number of terms equals ι

- Put `α` and `β' = (β_*^3)Ψ` in minimal position, with intersection points `x_1, ..., x_m` in
  order along `β'`. Then `𝕄 = Σ_{i=1}^m ε_i t^{k_i}` and `m = ι(α, β')`.
- For consecutive points, the subarcs of `α` and `β'` between `x_i` and `x_{i+1}` meet only at
  those endpoints. So they bound an embedded disk `Δ_i`, and lifting the loop changes the sheet
  by the signed count of punctures in `Δ_i`. Hence `k_j - k_i = Σ_{r=i}^{j-1} W_r` (the preprint's
  Corollary 3.2).
- If a sign change happens exactly at disks with an odd number of punctures (the parity
  condition), then `k_i = k_j` forces an even number of odd disks between them, so `ε_i = ε_j`.
  Nothing cancels, and the sum of the absolute values of the coefficients of `𝕄` equals `m = ι`.
- So different `ι` gives different `𝕄`. **Agreement with the logic of Lemma 4.2.** The parity
  condition is a hypothesis about the braid, so the content is in verifying it for `f(Φ)·Γ` and
  `Γ` (Proposition 6.4).

### 2.8 Squier's form

`ρ̃_n` is unitary for a Hermitian form over `Z[s^{±1}]`, `t = s²` (Squier, Proc. AMS 90 (1984)
199–202). As extracted, the preprint's architecture never uses it, and no step above needs it.
It gives no obstruction to kernel elements, since kernel elements map to the identity, which is
unitary.

## 3. Findings of part 1

- No disagreement with the architecture. Steps A, B5, B6 and C point the right way.
- Steps A (Long) and B1 (pseudo-Anosov) are re-proved independently for `n = 4`; B6 is proved
  above.
- **Not checked here (the load-bearing core):** Proposition 5.1 (proper products are in minimal
  position), Lemmas 6.2–6.3, Proposition 6.4 in both cases, and the verification that
  `f(Φ)·Γ` and `Γ` satisfy the parity condition for every nontrivial `Φ ∈ Brun_4`.
- The extraction tool flagged two places for the line-by-line check: a figure-based isotopy in
  the proof of Lemma 6.2, and a "we can assume without loss of generality" in the second case of
  Proposition 6.4.
