---
rg: 2
id: subshift-gl-exactness-reduces-to-limit-subsystem-proof
kind: route
title: The congruence kernel modulo the ultramatricial complement ideal is locally finite, so exactness passes up the extension by Kirchberg–Wassermann
target: subshift-gl-exactness-reduces-to-limit-subsystem
requires:
  - biasymptotic-subshift-complement-ideal-is-ultramatricial
  - ultramatricial-ideals-have-elementary-congruence-kernels
  - exact-groups-are-closed-under-extensions
  - commutative-ring-linear-groups-have-property-a
  - banded-matrix-groups-are-subshift-crossed-product-groups
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part2.md
---

Notation as in the target.

**Step 1 (the quotient).**
- Restriction `f ↦ f|_Z` maps `LC(Y,F_2)` onto `LC(Z,F_2)`: a clopen subset of `Z` is the trace of a clopen subset of `Y`.
- It is equivariant, so it extends to a surjective ring homomorphism `ρ: R_Y → R_Z` with kernel `I_Z = {Σ f_j u^j : f_j|_Z = 0}`.
- `ρ` induces a homomorphism `GL_m(R_Y) → GL_m(R_Z)` whose kernel is the congruence subgroup `GL_m(R_Y, I_Z)`.

**Step 2 (the kernel is locally finite).**
- By `biasymptotic-subshift-complement-ideal-is-ultramatricial`, applied to the subshift `Y` and the subsystem `Z` (this is its limit-set hypothesis), every finite subset of `I_Z` lies in a subring with a unit, isomorphic to a finite product of matrix rings `M_k(F_2)`.
- By `ultramatricial-ideals-have-elementary-congruence-kernels`, `GL_n(R_Y, I_Z)` is locally finite for `n ≥ 2`.
- For `m = 1`, `g ↦ diag(g,1)` embeds `GL_1(R_Y,I_Z)` in `GL_2(R_Y,I_Z)`. So `N = Γ ∩ GL_m(R_Y, I_Z)` is locally finite for every `m ≥ 1`.

**Step 3 (extension).**
- `N` is normal in `Γ` and `Γ/N ≅ ρ(Γ)`.
- `N` is locally finite, hence amenable, hence exact. `ρ(Γ)` is exact by hypothesis.
- By `exact-groups-are-closed-under-extensions`, `Γ` is exact. This proves the theorem.

**Step 4 (Corollary (a)).**
- **Base case.**
  - A periodic orbit `{y,…,σ^{p−1}y}` gives `LC(orbit,F_2) ⋊ Z ≅ M_p(F_2[t^{±1}])`: the matrix units are `u^i e_{σ^0 y}u^{-j}`, the corner is `F_2[u^p]`, and `e u^d e = 0` for `0 < |d| < p`.
  - So `R_{Y_d} ≅ ∏_i M_{p_i}(F_2[t^{±1}])`, and `GL_m(R_{Y_d}) = ∏_i GL_{mp_i}(F_2[t^{±1}]) ≤ GL_{mP}(S)` for `P = max p_i` and the commutative ring `S = ∏_i F_2[t^{±1}]` (pad each block by the identity).
  - By `commutative-ring-linear-groups-have-property-a`, finitely generated subgroups of `GL_m(R_{Y_d})` are exact.
- **Inductive step.** Suppose finitely generated subgroups of `GL_m(R_{Y_{i+1}})` are exact, and let `Γ ≤ GL_m(R_{Y_i})` be finitely generated. The image of `Γ` in `GL_m(R_{Y_{i+1}})` is finitely generated, hence exact, so Step 3 applied to `(Y_i, Y_{i+1})` gives exactness of `Γ`. Iterate down to `Y_0 = Y`.

**Step 5 (Corollary (b)).**
- **The orbit closure.**
  - If `y` agrees with periodic sequences at `+∞` and at `−∞`, the orbit closure is `Y = orbit(y) ∪ P_+ ∪ P_-` with `P_±` the two periodic orbits.
  - `Z = P_+ ∪ P_-` is closed and invariant, and every `x ∈ Y∖Z` is a shift of `y` with `α(x) ⊆ P_-` and `ω(x) ⊆ P_+`.
  - Corollary (a) applies with `d = 1`.
- **Banded matrices.**
  - The coding point of `banded-matrix-groups-are-subshift-crossed-product-groups`, Step 2, is a tuple of the coefficient sequences. If all of them are eventually periodic in both directions, so is the coding point.
  - The orbit representation there identifies `Γ` with a finitely generated subgroup of `GL_m(R_Y)` for this `Y`.

**Step 6 (Corollary (c)).** A filtration as in (a) whose bottom `Y_d` is an infinite minimal subshift `X` reduces, by Steps 3–4 with the base case removed, exactness of `Γ` to exactness of its image in `GL_m(R_X)`. That is the open question in rank `m`. ∎

**Model tests.**
- **Full shift.** The limit-set hypothesis forces `Z = Y`, so the theorem says nothing there ✓. The full shift carries every behaviour, and nothing is claimed.
- **Infinite minimal `Y`.** The only closed invariant subsets are `∅` and `Y`. `Z = ∅` fails the hypothesis, and `Z = Y` is vacuous ✓.
- **Lamplighter `⟨u, 1 + e_{[1]}⟩`** over the orbit closure of `…0001000…`:
  - `Z = {0^∞}`, `R_Z = F_2[t^{±1}]`, and the kernel is the finitely supported lamp group.
  - The image is `⟨t⟩ ≅ Z`, and the group is `F_2 ≀ Z`, which is exact ✓.
- **A recurrent point outside `Z`** (for example a Sturmian orbit closure plus one point asymptotic to it): the hypothesis fails for that orbit unless `Z` contains the Sturmian subsystem, which is then the bottom subsystem, as in (c) ✓.
