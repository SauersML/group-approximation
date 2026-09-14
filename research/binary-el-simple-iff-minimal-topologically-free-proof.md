---
rg: 2
id: binary-el-simple-iff-minimal-topologically-free-proof
kind: route
title: Proof of the simplicity criterion, by the manuscript's tower argument forward and the Steinberg criterion backward
target: binary-el-simple-iff-minimal-topologically-free
requires:
  - clopen-towers-at-every-scale-iff-topologically-free
  - steinberg-algebra-simple-iff-minimal-effective
  - crossed-products-are-transformation-steinberg-algebras
artifacts:
  - research/artifacts/sk-strong-4-boundaries-2026-09-13-part1.md
---

Full derivations in the artifact, §3 to §5.

**Forward.** Let `1 ≠ N ⊴ EL_n(R)` and `1 ≠ g ∈ N`. Choose a finite symmetric `B ∋ e` with every
entry of `g` and `g^{-1}` in `Σ_{γ∈B} LC(X,F_2)u_γ`, and a finite clopen partition `𝒫` on which
every `f∘α` is constant, for `α ∈ B` and `f` a coefficient of an entry of `g` or `g^{-1}`. Call
`V` admissible if it is nonempty clopen, `(B^{-1}B)`-free and inside one atom of `𝒫`.

- *Choice of the root (artifact Proposition 3).* Commuting with `e_{ij}(r)` says `g_{pi}r = 0` for
  `p ≠ i`, `r g_{jq} = 0` for `q ≠ j`, and `g_{ii}r = r g_{jj}`. With `r = e_V` and uniqueness of
  coefficients, each condition says a locally constant function vanishes on `γV` or on `V`. By the
  density statement of the tower claim, if `g` commutes with every `e_{ij}(e_V)` for admissible
  `V`, all off-diagonal entries vanish, all diagonal entries agree with one `c ∈ LC(X,F_2)`, and
  `c` is a unit of `LC(X,F_2)`, so `c = 1` and `g = I_n`. So some `h = e_{ij}(e_V)` with `V`
  admissible fails to commute with `g`, and `k = [g,h] ∈ N \ {1}`. This also gives
  `Z(EL_n(R)) = 1`.
- *The tower group (Proposition 4).* With `d = n|B|` and `ε_{αβ} = e_{αV}u_{αβ^{-1}}`, the
  `(B^{-1}B)`-freeness of `V` gives `ε_{αβ}ε_{α'β'} = δ_{βα'}ε_{αβ'}`, so
  `ψ(E_{(p,α),(q,β)}) = ε_{αβ}E_{pq}` is an injective multiplicative linear map `M_d(F_2) → M_n(R)`
  and `H = {I_n − ψ(I_d) + ψ(A)} ≅ GL_d(F_2)` lies in `EL_n(R)` for `n ≥ 3`, by the manuscript's
  transvection identities.
- *The commutator (Proposition 5).* The constancy on atoms makes every product
  `(fu_α)e_V(f'u_β)` either `0` or `ε_{α,β^{-1}}`, so `k − I_n = (ghg^{-1} − h)h` and
  `k^{-1} − I_n = h(ghg^{-1} − h)` lie in `ψ(M_d(F_2))` and `k ∈ H`.
- *Conclusion.* `GL_d(F_2) = PSL_d(F_2)` is simple for `d = n|B| ≥ 3`, so `H ⊆ N` and
  `e_{pq}(e_V) ∈ N`. The level `J = {r : e_{pq}(r) ∈ N ∀ p ≠ q}` is a two-sided ideal containing
  every `e_{γV} = u_γ e_V u_γ^{-1}`; by minimality `⋃_γ γV = X`, and compactness gives a finite
  subcover, so `1 = 1 − Π_i(1 − e_{γ_iV}) ∈ J` and `N = EL_n(R)`.

**Backward.** If the action is not minimal or not topologically free, then the transformation
groupoid `Γ ⋉ X` is Hausdorff and ample with Steinberg algebra `R`
(`crossed-products-are-transformation-steinberg-algebras`), and it fails to be minimal or
effective, so `R` is not simple by `steinberg-algebra-simple-iff-minimal-effective`. Take an ideal
`I` with `0 ≠ I ≠ R`. Then `EL_n(R,I)`, the normal closure of `{e_{ij}(a) : a ∈ I}`, is a normal
subgroup of `EL_n(R)`; it is nontrivial because `e_{12}(a) ≠ I_n` for `0 ≠ a ∈ I`, and it is
proper because `EL_n(R) → EL_n(R/I)` is onto with `EL_n(R,I)` inside its kernel while
`EL_n(R/I) ≠ 1`, since `1 ≠ 0` in `R/I` gives `e_{12}(1) ≠ I_n`. So `EL_n(R)` is not simple.
