---
rg: 2
id: aut-out-free-abelianized-extension-virtually-splits-proof
kind: route
title: Dividing the Fox determinant cocycle by n minus one on the subgroup where it is divisible gives a section of the abelianized extension
target: aut-out-free-abelianized-extension-virtually-splits
requires:
  - aut-out-free-abelianized-extension-splits-rationally
---

Notation as in the target. The only input is item 1 of
`aut-out-free-abelianized-extension-splits-rationally` (proof route
`aut-out-free-abelianized-extension-proof`): `h` is a crossed homomorphism,
`h(φψ) = h(φ) + φ_* h(ψ)`, with `h(ι_g) = (n − 1)[g]`. Write `m = n − 1`.

1. **Finite index.** Put `M = H/mH`, a finite group, and let `GL(M)` act on it.
   The map `Φ: Aut(F_n) → M ⋊ GL(M)`, `φ ↦ (h(φ) mod m, φ_* mod m)`, is a
   homomorphism: `(h(φ), φ_*)·(h(ψ), ψ_*) = (h(φ) + φ_* h(ψ), φ_*ψ_*)
   = (h(φψ), (φψ)_*)`. Its target is finite, and
   `A_n = Φ^{-1}({0} × GL(M))` is a subgroup of finite index.
   `h(ι_g) = m[g] ∈ mH`, so `Inn(F_n) ≤ A_n`.
2. **Well defined on outer classes.** `h(φ ι_g) = h(φ) + φ_*(m[g]) ≡ h(φ) mod mH`.
   So membership in `A_n` depends only on `[φ]`, and `Γ_n = π(A_n)` has finite
   index in `Out(F_n)`.
3. **The crossed homomorphism k.** `H` is torsion free and `φ_*` is linear, so
   `k = h/m: A_n → H` is well defined and satisfies
   `k(φψ) = k(φ) + φ_* k(ψ)`. Also `k(ι_g) = [g]`.
4. **K_n is a subgroup.** If `k(φ) = k(ψ) = 0` then `k(φψ) = 0`, and
   `0 = k(φφ^{-1}) = k(φ) + φ_* k(φ^{-1})` gives `k(φ^{-1}) = 0`.
5. **K_n meets the inner automorphisms in Inn([F_n,F_n]).** `k(ι_g) = [g] = 0`
   exactly when `g ∈ [F_n, F_n]`.
6. **K_n · Inn(F_n) = A_n.** Given `φ ∈ A_n`, choose `g ∈ F_n` with
   `[g] = −φ_*^{-1}k(φ)`. Then `k(φ ι_g) = k(φ) + φ_*[g] = 0`, so
   `φ ι_g ∈ K_n`.
7. **Conclusion.** By 5 and 6, `K_n / Inn([F_n,F_n])` maps isomorphically onto
   `A_n / Inn(F_n) = Γ_n`. This is a subgroup of `Aut(F_n)/Inn([F_n,F_n])` that
   is a complement to `H = Inn(F_n)/Inn([F_n,F_n])` over `Γ_n`. So the extension
   splits over `Γ_n`, and `c|_{Γ_n} = 0`. For `n = 2`, `m = 1` and `A_2 = Aut(F_2)`.

**Scope check.** Nothing here uses the rank beyond `n ≥ 2`, the landed
cocycle identity, or any unread source. A second, independent proof goes
through the free nilpotent quotient `N = F_n/γ_3F_n`: the extension is pulled
back from `1 → Inn(N) → Aut(N) → Out(N) → 1`, the level-2 congruence subgroup
of `GL_n(Z)` lifts to `Aut(N)` through the Mal'cev logarithm, and the
equivariant contraction `Hom(H, Λ²H) → H`, which restricts to `(1 − n)` on
`H`, divided by `1 − n` is integral on `H + (n − 1)Hom(H, Λ²H)`. That proof
is recorded as a check only; the route above does not depend on it.
