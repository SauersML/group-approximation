---
rg: 2
id: rf-kazhdan-group-not-flexibly-hs-stable-proof
kind: route
title: Give the Heisenberg cover property (T); a rounding makes the bimodule vector almost invariant, but the centre acts by a nontrivial scalar
target: rf-kazhdan-group-not-flexibly-hs-stable
requires:
  - elementary-linear-semidir-pair-relative-t
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - bdhv-central-extension-property-t
---

Notation is as in the claim, with `g >= 2`. `e_i` and `f_i = e_(g+i)` form the symplectic basis,
and `Π_i = Z e_i + Z f_i` is the `i`-th plane.

## 1. Residual finiteness

Reduction mod `k` gives homomorphisms `θ_k : Γ_g -> (Z/k)^(2g) ⋊ Sp_(2g)(Z/k)`. For
`(v,A) ≠ (0,1)`, take `k` larger than every entry of `v` and of `A - 1`. Then
`θ_k(v,A) ≠ 1`.

## 2. Property (T) of Γ_g

**(a) The quotient.** `Sp_(2g)(Z)` has (T). It is a quotient of the universal-cover lattice,
which has (T) by `deligne-universal-cover-lattice-is-non-rf-kazhdan` (item 3, with
`n = g >= 2`), and (T) passes to quotients. Fix a Kazhdan pair `(S_0, κ_0)` for
`Sp_(2g)(Z)`, embedded in `Γ_g` as the elements `(0,A)`.

**(b) Planes.** Let `SL_2(Z)_i` act on `Π_i` in the standard way and trivially on the other
planes. These matrices are symplectic, so `H_i = Π_i ⋊ SL_2(Z)_i <= Γ_g`, and
`H_i ≅ R^2 ⋊ EL_2(R)` for `R = Z`. By `elementary-linear-semidir-pair-relative-t` there are a
finite `S_i ⊂ H_i` and `κ_i > 0` such that every unitary representation of `H_i` with an
`(S_i, κ_i)`-invariant unit vector has a nonzero `Π_i`-invariant vector. Put
`κ_1 = min_i κ_i`.

**(c) The relative estimate on one plane.** Let `π` be a unitary representation of `Γ_g` on
`H`, and `P_i` the projection onto `H^(Π_i)`.
- `Π_i` is normal in `H_i`, so `H^(Π_i)` and its orthogonal complement are `H_i`-invariant.
- The complement has no nonzero `Π_i`-invariant vector, hence no `(S_i, κ_i)`-invariant unit
  vector.
- `π(s)` commutes with `P_i` for `s ∈ H_i`. So for every vector `ξ`:

```text
κ_1 ||ξ - P_i ξ||  <=  max_(s∈S_i) ||π(s)(ξ - P_i ξ) - (ξ - P_i ξ)||  <=  max_(s∈S_i) ||π(s)ξ - ξ||.
```

**(d) The whole module.** The `P_i` are spectral projections of the representation
`π|Z^(2g)` of an abelian group, so they commute. `P_N = P_1···P_g` is the projection onto
`H^(Z^(2g))`. Let `S = S_0 ∪ S_1 ∪ ... ∪ S_g`, let `ξ` be a unit vector, and put
`δ = max_(s∈S) ||π(s)ξ - ξ||`. Telescoping gives

```text
||ξ - P_N ξ||  <=  Σ_i ||ξ - P_i ξ||  <=  g δ / κ_1.
```

**(e) Conclusion.**
- `H^(Z^(2g))` is `Γ_g`-invariant because `Z^(2g)` is normal, and `Γ_g` acts on it through
  `Sp_(2g)(Z)`.
- Put `η = P_N ξ`. `P_N` commutes with `π(Γ_g)`, so `||π(s)η - η|| <= δ` for `s ∈ S_0`, and
  `||η|| >= 1 - gδ/κ_1`.
- Suppose `δ < min(κ_1/(2g), κ_0/2)`. Then `||η|| > 1/2`, so `η/||η||` is
  `(S_0, κ_0)`-invariant. Hence `H^(Z^(2g))` contains a nonzero `Sp_(2g)(Z)`-invariant vector,
  which is `Γ_g`-invariant.
- So `(S, min(κ_1/(2g), κ_0/2))` is a Kazhdan pair for `Γ_g`.

## 3. Property (T) of the Heisenberg cover

Let `Γ~_g = Z^(2g) × Z × Sp_(2g)(Z)` with product `(v,s,A)(w,t,B) = (v+Aw, s+t+ω(v,Aw), AB)`.
- **Group law.** Associativity reduces to `ω(Aw, ABu) = ω(w, Bu)`, which holds because `A` is
  symplectic.
- **The centre.** `z = (0,1,1)` is central, and `(v,s,A) -> (v,A)` induces
  `Γ~_g/⟨z⟩ ≅ Γ_g`.
- **Generators.** Let `x_w = (w,0,1)` and `y_A = (0,0,A)`. Then `(v,s,A) = x_v z^s y_A`, so
  these elements and `z` generate `Γ~_g`.
- **Finite abelianization.**
  - The commutator `[x_v, x_w]` equals `z^(2ω(v,w))`, so `z^2 ∈ [Γ~_g, Γ~_g]`.
  - `y_A x_w y_A^(-1) = x_(Aw)` and `x_w x_u = z^(ω(w,u)) x_(w+u)`. So `φ(w) = [x_w]` is a
    homomorphism `Z^(2g) -> ab/⟨[z]⟩` that is constant on `Sp_(2g)(Z)`-orbits.
  - The transvection `T_u(x) = x + ω(u,x)u` is symplectic, and `(T_u - 1)x = ω(u,x)u`. So the
    coinvariants of `Z^(2g)` vanish, and `φ` takes values in `⟨[z]⟩`, which has order at most 2.
  - `Sp_(2g)(Z)` is Kazhdan (§2a), hence has finite abelianization. Therefore `Γ~_g^(ab)` is
    finite.
- **Conclusion.** Apply `bdhv-central-extension-property-t` with `C = ⟨z⟩`; `Γ~_g/C = Γ_g` is
  Kazhdan by §2. So `Γ~_g` has (T). Fix a Kazhdan pair `(K, κ)` for `Γ~_g`.

## 4. The models

**Construction.** For `k >= 3`, let `Q~_k = (Z/k)^(2g) × Z/k × Sp_(2g)(Z/k)` with the same
formula, and let `θ~_k : Γ~_g -> Q~_k` be reduction. Let `λ` be the left regular representation
of `Q~_k`, and let

```text
E = (1/k) Σ_(j<k) e^(-2πij/k) λ(z̄^j),
```

the central projection onto the subspace where `z̄` acts by `e^(2πi/k)`. Since `z̄` acts freely
by translation, `rank E = |Q~_k|/k =: d_k`. Put `ρ~_k = (λ∘θ~_k)` restricted to `E ℓ^2(Q~_k)`.
It is a genuine unitary representation of `Γ~_g` with `ρ~_k(z) = e^(2πi/k)`.

**Defect.** With `s(v,A) = (v,0,A)` one has `s(g)s(h) = z^(c(g,h)) s(gh)`, where
`c((v,A),(w,B)) = ω(v,Aw)`. So `α_k = ρ~_k∘s` satisfies
`α_k(g)α_k(h) = e^(2πic(g,h)/k) α_k(gh)`. It is an asymptotic representation whose
operator-norm defect is at most `2π|c(g,h)|/k`.

**Trace.** The normalized trace of `α_k(g)` is `e^(2πim/k)` if `θ~_k(s(g)) = z̄^m`, and `0`
otherwise. For `g = (v,A) ≠ 1`, `θ~_k(v,0,A)` lies in `⟨z̄⟩` only if `v ≡ 0` and `A ≡ 1` mod `k`.
That fails for large `k`, so `tr α_k -> δ_e`.

## 5. No flexible rounding

Fix a finite generating set `F` of `Γ_g`. Suppose that, along a subsequence, there are genuine
`π_k : Γ_g -> U(D_k)` with `D_k >= d_k`, `D_k/d_k -> 1`, and
`||α_k(g) - P_k π_k(g) P_k*||_(2,d_k) -> 0` for every `g ∈ F`. Here `P_k : C^(D_k) -> C^(d_k)`
keeps the first `d_k` coordinates.

**The bimodule representation.**
- Let `H_k = M_(d_k × D_k)(C)` with inner product `⟨ξ,η⟩ = Tr(η*ξ)/d_k`, and
  `σ_k(x)ξ = ρ~_k(x) ξ π_k(q(x))*`, where `q : Γ~_g -> Γ_g` is the quotient map.
- `σ_k` is a genuine unitary representation of `Γ~_g`.
- `σ_k(z) = e^(2πi/k)·1 ≠ 1`, so `σ_k` has no nonzero invariant vector.

**Almost invariance of `P_k`.** `||P_k|| = 1`. For `g ∈ Γ_g`, using `P_k P_k* = 1`:

```text
||σ_k(s(g))P_k - P_k||^2  =  ||α_k(g) - P_kπ_k(g)P_k*||_(2,d_k)^2 + ||P_kπ_k(g)(1 - P_k*P_k)||_(2,d_k)^2
                          <=  ||α_k(g) - P_kπ_k(g)P_k*||_(2,d_k)^2 + (D_k - d_k)/d_k.
```

Also `||σ_k(z)P_k - P_k|| = |e^(2πi/k) - 1|`.

**Propagation to the Kazhdan set.**
- `Γ~_g` is generated by `s(F) ∪ {z}`, because `(v,s,A) = z^s s(v,A)` and
  `s(g)s(h) = z^c s(gh)`.
- For a word `x` in these letters and their inverses, `||σ_k(x)P_k - P_k||` is at most the sum
  of the letters' contributions.
- Hence `max_(x∈K) ||σ_k(x)P_k - P_k|| -> 0`.

**Contradiction.** For large `k` this maximum is `< κ`, so `σ_k` has a nonzero invariant
vector. This contradicts the bimodule observation above.

**Quantitative form (claim item 3).**
- Let every `x ∈ K` be a word of length `<= L` in `s(F)^(±1) ∪ {z^(±1)}`.
- Suppose `d_k <= D <= (1+ε)d_k` and `max_(g∈F) ||α_k(g) - Pπ(g)P*||_2 < ε`. Then each letter
  moves `P` by at most `max(ε + √ε, 2π/k)`.
- With `ε = min(1, (κ/(3L))^2)` and `k > 6πL/κ`, the total is `< κ`, which is the same
  contradiction.

## 6. Relation to Ioana--Spaas--Wiersma Theorem A

Take `Λ = Π_1`. The pair `(Γ_g, Λ)` has relative property (T) by §2. For `k >= 3`,
`c_k = exp(2πic/k)` satisfies `c_k(e_1,f_1) = e^(2πi/k) ≠ e^(-2πi/k) = c_k(f_1,e_1)`. So
`c_k|Λ` is not symmetric, hence not a coboundary. Moreover `c_k -> 1` pointwise, and `c_k`
factors through `(Z/k)^(2g) ⋊ Sp_(2g)(Z/k)`, whose twisted regular representation realizes it.

So `Γ_g` satisfies the hypotheses of ISW Theorem A (arXiv:2006.01874v2), and ISW's remark
after their definition of HS-stability gives the same conclusion by a different proof. The
argument above replaces their lifting step by property (T) of the Heisenberg cover.
