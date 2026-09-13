# Layered Schrödinger--Weil models: a totally non-roundable, normalizing actor model at one strict compressor

Lane `ex2-ft-actor-models`, 2026-09-13. Unreviewed.

Question: can an actor model of an infranormal pair with a residually finite Kazhdan vertex be totally
non-roundable on the vertex, and can it at the same time normalize the vertex commutant? At the Theorem E pair
both are open (`kt-actor-model-with-totally-non-roundable-vertex`). Here both hold at an explicit pair with one
strict compressor. The ingredients are a rational degree-two class on the vertex and Følner layers along the
compressor.

## 0. Setting

- `g >= 2`, `p` a prime, `Λ = Z^(2g)`, `ω(x,y) = Σ_i (x_i y_(g+i) - x_(g+i) y_i)`.
- `Γ = Λ ⋊ Sp_(2g)(Z)`, with `(v,A)(w,B) = (v + Aw, AB)`. It is residually finite and Kazhdan
  (`rf-kazhdan-group-not-flexibly-hs-stable`).
- `φ(v,A) = (pv, A)` is an injective endomorphism of `Γ`.
- `V = Γ *_φ = <Γ, t | tγt^(-1) = φ(γ)>` is the ascending HNN extension. It is isomorphic to
  `Z[1/p]^(2g) ⋊ (Sp_(2g)(Z) × <t>)`, with `t` acting by `v -> pv`.
  - Every element has a normal form `t^(-a) γ t^b` with `a, b >= 0`.
  - `N_V = <<Γ>>_V = Z[1/p]^(2g) ⋊ Sp_(2g)(Z) = ∪_a t^(-a)Γt^a`.
- **The pair is infranormal and non-normal.** `tΓt^(-1) = pΛ ⋊ Sp_(2g)(Z)` is a proper subgroup of `Γ`, of index
  `p^(2g)`, and `t^(-1)Γt` is not contained in `Γ`.
- `V` is not Kazhdan: `t` spans a `Z` quotient.

## 1. The Heisenberg cover and its transport

- **The cover.** `Γ~ = {(v,s,A)}`, with `(v,s,A)(w,u,B) = (v + Aw, s + u + ω(v,Aw), AB)`. This is the integral
  Heisenberg cover of `rf-kazhdan-group-not-flexibly-hs-stable`.
  - It is a group: `c((v,A),(w,B)) = ω(v,Aw)` satisfies the cocycle identity, because `ω(Aw, ABu) = ω(w, Bu)`.
  - It is Kazhdan (that node's proof).
  - The kernel of `Γ~ -> Γ` is the central `<z>`, `z = (0,1,1)`.
  - The section is `s(v,A) = (v,0,A)`.
- **Transport.** `φ~(v,s,A) = (pv, p^2 s, A)` is an endomorphism of `Γ~`, since `ω(pv, Apw) = p^2 ω(v,Aw)`.
  It covers `φ`, satisfies `φ~∘s = s∘φ`, and sends `z` to `z^(p^2)`.

## 2. Finite Schrödinger--Weil representations

Let `ℓ` be a prime with `ℓ ∤ 6p`, and let `Γ~_ℓ = Γ~ mod ℓ = H_ℓ ⋊ Sp_(2g)(F_ℓ)`, where `H_ℓ = F_ℓ^(2g) × F_ℓ`
carries the same law.

1. **Schrödinger representations.** For `c ∈ F_ℓ^×` there is a unique irreducible representation `S_c` of `H_ℓ`
   in which `z` acts by `e(c/ℓ)`, where `e(x) = exp(2πix)`. It has dimension `ℓ^g`.
   - The commutator of `(v,0)` and `(w,0)` is `z^(2ω(v,w))`, and `2c ≠ 0`.
   - Hence the pairing is nondegenerate, and Stone--von Neumann applies.
2. **Weil extension.** `A ∈ Sp_(2g)(F_ℓ)` fixes `z`, so `S_c∘A ≅ S_c`. This gives a projective representation
   of `Sp_(2g)(F_ℓ)`.
   - For `g >= 2` and `ℓ >= 5` that group is perfect with trivial Schur multiplier. So the projective
     representation lifts uniquely to `W_c` with `W_c(A) S_c(h) W_c(A)^* = S_c(A·h)`.
   - `S~_c(h,A) = S_c(h) W_c(A)` is an irreducible representation of `Γ~_ℓ`.
3. **Transport intertwiners.** Since `p` is invertible mod `ℓ`, `φ~` induces an automorphism of `Γ~_ℓ` with
   `z -> z^(p^2)`.
   - `S~_c∘φ~` is irreducible with central character `p^2 c`, so its restriction to `H_ℓ` is equivalent to
     `S_(p^2 c)`.
   - Its Sp-part lifts the same projective representation, and the lift is unique.
   - Hence there is a unitary `U_c` with `U_c S~_c(φ~x) U_c^* = S~_(p^2 c)(x)` for all `x ∈ Γ~_ℓ`.
4. **Traces.** Put `S(v) = S_c(v,0)`.
   - `{S(v) : v ∈ F_ℓ^(2g)}` is an orthogonal basis of `End(C^(ℓ^g))`, because `tr S(v) = 0` for `v ≠ 0`.
   - `Ad W_c(A)` permutes this basis, since `S(v) -> S(Av)`.
   - So `|tr W_c(A)|^2 = tr Ad W_c(A) = #{v : Av = v} = ℓ^(dim ker(A-1))`.
   - For `(v,s,A)` with `A ≠ 1`: conjugating by `S(w)` with `w ∈ ker(A-1)` multiplies it by `e(2cω(w,v)/ℓ)`.
     So its trace vanishes unless `v ⊥ ker(A-1)` under `ω`, that is, `v ∈ im(A-1)`. In that case it is
     conjugate to a scalar times `W_c(A)`.
   - For `A = 1` and `v ≠ 0` the trace is 0.
   - Conclusion, in normalized trace: `|tr S~_c(v,s,A)| <= ℓ^(-rank(A-1)/2)` for `A ≠ 1`, and it is 0 when
     `A = 1` and `v ≠ 0`.

## 3. The layered model

- **Parameters.** Put `L = L(ℓ) = ⌊log ℓ / (4 log p)⌋` and `c_j = p^(2j)` for `0 <= j < L`. Then
  `0 < c_j < ℓ^(1/2)`, and the `c_j` are distinct.
- **The space.** `H = ⊕_(j<L) C^(ℓ^g)`, with `n_ℓ = L ℓ^g`.
- **The vertex.** `σ_ℓ(γ) = ⊕_j S~_(c_j)(s(γ) mod ℓ)` for `γ ∈ Γ`.
- **The compressor.** `σ_ℓ(t) = T`, where `(Tξ)_j = U_(c_j)^* ξ_(j+1)` for `j < L-1` and `(Tξ)_(L-1) = ξ_0`.

**Relations.**
1. **Vertex relations.**
   - `σ_ℓ(γ)σ_ℓ(γ') = D(γ,γ') σ_ℓ(γγ')`, with `D(γ,γ') = ⊕_j e(c_j ω(v,Aw)/ℓ)` for `γ = (v,A)`, `γ' = (w,B)`.
   - So `||D - 1|| <= 2π |ω(v,Aw)| ℓ^(-1/2)`.
2. **The HNN relation.**
   - On layer `j < L-1`: `(Tσ_ℓ(γ)T^*)_j = U_(c_j)^* S~_(p^2 c_j)(sγ) U_(c_j) = S~_(c_j)(φ~ sγ) = S~_(c_j)(s φγ)`,
     which is `σ_ℓ(φγ)_j`.
   - Only layer `L-1` is wrong. Hence `||Tσ_ℓ(γ)T^* - σ_ℓ(φγ)||_2 <= 2/√L`.

So `σ = (σ_ℓ)_U` defines a homomorphism `V -> U(prod_U M_(n_ℓ))`, as in
`one-compressor-actor-models-with-exact-origin-vertex`.

**Traces.** Take `g = t^(-a)γt^b ≠ 1`.
- If `a ≠ b`, then `σ(g)` maps layer `j` to layer `j + a - b mod L`, so its trace is 0 once `L > |a - b|`.
- If `a = b`, then `γ ≠ 1` and `T^(-a)σ(γ)T^a` is block diagonal. Off at most `a` wrap-around layers, each block
  is conjugate to some `S~_(c_j)(sγ)`.
  - So `|tr σ_ℓ(g)| <= ℓ^(-1/2) + a/L` whenever `γ ≠ 1 mod ℓ`, by §2.4.
  - This tends to 0. So `σ` is trace-preserving.

## 4. Total non-roundability

`σ|Γ = ρ∘s` with `ρ_ℓ = ⊕_j S~_(c_j)`, a genuine representation of `Γ~`.
- `||ρ_ℓ(z) - 1|| <= 2π ℓ^(-1/2)`, so (KC1) holds for the kernel `<z>`.
- `Fix_z(ρ_ℓ) = 0`, since every `c_j ≠ 0`.

Let `P ∈ R = σ(Γ)' ∩ M` be a nonzero projection.
1. **`P` commutes with `ρ(Γ~)`.**
   - `σ(v)σ(w)σ(v)^*σ(w)^* = ρ(z)^(2ω(v,w))` exactly. Choose `ω(v,w) = 1`, so `ρ(z)^2 ∈ C*(σ(Γ))`.
   - The spectrum of `ρ_ℓ(z)^2` lies on an arc of length `<= 4π ℓ^(-1/2)` at 1, where `e(x) -> e(x/2)` is
     uniformly continuous.
   - So `ρ(z)` is a continuous function of `ρ(z)^2` in the ultraproduct, and `P` commutes with it.
   - `ρ(Γ~)` is generated by `σ(Γ)` and `ρ(z)`.
2. **`P` is exactly representable.** `Γ~` is Kazhdan, so the Kazhdan corner lemma applied to `Ad ρ_ℓ` gives
   representatives `P_ℓ ∈ ρ_ℓ(Γ~)'` of `P`.
3. **The corner does not round.** The corner representation `P_ℓ ρ_ℓ` is a genuine representation of `Γ~`
   satisfying (KC1), with `Fix_z = 0`. By `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` (c), its
   restriction `P σ|Γ` does not round.

So no nonzero projection of `R` is roundable: `σ|Γ` is totally non-roundable, and `d(σ) >= κ` by Lemma C of
`compressor-extension-makes-roundable-vertex-part-invariant`.

## 5. Normalization

1. **`R` is the layer algebra.**
   - By step 1 of §4 and the Kazhdan corner lemma, `R = prod_U ρ_ℓ(Γ~)'`.
   - The `S~_(c_j)` are irreducible and pairwise inequivalent, since their central characters differ. So
     `ρ_ℓ(Γ~)' = ⊕_j C·1_j`.
   - Hence `R = prod_U ℓ^∞(L_ℓ)`, a diffuse abelian algebra.
2. **The actor normalizes it.** `T` permutes layers, the wrap-around included. So `T R T^* = R` exactly, and
   `σ(V)` normalizes `R`.
3. **`R = σ(N_V)' ∩ M`.** Each `σ(t^(-a)γt^a) = T^(-a)σ(γ)T^a` is block diagonal, so it commutes with `R`.

## 6. Reading and scope

- **Pointwise separation.** At an infranormal, non-normal pair with a residually finite Kazhdan vertex, a
  trace-preserving actor model can be totally non-roundable and normalizing at once.
  - So no argument of the form "(H1) fails at `σ`, hence `σ` does not normalize" holds at this generality.
  - At the Theorem E pair this is the first kind of witness named in
    `kt-actor-model-with-totally-non-roundable-vertex`.
- **No hyperlinear wreath from it.** The lamp argument of `kt-centralizer-normalization-hs` needs a
  non-normalized commutant. So this model does not extend to `(⊕_(V/Γ) Z/2) ⋊ V`.
- **What the construction spends.** Both are absent at the Theorem E pair.
  - **A rational class on the vertex** (`H^2(Γ; R) ≠ 0`). The vertex `EL_r(F_q[x_1..x_d])` has none in the
    stable range.
  - **Følner layers along a `Z` quotient of the actor.** `G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)` is Kazhdan and has no
    such quotient.
- **Model tests.**
  - With all `c_j = 0` the layers are genuine representations of `Γ`, the vertex rounds, and the claim fails.
  - The real object is `σ` above.
- **Scope.** `V` is not Kazhdan, so it lies outside the literal scope of `hs-stable-vertex-rounding-for-every-model`.
  The compressor has finite index `p^(2g)`, while the Theorem E compressors have infinite index.
