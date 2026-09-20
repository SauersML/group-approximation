---
rg: 2
id: kazhdan-gapped-mapping-torus-models-are-lef-quotients-proof
kind: route
title: Proof that wraps below kappa preserve irreducible supports, by property (T) on Hilbert--Schmidt intertwiner spaces, and that gapped corona models of a Kazhdan mapping torus converge to stage-lifted LEF quotients
target: kazhdan-gapped-mapping-torus-models-are-lef-quotients
requires:
  - fpbs-shalom-property-t-is-open
  - lef-mapping-torus-iff-stage-liftable-automorphism
  - lef-implies-operator-mf
  - finite-order-unitary-has-uniform-opnorm-gap
artifacts:
  - research/kazhdan-gapped-mapping-torus-models-are-lef-quotients.md
---

Notation is as in the target. `‖·‖` is the operator norm. `‖X‖_2 = tr(X*X)^(1/2)` is the
unnormalized Hilbert--Schmidt norm, and `‖AXB‖_2 ≤ ‖A‖ ‖X‖_2 ‖B‖`.

## 1. Kazhdan pairs

`(S, κ)` is a Kazhdan pair for `K~`. So if a unitary representation `ρ` of `K~` on a Hilbert space
has a unit vector `ξ` with `max_s ‖ρ(s)ξ − ξ‖ < κ`, then `ρ` has a nonzero invariant vector. Such
a pair exists because `K~` has (T) and `S` generates it, by `fpbs-shalom-property-t-is-open`. That
node provides the finite set `R_0` of relators of `K`.

## 2. Proof of (SR1)

**Step 2a: both are representations of `K~`.** Let `U` be a model and put `U' = U ∘ ŵ`, a
homomorphism `F -> U(n)`. `U` kills `R_0 ⊆ R_Γ`. `U'` kills `R_0` because
`U'(r) = U(ŵ(r))` and `ŵ(R_0) ⊆ R_Γ`. So both factor through `K~`.

**Step 2b: `Supp U ⊆ Supp U'`.** Let `σ` be an irreducible constituent of `U` on `H_σ`, and let
`J : H_σ -> C^n` be an isometry with `U(g) J = J σ(g)` for all `g`.

On the finite-dimensional Hilbert space `HS(H_σ, C^n)`, with the inner product
`<X, Y> = tr(Y* X)`, put `ρ(g) X = U'(g) X σ(g)*`. This is a unitary representation of `K~`.

Put `X = T J / √(dim σ)`. It is a unit vector, since `‖T J‖_2 = ‖J‖_2 = √(dim σ)`. Using
`J = U(s) J σ(s)*`, we get

```text
ρ(s)X − X = ( U'(s) T − T U(s) ) J σ(s)* / √(dim σ) ,
‖ρ(s)X − X‖_2 ≤ ‖U'(s) T − T U(s)‖ = ‖U'(s) − T U(s) T*‖ ≤ δ < κ.
```

So there is a nonzero `Y ∈ HS(H_σ, C^n)` with `U'(g) Y = Y σ(g)` for all `g`. The kernel of `Y`
is `σ`-invariant, hence zero, since `σ` is irreducible. So `Y` is injective, `Y(H_σ)` is a
`U'`-invariant subspace, and `U'` restricted to it is equivalent to `σ`. Thus `σ ∈ Supp U'`.

**Step 2c: equality.** Step 2b used only two facts: `U` and `U'` are representations of `K~`, and
`‖U'(s) − T U(s) T*‖ < κ` for every `s`. Now swap the roles, putting `(U', U, T*)` in place of
`(U, U', T)`. The second fact still holds, because
`‖U(s) − T* U'(s) T‖ = ‖T U(s) T* − U'(s)‖ < κ`. So `Supp U' ⊆ Supp U`.

**Step 2d: kernels.** A finite-dimensional unitary representation is an orthogonal direct sum of
irreducibles. So its kernel is the intersection of the kernels of its constituents, and it
depends only on the support. Hence `ker_(K~) U = ker_(K~) U'`. Both kernels in `F` contain
`<<R_0>>`, so they are the preimages of these, and `ker_F U = ker_F U'`.

**Step 2e: the automorphism.** Define `α : M -> M` by `α(U(x)) = U(ŵ(x))`.

- *Well defined and injective.* `U(x) = U(y)` iff `x^-1 y ∈ ker U = ker U'` iff
  `U(ŵ x) = U(ŵ y)`.
- *Takes values in `M`.* `U(ŵ(x)) ∈ U(F) = M`.
- *A homomorphism.* `ŵ` is a homomorphism of `F`.
- *Onto.* `s = ŵ(v_s) r_s` in `F`, and `U(r_s) = 1`, so `U(s) = U(ŵ(v_s)) = α(U(v_s))`. The
  `U(s)` generate `M`.

Finally, `α(U(s)) = U(w_s)` by definition. This proves (SR1). Finiteness of `M` was not used, and
neither was any structure of `U` or `T`.

## 3. Proof of (SR2)

Let `π`, `c` and `U_i` be as in (SR2). Write `π(t) = [T_i]` with unitaries `T_i`. This is
possible: lift `π(t)` to `(x_i)` with `‖x_i* x_i − 1‖, ‖x_i x_i* − 1‖ -> 0`. For large `i`,
`x_i` is invertible, and its unitary polar part `T_i` satisfies `‖T_i − x_i‖ -> 0`. For the
finitely many small `i`, put `T_i = 1`.

For `u ∈ F`, multiplicativity of `[·]` gives `π(ū) = [U_i(u)]`, where `ū` is the image of `u`
in `K`.

**Step 3a: relators become exact.** Let `r ∈ F` be a relator of `K`. Then `[U_i(r)] = π(1) = 1`,
so `‖U_i(r) − 1‖ -> 0`. By the gap, `U_i(r) = 1` for all large `i`. Since `R_Γ` is finite, `U_i`
is a model for all `i ≥ i_0`.

**Step 3b: wraps become small.** In `G`, `t s t^-1 = w_s`. So
`[T_i U_i(s) T_i*] = π(t) π(s) π(t)* = π(w_s) = [U_i(w_s)]`. Hence

```text
δ_i = max_s ‖T_i U_i(s) T_i* − U_i(w_s)‖ -> 0.
```

Enlarging `i_0`, we get `δ_i < κ` for `i ≥ i_0`. By (SR1), each `M_i = U_i(F)` then carries an
automorphism `α_i` with `α_i(U_i(x)) = U_i(ŵ(x))` for all `x ∈ F`.

**Step 3c: the images are finite.** A `c`-gapped subgroup `M_i` of the compact group `U(n_i)` is
finite. If it were infinite, it would have distinct elements `a ≠ b` with `‖a − b‖ < c`. Then
`a^-1 b ≠ 1` and `‖a^-1 b − 1‖ = ‖b − a‖ < c`, which contradicts the gap.

**Step 3d: a convergent subsequence that sees `k`.** Let `k̃ ∈ F` represent `k`. Since
`π(k) = [U_i(k̃)] ≠ 1`, the set `I_1 = {i ≥ i_0 : U_i(k̃) ≠ 1}` is infinite. Put
`N_i = ker U_i ⊴ F`. Enumerate `F` and extract diagonally an infinite `I_2 ⊆ I_1` such that, for
every `u ∈ F`, either `u ∈ N_i` for all but finitely many `i ∈ I_2`, or `u ∉ N_i` for all but
finitely many `i ∈ I_2`.

Let `N_∞` be the set of `u` of the first kind. It is a normal subgroup of `F`, and
`(M_i, S) = (F/N_i, S)` converges to `(F/N_∞, S)` along `I_2`. Also:

- `k̃ ∉ N_∞`, because `k̃ ∉ N_i` for every `i ∈ I_2`;
- every relator of `K` lies in `N_∞`, by Step 3a.

So `L = F/N_∞` is a quotient `K/N` of `K`, with `N = N_∞/<<rel(K)>>` and `k ∉ N`.

**Step 3e: `N` is `φ`-invariant.** Let `u ∈ N_∞`. For large `i ∈ I_2`,
`U_i(ŵ u) = α_i(U_i(u)) = 1`, so `ŵ(u) ∈ N_∞`. Next, `ŵ(v̂(u)) u^-1` is a relator of `K`, since
`φ(φ^-1(ū)) = ū`. So for large `i`,

```text
α_i(U_i(v̂ u)) = U_i(ŵ v̂ u) = U_i(u) = 1,
```

hence `U_i(v̂ u) = 1` and `v̂(u) ∈ N_∞`. In `K`, `ŵ` and `v̂` induce `φ` and `φ^-1`. So
`φ(N) ⊆ N` and `φ^-1(N) ⊆ N`, that is, `φ(N) = N`. Let `φ̄` be the induced automorphism of `L`;
`w_s` and `v_s` represent `φ̄(s)` and `φ̄^-1(s)` in `L`.

**Step 3f: LEF.** Along `I_2`, the finite marked groups `(M_i, S)` converge to `(L, S)`, and
`α_i ∈ Aut(M_i)` satisfies `α_i(U_i(s)) = U_i(w_s)`, so it is a stage lift of `φ̄`. By
`lef-mapping-torus-iff-stage-liftable-automorphism` ((b) implies (a)), `L ⋊_φ̄ Z` is LEF. By
`lef-implies-operator-mf`, it is operator MF.

The map `G -> L ⋊_φ̄ Z` is onto, with kernel `N × {0}`. Composing it with an embedding of the MF
group `L ⋊_φ̄ Z` into `U(Q)` gives a homomorphism `G -> U(Q)` whose kernel is `N`, which does not
contain `k`. So `k ∉ Rad_MF(G)`. This proves (SR2).

## 4. Proof of (SR3)

(SR2) is the forward implication.

Conversely, let `H = (K/N) ⋊ Z` be LEF with `k ∉ N`. Choose finite groups `E_j` with maps
`ι_j : H -> E_j` that are multiplicative and injective on the ball of radius `j`, and put
`ρ(h) = [λ_(E_j)(ι_j(h))]`. This is the construction of `lef-implies-operator-mf`: it is an
injective homomorphism `H -> U(Q)`.

Composing it with `G -> H` gives `π`. For `s ∈ S`, `π(s) = [U_j(s)]`, where `U_j` is the
homomorphism `F -> Sym(E_j) ⊂ U(ℓ² E_j)` given by `s ↦ λ(ι_j(s̄))`. This is a permutation model,
so it is `√3`-gapped. And `π(k) ≠ 1`.

## 5. Proof of (SR4) and of the gap table

**(SR4)** follows from (SR2): if `Rad_MF(G) = K`, no `k ∈ K` survives in any homomorphism to
`U(Q)`. The finite-dimensional remark in the target is (SR1), together with the fact that a
finite quotient of `G` that is nontrivial on `K` gives a nontrivial finite quotient of `K`.

**The gap table.**

- *Permutation matrices.* Let `P ≠ 1` be a permutation matrix. Then `P` has a cycle of length
  `ℓ ≥ 2`, so every `ℓ`-th root of unity is an eigenvalue of `P`. Hence
  `‖P − 1‖ ≥ 2 sin(π ⌊ℓ/2⌋ / ℓ) ≥ 2 sin(π/3) = √3`. Regular representations are permutation
  representations. Direct sums keep the gap, because `‖⊕ A_j − 1‖ = max_j ‖A_j − 1‖`.
- *Rational characters.* Let `U(g) ≠ 1` have finite order, with a Galois-stable spectrum. Some
  eigenvalue is a primitive `d`-th root of unity with `d ≥ 2`, so every primitive `d`-th root
  occurs. It suffices to find `k` coprime to `d` with `2 sin(π k/d) ≥ 1`:
  - for `d` odd, `k = (d−1)/2` works and gives `2 cos(π/2d) ≥ √3`;
  - for `d = 2e` with `e` even, `k = e − 1` gives `2 cos(π/2e) ≥ √2`;
  - for `d = 2e` with `e ≥ 3` odd, `k = e − 2` gives `2 cos(π/e) ≥ 1`;
  - for `d = 2`, the value is `2`.
- *Exponent `N`.* This is `finite-order-unitary-has-uniform-opnorm-gap`.

## Imports

- Shalom's openness of (T) (`fpbs-shalom-property-t-is-open`), which is ESTABLISHED as a citation
  import.
- The stage-lift criterion (`lef-mapping-torus-iff-stage-liftable-automorphism`) and
  `lef-implies-operator-mf`, both ESTABLISHED.
- `finite-order-unitary-has-uniform-opnorm-gap`, ESTABLISHED, used only for the last row of the
  table.

Everything else is elementary: the definition of a Kazhdan pair, Schur's lemma, complete
reducibility, compactness of `U(n)`, and compactness of the space of marked groups.
