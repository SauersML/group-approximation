---
rg: 2
id: no-homeomorphism-shifts-primes-acting-as-l-adic-scalars
kind: claim
title: No homeomorphism of a compact space conjugates the l-adic unit actions of six primes p_0..p_5 in a chain p_k -> p_(k+1)
distinct_from:
  gl-n-q-lies-in-prime-shift-permutation-group: that realizes GL_n(Q) with a prime-shift permutation of the discrete set Q^n; this shows that no prime shift exists once the primes act through a continuous action of the l-adic units on a compact space.
  fg-piecewise-linear-hosts-omit-natural-gl-n-q: that excludes finitely generated piecewise-linear hosts through their finitely generated coefficient ring; this excludes one extra homeomorphism of any kind that shifts primes, with no finiteness hypothesis on the host.
  prime-shift-hnn-groups-are-not-finitely-presented: that is a finite-presentation obstruction for the abstract prime-shift HNN groups; this is a topological-dynamics obstruction to realizing the shift at all.
---

**ESTABLISHED** (lane proof, not reviewed). No priority claimed. One deep input, recalled and
not re-read: the **ℓ-adic six exponentials theorem** (J.-P. Serre, *Dépendance d'exponentielles
p-adiques*, Sém. Delange–Pisot–Poitou 1965/66; the ℓ-adic analogue of Lang–Ramachandra).
- *The theorem.* Let `x_1, x_2, x_3` and `y_1, y_2` in `C_ℓ` be `Q`-linearly independent triples
  and pairs, with all `x_i y_j` in the domain of `exp_ℓ`. Then some `exp_ℓ(x_i y_j)` is
  transcendental.

**Statement.** Let `ℓ` be a prime, `Y` a compact metrizable space, and `ι: Z_ℓ^× → Homeo(Y)` a
continuous injective homomorphism. Let `p_0, …, p_5` be distinct primes different from `ℓ`. Then
no `s ∈ Homeo(Y)` satisfies

    s ι(p_k) s^{-1} = ι(p_{k+1})   for k = 0, …, 4.

**Instances.**
- `Y = Z_ℓ^D` with `ι(u) =` multiplication by `u` on one coordinate. This is the diagonal of the
  hosts `W_{P,ℓ}` of `twisted-s-integral-affine-groups-are-fp-and-virtually-simple`, and of every
  compact `ℓ`-adic model in which the diagonal of `GL_1(Q)` or `GL_n(Q)` acts by `ℓ`-adic scalars.
- Scalar multiplication on `Z_ℓ^n`, on `P^{n−1}(Q_ℓ)` twisted by a character, or on any compact
  `Z_ℓ^×`-space.

So the prime-shift trick of `gl-n-q-lies-in-prime-shift-permutation-group` cannot be realized
topologically in any such model, whatever the rest of the host.

## Proof

1. **Continuous extension.** `Homeo(Y)` with the uniform topology is a topological group, and
   conjugation by `s` is a topological automorphism of it. `ι` is a continuous injection from a
   compact group, so it is a homeomorphism onto its closed image. Let `M = ⟨p_0, …, p_4⟩` and
   `M' = ⟨p_1, …, p_5⟩`, both free abelian by unique factorization. Conjugation by `s` maps
   `ι(M)` onto `ι(M')`, inducing `σ: p_k ↦ p_{k+1}`. So it maps `ι(M̄)` onto `ι(M̄')`. Hence
   `σ` extends to a continuous isomorphism `φ: M̄ → M̄'` of closed subgroups of `Z_ℓ^×`.
2. **It is a power map.** Let `U = 1 + ℓ^N Z_ℓ` with `N ≥ 2`, torsion-free, and `log: U ≅ ℓ^N Z_ℓ`.
   `M̄ ∩ U` and `M̄' ∩ U` are open in `U`, since `M̄` contains the closure of `⟨p_0⟩`, which is open.
   `φ` is continuous, so it maps some open subgroup `U_1 ≤ M̄ ∩ U` into `U`. In `log`
   coordinates, a continuous additive map `log U_1 → log U` between open subgroups of `Z_ℓ` is
   multiplication by some `λ ∈ Q_ℓ`. So `φ(x) = exp(λ log x)` on `U_1`, and `λ ≠ 0`, since `φ`
   is injective.
3. **Logarithms.** Pick `e ≥ 1` with `p_k^e ∈ U_1` for `k ≤ 5`. Then
   `p_{k+1}^e = φ(p_k^e) = exp(λ log p_k^e)`, so `log p_{k+1} = λ log p_k`, hence
   `log p_k = λ^k log p_0` for `k = 0, …, 5`, and `exp_ℓ(λ^k y) = p_k^e` with `y = e log p_0 ≠ 0`.
4. **Degenerate cases, by unique factorization.**
   - *`1, λ, λ^2` are `Q`-dependent.* Then `λ^2 = uλ + v` with `u, v ∈ Q`. So
     `c log p_2 = a log p_1 + b log p_0` for integers `a, b` and `c ≠ 0`. Hence
     `p_2^{ec} = p_1^{ea} p_0^{eb}` in `Z_ℓ` (`log` is injective on `U`), and so in `Q`. That is
     impossible for distinct primes. The case `λ ∈ Q` is the special case `u = 0`, read with
     `p_1` in place of `p_2`.
   - *`λ^3 ∈ Q`, say `λ^3 = a/c`.* Then `p_3^{ec} = p_0^{ea}`, which is impossible.
5. **Six exponentials.** Otherwise `x = (1, λ, λ^2)` and `y = (y, λ^3 y)` are `Q`-linearly
   independent, and the six numbers `exp_ℓ(λ^{i+3j} y) = p_{i+3j}^e`, for `i ≤ 2` and `j ≤ 1`,
   are all rational. This contradicts the ℓ-adic six exponentials theorem. They lie in the
   domain of `exp_ℓ`, since `λ^k y = log(p_k^e) ∈ ℓ^N Z_ℓ`. ∎

**What survives.** Shifts that also move the coordinate, with `p_k` acting on its own coordinate
`d_k`. The closure is then a product of separate procyclic groups, and step 2 gives nothing.
See item 3 of the Toward section of `one-fp-simple-group-contains-every-s-integral-linear-group`.
