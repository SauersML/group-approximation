---
rg: 2
id: sl3z-z-extension-centres-bounded-proof
kind: route
title: Central eigenspaces realize rescaled extension classes, finiteness of the realizable multiplier bounds their orders, and a spectral gap at 1 gives full fixed mass
target: sl3z-finite-index-z-extension-centres-stay-bounded
requires:
  - sl3z-finite-index-fd-projective-multiplier-is-finite
  - sl3z-schur-multiplier-is-klein-four
  - z-extension-centre-orders-are-restricted-evaluation-indices
  - kazhdan-cover-models-round-iff-kernel-fixed-mass-one
  - bdhv-central-extension-property-t
  - ershov-jaikin-kassabov-steinberg-groups-have-property-t
---

**Conventions.**
- All cohomology is of discrete groups with trivial coefficients.
- `s : K -> K~` is a section with `s(e) = e`, and `c(g, h) ∈ Z` is defined by
  `s(g)s(h) = z^(c(g,h)) s(gh)`. This `c` is a 2-cocycle representing the class of the extension.
  Only orders of classes matter below, so the sign convention is irrelevant.
- `exp : R -> T` is `t ↦ e^(2πit)`. `0 -> Z -> R -> T -> 0` gives the exact sequence
  `H^1(K; T) --β--> H^2(K; Z) --> H^2(K; R) --exp_*--> H^2(K; T)`.
- `||A||_(2,d)^2 = tr_d(A*A)`, where `tr_d` is the normalized trace.

## Item 1: the class is archimedean

- **`c` has infinite order.** Suppose `rc = δF` for some `r >= 1` and `F : K -> Z`, meaning
  `r c(g, h) = F(g) + F(h) - F(gh)`. Define `φ(z^a s(g)) := ra + F(g)`.
  - Every element of `K~` is uniquely `z^a s(g)`, and
    `z^a s(g) · z^b s(h) = z^(a + b + c(g,h)) s(gh)`.
  - So `φ` is a homomorphism: `r(a + b + c(g,h)) + F(gh) = ra + F(g) + rb + F(h)`.
  - `φ(z) = r != 0`, so `φ(K~)` is a nonzero subgroup of `Z` and `K~^ab` is infinite. This is a
    contradiction.
- **`c_R != 0`.** The kernel of `H^2(K; Z) -> H^2(K; R)` is `β(H^1(K; T))`. Here
  `H^1(K; T) = Hom(K^ab, T)`, and `K^ab` is finite because `K` has (T)
  (`ershov-jaikin-kassabov-steinberg-groups-have-property-t`, passed to finite index). So the
  kernel is finite, hence torsion, and it cannot contain `c`.
- **`b_2(K) > 0`.** By the universal coefficient theorem `H^2(K; R) = Hom(H_2(K; Z), R)`, since
  `Ext(-, R) = 0`. This group is nonzero exactly when `H_2(K; Z) ⊗ Q != 0`.
- **Level one.** `H_2(SL_3(Z); Z)` is finite by `sl3z-schur-multiplier-is-klein-four`, so
  `H^2(SL_3(Z); R) = 0`.

## Item 2: divisibility

- `c_R != 0`, so by UCT some `x ∈ H_2(K; Z)` has `a := <c, x> != 0`, where `a ∈ Z`.
- If `t c_R` is the image of `c' ∈ H^2(K; Z)`, then evaluating on `x` gives
  `ta = <c', x> ∈ Z`, so `t ∈ (1/|a|)Z`.
- Hence `T_c := {t : t c_R ∈ Λ}` is a subgroup of `R` with `Z <= T_c <= (1/|a|)Z`. So
  `T_c = (1/m)Z` for a unique integer `m >= 1`, and `m` divides `a`.
- **Orders.** For `θ ∈ R`, the class `exp_*(θ c_R)` has finite order exactly when `θ ∈ Q`. If
  `θ = b/n` in lowest terms, its order is `n / gcd(n, m)`.
  - Indeed `j·exp_*(θ c_R) = exp_*(jθ c_R)`, which vanishes iff `jθ c_R ∈ Λ` (exactness), iff
    `jθ ∈ (1/m)Z`.
  - For `θ = b/n` this reads `n | jbm`, that is `n | jm`, that is `n/gcd(n, m) | j`.
  - For irrational `θ` no `j >= 1` works.

## Item 3: bounded eigenvalues

- Let `ρ : K~ -> U(d)` and let `ζ = exp(θ)` be an eigenvalue of `ρ(z)`, with eigenspace
  `H_ζ != 0`. `z` is central, so `H_ζ` is `K~`-invariant.
- `π(g) := ρ(s(g))|_(H_ζ)` satisfies `π(g)π(h) = ρ(z)^(c(g,h)) π(gh) = ζ^(c(g,h)) π(gh)`.
  So `π` is a finite-dimensional projective unitary representation of `K` with exact cocycle
  `ζ^c`.
- The class of `ζ^c` is the image of `c` under `Z -> T, 1 ↦ ζ`. That map factors as
  `Z --(·θ)--> R --exp--> T`, so the class is `exp_*(θ c_R)`, and it lies in `R(K)`.
- `R(K)` is a finite group (`sl3z-finite-index-fd-projective-multiplier-is-finite`, (SF1): it
  is the image of a homomorphism from a finite group). So `exp_*(θ c_R)` has finite order at
  most `|R(K)|`.
- By Item 2, `θ = b/n ∈ Q` in lowest terms and `n/gcd(n, m) <= |R(K)|`. So `ζ` has order
  `n <= gcd(n, m)·|R(K)| <= m·|R(K)| = C`.

## Item 4: bounded centre orders

- Let `q : K~ -> Q` be onto a finite group, with `q(z)` of order `n`.
- Let `ρ` be the left regular representation of `Q` composed with `q`.
- `<q(z)>` is cyclic of order `n`. Restricted to it, `l^2(Q)` is a multiple of the regular
  representation of `<q(z)>`, which contains every character. So `e^(2πi/n)` is an eigenvalue of
  `ρ(z)`.
- By Item 3, `n <= C`.
- Item 2 of `z-extension-centre-orders-are-restricted-evaluation-indices` (global identity) applies
  because `<c, x> != 0` (Item 2 above). It identifies the supremum of these orders with
  `sup_N e(N)`, so `sup_N e(N) <= C`.

## Item 5: pulled-back models round

- **Property (T).** `K` has (T), `<z>` is central and `K~^ab` is finite. So `K~` has (T) by
  `bdhv-central-extension-property-t`. `K~` is finitely generated, as an extension of a finitely
  generated group by `Z`.
- **Spectral gap at 1.** Let `ρ_k` be as in the claim, with eigenvalues `ζ_1, ..., ζ_d` of
  `ρ_k(z)` counted with multiplicity.
  - Every `ζ_i != 1` has order `n_i` with `2 <= n_i <= C` (Item 3). So
    `|ζ_i - 1| = 2|sin(π b_i/n_i)| >= 2 sin(π/n_i) >= 2 sin(π/C)`, for `b_i` prime to `n_i`
    with `0 < b_i < n_i`.
  - Hence
    `||ρ_k(z) - 1||_(2,d)^2 = (1/d) Σ_i |ζ_i - 1|^2 >= (1 - tr_d E_k)·4 sin^2(π/C)`.
  - If `C = 1`, every eigenvalue is `1` and `E_k = 1`.
- **(KC1).** For `u = z^j ∈ <z>`, telescoping and unitary invariance give
  `||ρ_k(z^j) - 1||_(2,d) <= |j|·||ρ_k(z) - 1||_(2,d) -> 0`. Also
  `Fix_(<z>)(ρ_k) = Fix ρ_k(z)`.
- **Conclusion.** `tr E_k -> 1`. By `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`,
  with `Γ~ = K~`, `N = <z>` and `Γ = K`, implication (c) ⇒ (b) makes `ρ_k ∘ s` round strictly.

**Model tests.**
- *The finiteness input is needed.* On `Z^(2g) ⋊ Sp_(2g)(Z)`, Item 3 run backwards on the
  Heisenberg cover of `rf-kazhdan-group-not-flexibly-hs-stable` produces realizable classes
  `exp_*(c_R/k)` of unbounded order. That is consistent, since there `R` is infinite.
- *Vacuity at level one.* By Item 1 there is no such extension of `SL_3(Z)` itself. The
  hypothesis becomes non-vacuous only at a finite-index `K` with `b_2(K) > 0`, which is not
  verified here.
