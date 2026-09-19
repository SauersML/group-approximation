---
rg: 2
id: thompson-t-kahler-euler-class-is-a-hermitian-domination-problem
kind: claim
title: "(K) is exactly a Hermitian-form domination problem on Thompson's T: e_R is a Kahler area class iff, for some cnd function psi and some odd function f on T, the explicit bounded skew kernel Omega(g,k) = int u_{g^-1} du_{k^-1} of the displacement cocycle, corrected by the coboundary kernel of f, is dominated as a Hermitian form by the Gram kernel of psi; every finite section is feasible, so no finitary certificate refutes (K)"
distinct_from:
  lifted-thompson-t-euler-class-in-kahler-subspace: that is (K) itself, quantified over all unitary representations; this proves (K) is equivalent to one positivity condition on explicit kernels over T x T, with only a cnd function and an odd function as unknowns
  lifted-thompson-t-root-twist-cost-iff-euler-cup-product: that shows (K) is equivalent to the square-root twist rate of T-bar; this rewrites (K) with no representation and no T-bar, as a semidefinite feasibility problem on T
  cup-products-of-integrably-paired-potential-cocycles-are-exact: that kills the witnesses whose two cocycles have an integrably paired potential; this is a universal form for all witnesses, and it kills refutations by finite sections
artifacts: []
---

**ESTABLISHED** by `thompson-t-kahler-euler-class-hermitian-domination-proof`. The proof is
self-contained. Its one input from the graph is Step 3 of `integrably-paired-cup-products-exact-proof`:
the displacement cocycle has area class `e_R`.

## Notation

- `T̄` acts on `R` by lifts of Thompson's `T`. For `g ∈ T` and any lift `g̃`, `u_g = g̃ − id` is a
  1-periodic PL function, well defined modulo constants.
- `W` is the space of 1-periodic PL functions modulo constants. It carries the skew form
  `ω(φ, ψ) = ∫_0^1 φ dψ`.
- `T` acts on `W` on the left by `g·φ = φ ∘ g̃^{-1}`, which preserves `ω`. Then `v_g := u_{g^{-1}}`
  is a left 1-cocycle: `v_{gh} = g·v_h + v_g`.
- The displacement kernel is `Ω(g, k) := ω(v_g, v_k) = ∫_0^1 u_{g^{-1}} du_{k^{-1}}`. It is real
  and skew, and `|Ω| < 2`.
- For a function `ψ` on `T`, the Gram kernel is `G_ψ(g, k) := ½(ψ(g) + ψ(k) − ψ(g^{-1}k))`.
- For a function `f` on `T`, the coboundary kernel is `∂f(g, k) := f(g) + f(g^{-1}k) − f(k)`.
- `c_c(T)` is the space of finitely supported functions `T → C`. For a kernel `K`,
  `⟨c, K c⟩ := Σ_{g,k} c̄(g) K(g,k) c(k)`.

## Statement

**(A) Equivalence.** The following are equivalent.

1. (K) holds, i.e. `lifted-thompson-t-euler-class-in-kahler-subspace`: some unitary
   representation `π` and some `b ∈ Z¹(T, π)` satisfy `[Im⟨b(g), π(g)b(h)⟩] = e_R`.
2. There are a cnd function `ψ` on `T` with `ψ(1) = 0`, and a function `f : T → R` with
   `f(1) = 0` and `f(g^{-1}) = −f(g)`, such that the Hermitian kernel
   `H_{ψ,f}(g, k) := G_ψ(g, k) + i(Ω(g, k) + ∂f(g, k))` is positive semidefinite on `T × T`.
3. The same `ψ` and `f` exist, with *form domination*:
   `|⟨c, (Ω + ∂f) c⟩| ≤ ⟨c, G_ψ c⟩` for every `c ∈ c_c(T)`.

When these hold, the witness can be taken universal. `π` is the GNS completion of `c_c(T)` under
`H_{ψ,f}`, with the affine action `δ_g ↦ δ_{ag} − δ_a`, and `b(g) = [δ_g]`. Then
`Im⟨b(g), π(g)b(h)⟩ = −D(g,h) + f(g) + f(h) − f(gh)` exactly, where `D` is the bounded Euler
cocycle of Step 3 and `e_R = [D]`. Conversely, every witness `(π, b)` of (K), rescaled and
conjugated so that its class is `−e_R`, gives such a pair: `ψ = ‖b‖²`, and `f` is the unique
function with `Im⟨b(g), π(g)b(h)⟩ + D(g,h) = δf(g,h)`.

**(B) No finitary refutation.** For every finite `E ⊂ T` there is a pair `(ψ, f)` whose kernel
`H_{ψ,f}` is positive semidefinite on `E × E`: take `f = 0` and `ψ = 2C·1_{T∖{1}}`, where `C ≥ 2|E|`.

So no computation on a finite set of group elements can refute (K), and neither can any
argument that uses only finitely many relations at a time. A refutation must use the behaviour
at infinity of `Ω + ∂f` against *unbounded* cnd functions.

**(C) The displacement form is unbounded modulo every correction.** For every odd `f` with
`f(1) = 0`, the Hermitian form `c ↦ ⟨c, i(Ω + ∂f)c⟩` is unbounded on the unit ball of `ℓ²(T)`.

Equivalently, no pair in (A2) has `ψ` bounded. If some pair did, it would give a bounded cocycle
and so `e_R = 0`, which is false.

## What this changes

- **For a prover of (K).** The unknown is no longer a representation. It is a cnd function `ψ`
  on `T` and an odd function `f`, subject to one explicit inequality (A3). The kernel `Ω` is
  explicit, bounded and computable exactly on dyadic PL maps.
  - `f` is the only freedom beyond `ψ`. It is the choice of representative of the class.
  - By `cup-products-of-integrably-paired-potential-cocycles-are-exact`, `ψ` cannot be a
    wall/cubical function, whatever `f` is.
- **For a breaker of (K).** By (B), the census-computation family is dead on (K) as it stands:
  finite-section semidefinite programs and finite relator checks are always feasible.
  - A refutation must show that for every unbounded cnd `ψ` and every odd `f`, the violating
    vectors `c` escape to infinity.
  - By (C), `Ω` alone is already not `ℓ²`-bounded. That unboundedness is the only resource a
    refutation can exploit, and it is exactly what an unbounded `ψ` must absorb.
- **Relation to the twist cost.** Through
  `lifted-thompson-t-root-twist-cost-iff-euler-cup-product`, the failure of (A3) for every
  `(ψ, f)` is equivalent to `c(θ)/√‖θ‖ → ∞` for the twist cost of `T̄`.

## Not claimed

- No choice of `ψ` is shown to work or to fail beyond (B) and (C).
- (C) uses `e_R ≠ 0`. That fact is recalled from Ghys–Sergiescu, following the convention of
  `cup-products-of-integrably-paired-potential-cocycles-are-exact`, and is not re-verified here.
  (A) and (B) do not use it.
- The analogous statement holds verbatim for any group `Γ`, any `Γ`-module with an invariant skew
  form and any cocycle, as the proof shows. Only its application to `T` uses Step 3.
