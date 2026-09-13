---
rg: 2
id: zp-o2-generator-kk-class-is-twisted-asymptotic-innerness
kind: claim
title: For outer Z/p-actions on O_2 the generator's KK^G-class is a character iff the generator is asymptotically inner through approximate eigen-unitaries of that character; a phantom is twisted but not untwisted innerness
distinct_from:
  zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner: that is the case of the trivial character, invariant unitary paths; this treats every character and shows that contractible crossed product means exactly that only nontrivial characters occur.
  zp-restriction-trivial-splits-cellular-plus-phantom: that splits off the trivial-action part by the norm idempotent of the action element; this splits the phantom part further by the Galois components where the action element equals a character, and gives each component its dynamics.
---

**ESTABLISHED (derivation from Gabe--Szabó Theorem 5.8 and the cyclotomic and
splitting nodes; standard inputs flagged in the proof).**  Let `p` be prime,
`G = Z/p` with generator `ω`, `α : G ↷ O_2` pointwise outer, `E = (O_2, α)`,
`θ = [α_ω] ∈ KK^G(E, E)`, and `ψ·1_E` the exterior product with the class of a
character `ψ ∈ Ĝ` in `R(G)`.

1. **Twisted innerness.**  For `ψ ∈ Ĝ`, `θ = ψ·1_E` iff there is a
   norm-continuous unitary path `u_t ∈ O_2` with
   `α_ω(a) = lim_(t→∞) u_t a u_t^*` for all `a`, and
   `lim_(t→∞) ‖α_g(u_t) − ψ(g) u_t‖ = 0` for all `g`.
   Call this **`ψ`-twisted asymptotic innerness**.
2. **Twisted innerness kills the crossed product.**  If `α_ω` is `ψ`-twisted
   asymptotically inner for some `ψ ≠ 1`, then `O_2 ⋊_α G ≅ O_2`.
3. **Two characters give the Rokhlin property.**  The following are
   equivalent:
   - `α` has the Rokhlin property;
   - `α_ω` is `ψ`-twisted asymptotically inner for every `ψ ∈ Ĝ`;
   - it is `ψ`-twisted and `ψ'`-twisted asymptotically inner for two
     distinct characters.
4. **Galois components.**  `O_2 ⋊_α G ≃_KK 0` iff `Φ_p(θ) = 0`.  In that case:
   - `KK^G(E, E)` is an algebra over
     `Z[1/p][x, y]/(Φ_p(x), Φ_p(y)) ≅ ∏_(k ∈ F_p^×) Z[ζ_p, 1/p]`, with `x ↦ χ`
     and `y ↦ θ`;
   - `E ≅ ⊕_(k ∈ F_p^×) E_k` with `θ = χ^k` on `E_k`;
   - each `E_k ≠ 0` is KK^G-equivalent to a pointwise outer action `α^(k)` on
     unital `O_2`, with crossed product `O_2`, whose generator is
     `χ^k`-twisted asymptotically inner and not `1`-twisted.
5. **Detection as untwisting.**
   `zp-restriction-and-crossed-product-detect-kk-g-contractibility` holds at
   `p` iff, for every pointwise outer `α : Z/p ↷ O_2` and every
   `k ∈ F_p^×`, `χ^k`-twisted asymptotic innerness of `α_ω` implies invariant
   asymptotic innerness.
6. **The case `p = 2`.**  Let `σ = α_ω`.  Call a unitary path *odd* if
   `‖σ(u_t) + u_t‖ → 0` and *even* if `‖σ(u_t) − u_t‖ → 0`.
   - `O_2 ⋊_α Z/2 ≅ O_2` iff `σ` is asymptotically inner along an odd path.
   - `α` is Rokhlin iff `σ` is asymptotically inner along an odd path and also
     along an even path.
   - Detection at `2` iff odd asymptotic innerness implies even asymptotic
     innerness.
7. **The implementing cocycle.**  Take `v ∈ U(A_∞)`, `A = O_2`, with
   `Ad(v)|_A = α_ω`.  Then `w_g = v^* α_g(v)` is an `α_∞`-cocycle in
   `F_∞(A) = A_∞ ∩ A'`, and its class
   `c(α) ∈ H^1(G, U(F_∞(A)))` does not depend on `v`.
   - If `θ = χ^k`, then `c(α)` is the class of the scalar cocycle `χ^k`.
   - So on each Galois component, the cocycle whose vanishing the detection
     step asks for is a character.  By
     `zp-o2-contractible-crossed-product-only-coboundaries`, item 5,
     that character is a coboundary in `F_∞(A)` iff `α` is Rokhlin.

**What this says about a phantom.**  A counterexample to detection is an
outer action on `O_2` whose generator is asymptotically inner through
approximate eigen-unitaries of a nontrivial eigenvalue, and never through
approximately invariant ones.  At `p = 2`: odd but not even.  Every outer
action with contractible crossed product is odd, so detection is the single
implication "odd ⟹ even".

**Model tests.**
* Rokhlin model `id ⊗ μ_G` on `O_2 ⊗ M_(p^∞)`: `E ≃ 0`, so item 3 predicts
  paths of every eigenvalue.  Explicitly, `W_n = ⊗_(j≤n) λ_ω` implements
  `α_ω` on the first `n` factors and is invariant.  Multiplying by a far-out
  factor unitary of eigenvalue `ψ(ω)` changes the eigenvalue, not the limit.
* Trivial character: item 1 with `ψ = 1` is item 1 of
  `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner`.
* Outerness is needed in items 1 and 3.  The trivial action on `O_2` is
  KK^G-contractible, so `θ = ψ·1_E` for every `ψ`.  But no path is
  `ψ`-twisted for `ψ ≠ 1`, since `α(u_t) = u_t`, and the action is not
  Rokhlin.

No priority is claimed.  Items 1 and 6 are direct applications of Gabe--Szabó
Theorem 5.8.  The Galois splitting refines item 6 of the splitting node from
`D ⊗ D` to `D`.

Proof: `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness-proof`.
