---
rg: 2
id: novikov-level-descent-fails-for-d-shaped-laplacian-systems
kind: claim
title: "Level-0 descent fails for abstract D-shaped Laplacian systems, at depth 1, for both signs and with every ring obstruction vanishing; the missing input is the Artin constraint [p, (pq)^k] = 1, which forces descent when H is abelian"
distinct_from:
  artin-sigma1-is-level-zero-laplacian-surjectivity: that open claim is descent for Artin dead-cut Laplacians; this shows descent is false for the abstract systems with the same shape, so any proof of that claim must use the Artin constraint
  artin-sigma1-is-union-of-finite-depth-level-systems: that sets up the depth hierarchy and the map d^1 for Artin groups; this shows d^1 is genuinely nonzero on D-shaped systems and gives the first system that stops at depth exactly 1
  artin-sigma1-dead-edge-ring-obstruction: that is a ring certificate of non-membership; here the theta-stable ring hull is the whole ring and the Novikov ideal is everything, yet level 0 is not onto
  artin-2x2-dead-joins-sigma1-iff-k-q-odd-family: that decides a class of Artin groups, where descent holds throughout; this is an abstract system outside every Artin group, where descent fails
---

**Setting (abstract D-shaped system).**
- `G` is a group, `χ : G -> Z` is onto, `H = ker χ`, `t ∈ G` has `χ(t) = 1`, and
  `θ(h) = t h t^{-1}`.
- A *D-shaped system* is a finite family of generators `g_ρ = σ_ρ (p_ρ - 1)`, where
  `σ_ρ = S_{k_ρ}(x_ρ) = 1 + x_ρ + ... + x_ρ^{k_ρ - 1}`, `x_ρ ∈ H` has infinite order,
  `k_ρ >= 2`, and `p_ρ = h_ρ t` with `h_ρ ∈ H`.
- It is *Novikov onto at `χ`* if the left ideal `Σ_ρ N_χ g_ρ` is `N_χ`. It is *level-0 onto*
  if `J_0 = Σ_ρ Z[H] σ_ρ = Z[H]`.
- At `-χ` the generators are normalised as `t^{-1} g_ρ`, whose level-0 parts are
  `θ(σ_ρ h_ρ)`. So the level-0 ideal at `-χ` is `θ(J_0)`.
- *Formal descent* is the implication: Novikov onto `⇒` level-0 onto.
- The Artin dead-cut generators `S_k(pq)(p - 1)` (for `r = 2`, `χ(p) = 1`) are D-shaped with
  `x = pq`. They satisfy in addition the **Artin constraint**
  `p_ρ x_ρ^{k_ρ} p_ρ^{-1} = x_ρ^{k_ρ}`, because `p (qp)^k p^{-1} = (pq)^k` and
  `(qp)^k = (pq)^k`.

**Claim.**
1. *Counterexample to formal descent (the swap toy).* Take `G = Z^2 ⋊ Z = ⟨a, b, t⟩` with
   `t a t^{-1} = b`, `t b t^{-1} = a`, and `χ` the `t`-exponent. Take
   `g_1 = (1 + a)(ab·t - 1)` and `g_2 = (1 + b + b^2)(t - 1)`. Then:
   - (a) the system is Novikov onto at `χ` and at `-χ`, each time by a certificate of depth
     exactly 1. The certificate for `χ` has `ν = (c(1 + a + a^2), -c(1 + b))`, `c = -b^2`;
   - (b) it is level-0 onto at neither sign: `Z[H]/J_0 ≅ Z[ω] ≅ Z[H]/θ(J_0)` with `ω`
     a primitive cube root of unity, and `a = -1, b = 2` over `F_7` kills `J_0`;
   - (c) every obstruction that implies Novikov non-surjectivity vanishes. In particular
     the `θ`-stable two-sided hull is `J_0 + θ(J_0) = Z[H]`, since
     `1 = (1 + b + b^2) - b(1 + b)`;
   - (d) `H = Z^2` is abelian, torsion-free and residually finite, and the `σ_ρ` are
     cyclotomic polynomials (`Φ_2(a)`, `Φ_3(b)`), exactly as the `S_k(pq)` factor into
     cyclotomics;
   - (e) the Artin constraint fails: `p_1 a^2 p_1^{-1} = b^2`.
2. *Class kill.* Consider an argument deriving level-0 surjectivity from Novikov
   surjectivity using only properties (d), the D-shape, Novikov surjectivity at both signs,
   vanishing of all ring or Alexander-type obstructions, and the leading-term peeling of the
   w17 attempt. Every such argument proves formal descent for the swap toy, which is false.
   - *The step where every member dies* is the lifting of the least-level syzygy. In the toy,
     the syzygy `θ(ν) = (c'(1 + b + b^2), -c'(1 + a))`, read off level `-1`, has no lift. A
     lift would give a solution in `N_{≥0}`, hence `J_0 = Z[H]`.
   - *The invariant* is the first level differential
     `d^1 : Syz_0 -> Z[H]/θ(J_0)`, `ν -> Σ ν_ρ σ_ρ h_ρ`. In the toy `d^1(θ(ν)) ≡ 1` in
     `Z[H]/θ(J_0) ≅ Z[ω]` while `Z[H]/J_0 ≠ 0`. By part 4 of
     `artin-sigma1-is-union-of-finite-depth-level-systems`, this is exactly depth 1 without
     depth 0.
3. *Gate: the Artin constraint closes the abelian case.* Let a D-shaped system satisfy the
   Artin constraint, with `H` abelian and torsion-free. Then formal descent holds, at `χ` and
   at `-χ`. More generally, formal descent holds whenever `J_0` is `θ`-stable and two-sided.

**What it shows for Problem 1.6.**
- The open claim `artin-sigma1-is-level-zero-laplacian-surjectivity` cannot follow from the
  shape of the Laplacian, cyclotomicity, sign symmetry or ring-theoretic vanishing alone.
  The swap toy has all of these and still needs negative-level cancellation.
- A proof must use `[p_ρ, (p_ρ q_ρ)^{k_ρ}] = 1`, and must use it for non-abelian `H`, where
  conjugation by different `p_ρ` differs by inner automorphisms of `H`. This is exactly where
  the abelian gate stops.
- A counterexample must look like the toy on the level-0 cokernel. It needs a mixed D–D
  syzygy whose `d^1` is a unit modulo `θ(J_0)` while `J_0 ≠ Z[H]`, and it must be compatible
  with the Artin constraint. The toy shows that such a `d^1` is not forbidden by anything
  except that constraint.

Proof: `novikov-level-descent-fails-for-d-shaped-laplacian-systems-proof`.
