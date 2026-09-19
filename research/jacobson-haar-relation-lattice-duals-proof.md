---
rg: 2
id: jacobson-haar-relation-lattice-duals-proof
kind: route
title: Embed the affine group as an S-arithmetic lattice, dualize against lattices of the point stabilizer, and read the dual as a skew product over the Haar relation
target: jacobson-haar-lattice-duals-are-class-bijective-extensions
requires:
  - jacobson-haar-relation-is-laurent-affine-restriction
  - jacobson-haar-relation-is-kazhdan-and-unsplittable
  - cordeiro-sofic-relation-permanence
  - paunescu-class-is-measure-equivalence-invariant
---

## Step 0. Imports

* **(I1)** From `jacobson-haar-relation-is-laurent-affine-restriction`:
  * `Γ ↷ (K_∞^n, m)` is essentially free and preserves `m`;
  * `R_Γ|_D` sofic implies `EL_n(J)` sofic;
  * `L(R_Γ|_D)` CE implies `EL_n(J)` hyperlinear.
* **(I2)** Every `Γ`-orbit in `K_∞^n` meets `D`. The reason is `K_∞ = D ⊕ F_2[x]` and `F_2[x]^n ⊆ A^n`.
* **(I3)** Harder's reduction theory over global function fields (literature import; Harder, Invent. Math. 7 (1969)).
  For a nonempty finite set `S` of places of `F_2(x)` with ring of `S`-integers `O_S`, `SL_n(O_S)` is a lattice in
  `Π_(v in S) SL_n(K_v)`. We use three cases:
  * `S = {∞, 0}`, `O_S = A`;
  * `S = {∞}`, `O_S = F_2[x]`;
  * `S = {0}`, `O_S = F_2[x^(-1)]`.
* **(I4)** From `cordeiro-sofic-relation-permanence`: Theorem 2.2 and Proposition 3.2(a) (restriction).
* **(I5)** From the artifact of `paunescu-class-is-measure-equivalence-invariant`:
  * Lemma 2.2 (amplification). If `V` meets almost every class of `R` on a finite measure space and `R|_V` is sofic,
    then `R` is sofic.
  * The corner/amplification form for CE. If `p` has central support `1` in a finite von Neumann algebra `M` and
    `pMp` is CE, then `M` is CE.
* **(I6)** From `jacobson-haar-relation-is-kazhdan-and-unsplittable`: `R_Γ|_D` is ergodic.

## Step 1. The envelope (D1)

1. **`A` is a cocompact lattice in `K_∞ x K_0`.**
   * *Discreteness.* `A ∩ (D_1 x O_0) = 0`, where `D_1 = x^(-1)O_∞`. A Laurent polynomial with only negative powers
     and only nonnegative powers is `0`.
   * *Covering.* Take `(u,v)`. Let `a ∈ A` be the polar part of `v`, so that `v - a ∈ O_0`. Let `b ∈ F_2[x]` be
     the part of `u - a` of degree `>= 0`. Then `u - a - b ∈ D_1`, and `v - a - b ∈ O_0` because `b ∈ O_0`.
   * So `D_1 x O_0` is a fundamental domain of measure `1`.
2. **`SL_n(A)` is a lattice in `SL_n(K_∞) x SL_n(K_0)`** by (I3). Hence `Γ = A^n x| SL_n(A)` is a lattice in
   `G = G_∞ x G_0`.
   * A fundamental domain is `(D_1 x O_0)^n x F`, where `F` is one for `SL_n(A)`.
   * `G` is unimodular, since `SL_n` preserves Haar measure on `K_v^n` (determinant `1`).
3. **The quotient `G/H`.** `G` acts on `K_∞^n` through `G_∞`, transitively, with stabilizer of `0` equal to `H`.
   * On `Γ` this action is `(w,a).y = a y + w`, which is the affine action of (I1).
   * The invariant measure on `G/H` is a multiple of `m`.
4. **Freeness.** `Stab_H(Γg) = H ∩ g^(-1)Γg = g^(-1) Stab_Γ(gH) g`.
   * The set of `g` with `Stab_Γ(gH) = 1` is conull by (I1).
   * That set is left `Γ`-invariant and right `H`-invariant.
   * So `H ↷ Γ\G` is essentially free.
5. **Ergodicity.**
   * `Γ ↷ K_∞^n` is ergodic, by (I2) and (I6).
   * By Moore duality, an `H`-invariant set in `Γ\G` pulls back to a set in `G` that is left `Γ`-invariant and right
     `H`-invariant. Such a set is the pullback of a `Γ`-invariant set in `G/H`.
6. **Lattices of `H`.**
   * `SL_n(F_2[x])` is a lattice in `SL_n(K_∞)`, by (I3).
   * `F_2[x^(-1)]` is a cocompact lattice in `K_0`, with fundamental domain `x O_0`.
   * `SL_n(F_2[x^(-1)])` is a lattice in `SL_n(K_0)`, by (I3).
   * So `Δ_std` is a lattice in `H`.

## Step 2. The dual relation is a skew product over R_Γ|_D (D3, first part)

Fix a lattice `Δ` of `H`.

1. **The coupling.** Let `Γ x Δ` act on `(G, Haar)` by `(γ,δ).g = γ g δ^(-1)`. This preserves measure because `G`
   is unimodular. Let `R` be its orbit relation.
2. **Two fundamental domains.** Let `Φ_Γ` be a Borel fundamental domain for left `Γ` (finite measure), and `Φ_Δ` one
   for right `Δ`.
   * For `g, g' ∈ Φ_Γ`, `(g,g') ∈ R` iff `Γg' = Γgδ^(-1)` for some `δ`. So `R|_(Φ_Γ) ≅ R_Δ` on `(Γ\G, Haar)`.
   * In the same way, `R|_(Φ_Δ)` is the orbit relation of `Γ` on `G/Δ`.
3. **Skew-product coordinates.** Pick a Borel section `σ: K_∞^n -> G` of `G -> G/H`. Define
   `c(γ,y) = σ(γy)^(-1) γ σ(y) ∈ H`, a cocycle.
   * `(y, hΔ) -> σ(y) h Δ` is a Borel isomorphism `K_∞^n x H/Δ -> G/Δ`.
   * It carries `m ⊗ vol` to Haar measure, by the Weil formula.
   * It carries `γ.(y,ξ) = (γy, c(γ,y)ξ)` to the left action of `Γ`.
4. **Normalization.** Put `S_Δ = R_Γ restricted to D x H/Δ`, with the normalized measure `m|_D ⊗ vol/vol(H/Δ)`.
   Let `B ⊆ Φ_Δ` be the set corresponding to `D x H/Δ`.
5. **Both sets meet every class.**
   * Every `R`-class `ΓgΔ` meets `Φ_Γ`.
   * Every `R`-class also meets `B`: the orbit `Γ.gH` meets `D` by (I2), so some `γgΔ` lies over `D`.
6. **Class-bijectivity.** For `p(y,ξ) = y`, the `S_Δ`-class of `(y,ξ)` is
   `{(γy, c(γ,y)ξ) : γy ∈ D}`.
   * `p` maps this class onto the `R_Γ|_D`-class of `y`.
   * `p` is injective on the class, because `γy = γ'y` forces `γ = γ'` off the null set of (I1). That null set is
     `Γ`-invariant.
   * `p` pushes the measure forward to `m|_D`.
   * So `p: S_Δ -> R_Γ|_D` is a class-bijective factor map, and `R|_(Φ_Γ)`, `R|_B ≅ S_Δ` are two complete
     restrictions of one relation `R`.
7. **The fibre is never trivial.** `H/Δ` is non-atomic, since `H ⊇ SL_n(K_∞)` is non-discrete. So `S_Δ` is a proper
   extension of `R_Γ|_D` for every choice of `Δ`.

## Step 3. Class-bijective factors inherit approximations

**Lemma.** Let `p: (Z, ν, S) -> (X, μ, R_0)` be a measure-preserving, class-bijective factor map of p.m.p. relations.
1. If `S` is sofic, then `R_0` is sofic.
2. If `L(S)` is CE, then `L(R_0)` is CE.

*Proof.*
1. **The lift.** For `φ ∈ [[R_0]]` with domain `U`, define `φ~` on `p^(-1)U` by letting `φ~(z)` be the unique `z'` in
   the `S`-class of `z` with `p z' = φ(p z)`. This is well defined by class-bijectivity.
2. **Properties of the lift.**
   * `φ~` is a measure-preserving partial bijection.
   * `(φψ)~ = φ~ψ~` and `(φ^(-1))~ = (φ~)^(-1)`.
   * `φ~(z) = z` iff `φ(pz) = pz`, because `z` is the only lift of `pz` in its class. So
     `tr φ~ = ν(p^(-1) Fix φ) = tr φ`.
3. **Consequences.**
   * `[[R_0]] -> [[S]]` is a trace-preserving embedding. It is isometric for the trace metric of Cordeiro
     Theorem 2.2 (I4).
   * Composing with an isometric embedding of `[[S]]` in `Π_𝒰 [[n_k]]` gives one for `[[R_0]]`. That is (1).
   * Linearly, `f ⊗ φ -> (f∘p) φ~` extends to a trace-preserving normal `*`-embedding `L(R_0) -> L(S)`. CE passes to
     von Neumann subalgebras. That is (2). ∎

## Step 4. Transfer (D2)

Assume `Δ ↷ Γ\G` is sofic. Then:
1. `R_Δ` is sofic, by Păunescu Proposition 1.15, as used in (I5) for essentially free actions (Step 1.4).
2. `R|_(Φ_Γ)` is sofic, by Step 2.2.
3. `R|_(Φ_Γ ∪ B)` is sofic, by (I5) amplification, since `Φ_Γ` meets every class (Step 2.5).
4. `R|_B ≅ S_Δ` is sofic, by (I4) restriction.
5. `R_Γ|_D` is sofic, by Step 3.
6. `EL_n(J)` is sofic, by (I1).

For CE the same chain runs through von Neumann algebras:
* `L^∞(Γ\G) x| Δ = L(R_Δ)`, since the action is free.
* `L(R|_(Φ_Γ))` and `L(R|_B)` are corners of `L(R|_(Φ_Γ ∪ B))` whose projections have central support `1`.
* Step 3 then gives CE of `L(R_Γ|_D)`, and (I1) gives that `EL_n(J)` is hyperlinear. ∎

## Step 5. The fibre-free alternative is tautological (D3, second part)

1. **The solenoid.** Let `Y = (K_∞ x K_0)^n / A^n`. It is compact by Step 1.1, with fundamental domain
   `(D_1 x O_0)^n = D x O_0^n`.
2. **The group `H'`.** Let `H' = K_0^n x| SL_n(A)`, with `SL_n(A)` discrete, act on `Y` by
   `(t,a).[(u,v)] = [(a u, a v + t)]`. This is well defined because `aA^n = A^n`.
3. **The transversal.** `θ(d) = [(d,0)]`, for `d ∈ D`, meets every orbit of `U = O_0^n` exactly once.
   * `[(d,w)] = [(d',0)]` means there is `b ∈ A^n` with `d' = d + b` and `w = b`.
   * So `b ∈ A^n ∩ O_0^n = F_2[x]^n` and `b ∈ D - D`, which forces `b = 0`.
4. **The cross-section relation.** For `d, d' ∈ D`, `θ(d') ∈ H'.θ(d)` iff there are `a`, `t` and `b ∈ A^n` with
   `d' = a d + b` and `t = b`. That holds iff `d' ∈ Γ.d`. The acting elements `(b,a)` form a countable set.
   * So the cross-section relation of `H' ↷ Y` on `θ(D)` is `R_Γ|_D` itself.
   * `H'` does not enlarge the problem, and it offers no discrete dual group.
5. **No finite orbits.** `Γ` sits in `H'` as `(w,a) -> (w,a)`, with `w ∈ A^n ⊆ K_0^n`. Its translations
   `[(0,w)] = [(w,0)]` form a subgroup of `Y` isomorphic to `A^n`, because `(w,0) ∈ A^n` forces `w = 0`. So every
   `Γ`-orbit on `Y` is infinite.
   * The periodic-point scheme of the half `Γ_+` (finite invariant subgroups of `K^n / x^(-k)F_2[x]^n`) and the ball
     scheme of `Γ_-` have no common finite model on `Y`.
   * This is the solenoid form of item (F) of `leavitt-corner-toeplitz-support-class-is-jacobson-hyperlinearity`.

## Step 6. Why the class dies (D3, conclusion)

**Invariant.** For each lattice `Δ ≤ H`, the class-bijective factor map `p: S_Δ -> R_Γ|_D` of Step 2.6.

**Death step.** "Construct approximations of `Δ ↷ Γ\G`." By Step 3, any sofic approximation or CE embedding of `S_Δ`
restricts along `[[R_Γ|_D]] -> [[S_Δ]]` to one of `R_Γ|_D`. So the dual problem implies the original problem, and it
cannot be weaker.

**What is left.** A duality proof has to use structure of `S_Δ` that is invisible on `R_Γ|_D`. The candidates are:
* the finite-volume fibre `H/Δ`;
* the product splitting `Δ = Δ_∞ x Δ_0`.

This is question `(D4)` of the claim. Both factors of `Δ_std` are Kazhdan for `n >= 3`:
* `SL_n(F_2[y])` has (T) for `n >= 3`;
* `F_2[y]^n x| SL_n(F_2[y])` has (T) as well, by relative (T) of the pair.

So any `(D4)` scheme has to avoid the gluing obstruction of `jacobson-haar-relation-is-kazhdan-and-unsplittable`,
now for the ergodic Kazhdan action `Δ ↷ Γ\G`. ∎
