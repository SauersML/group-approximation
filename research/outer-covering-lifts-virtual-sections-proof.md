---
rg: 2
id: outer-covering-lifts-virtual-sections-proof
kind: route
title: Unique roots make extensions from a finite-index subgroup unique, and fixed marked points descend to a based class
target: outer-covering-lifts-are-virtual-sections
requires: []
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**Unique roots.** Let `N` be torsion-free, with the centralizer of every
nontrivial element cyclic. This holds for free groups and for closed hyperbolic
surface groups (standard).
- If `x^k = y^k = 1`, then `x = y = 1`.
- Otherwise `x` and `y` both lie in the cyclic group `C(x^k) = <z>`. Writing
  `x = z^a` and `y = z^b` gives `z^(ak) = z^(bk)`, so `a = b`.

**(i).**
- **Uniqueness.** Let `φ, ψ ∈ Aut(N)` agree on `H`, and put `θ = ψ^-1 φ`.
  - For `γ ∈ N`, the cosets `γ^i H` with `0 ≤ i ≤ [N:H]` cannot all be
    distinct, so `γ^k ∈ H` for some `k ≥ 1`.
  - Then `θ(γ)^k = θ(γ^k) = γ^k`, and unique roots give `θ(γ) = γ`.
- **Homomorphism.** `σ(f)σ(h)` preserves `H`, restricts on `H` to
  `λ(f)λ(h) = λ(fh)`, and represents `fh`. By uniqueness it equals `σ(fh)`.
- **Converse.** Take `H = N` and `λ = σ`.

**(ii).**
1. `λ(f)` permutes `P`, and all representatives induce the same permutation,
   since isotopies rel `P` fix `P` pointwise. Let `L′` be the kernel of this
   action; it has finite index in `L`.
2. Fix `p̃ ∈ P` and put `x = π(p̃)`. The covering map gives an injection
   `π_*: π1(Σ̃, p̃) → π1(Σ, x)` onto a subgroup `H` of finite index.
3. Let `f ∈ L′`. Every representative `F` of `λ(f)` fixes `P` pointwise, and
   `F_* ∈ Aut(π1(Σ̃, p̃))` depends only on the class of `F` rel `P`. So
   `λ̄(f) := π_* F_* π_*^-1` defines a homomorphism `L′ → Aut(H)`.
4. Choose `F` covering a representative `f′` of `f`, as the hypothesis allows.
   - `f′(x) = π(F(p̃)) = π(p̃) = x`.
   - `f′_* ∈ Aut(π1(Σ, x))` satisfies `f′_* π_* = π_* F_*`, so `f′_*(H) = H`
     and `f′_*|_H = λ̄(f)`.
   - `f′_*` represents `f` in `Out(π1 Σ)`.
5. `F` is orientation-preserving and `π` is a local homeomorphism, so `f′` is
   orientation-preserving. Put `σ(f) := [f′] ∈ Mod(Σ, x)`.
   - **Well-defined.** By uniqueness in (i), all admissible choices of `f′`
     induce the same automorphism `f′_*`. By the based Dehn--Nielsen--Baer
     theorem (standard; Farb--Margalit, *A Primer on Mapping Class Groups*,
     Chapter 8), `Mod(Σ, x) → Aut(π1(Σ, x))` is injective. So `[f′]` does not
     depend on the choice.
   - **Homomorphism.** `F_f F_h` represents `λ(fh)` and covers `f′_f f′_h`,
     which is therefore an admissible choice for `fh`. So
     `σ(fh) = σ(f)σ(h)`.
   - **Section.** Forgetting `x` sends `σ(f) = [f′]` to `f`.

   So `σ` splits the Birman sequence over `L′`.
6. **Converse.** Given a section `σ: L′ → Mod(Σ, x)`, take `Σ̃ = Σ`,
   `π = id`, `P = {x}` and `λ = σ`. Each `σ(f)` has a representative fixing
   `x`, and that representative covers itself and represents `f`. `∎`
