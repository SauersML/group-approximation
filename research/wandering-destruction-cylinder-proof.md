---
rg: 2
id: wandering-destruction-cylinder-proof
kind: route
title: A cylinder on which an upset is entered one way can never return to itself, so recurrence and invariant measures never meet it
target: non-exact-transitions-of-injective-automata-are-wandering
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
---

Complete proof over every group `G`. Notation as in the target. `(g^(-1)x)(h) = x(gh)`, so
`Φ(x)(g) = Φ(g^(-1)x)(1)`. `Φ` is continuous, injective and commutes with the shift. `B^G` is compact
Hausdorff, so `Φ(B^G)` is closed.

**Import, verbatim.** `bijective-ca-preserve-uniform-bernoulli-measure`: "Let `G` be any group, `A` a finite
alphabet, `mu` the uniform product measure on `A^G`, and `tau: A^G -> A^G` a bijective cellular automaton.
Then `tau_* mu = mu`."

**Item 1.**
- (a) Let `x ∉ Φ(B^G)`. Since the image is closed, some open `V ∋ x` misses it. For `k >= 1`,
  `Φ^k(V) ⊆ Φ(B^G)`, so `Φ^k(V) ∩ V = ∅`, and `x` is wandering.
- (b) If `NW(Φ) = B^G`, then (a) gives `Φ(B^G) = B^G`. Conversely let `Φ` be onto, hence bijective, and
  let `λ` be the uniform product measure. By the import, `λ(Φ^(-k) V) = λ(V)` for Borel `V`.
  - Let `V` be nonempty open. It contains a cylinder `V'` with `λ(V') > 0`.
  - The sets `Φ^(-k) V'`, `k >= 0`, all have measure `λ(V')`, so they are not pairwise disjoint. Take
    `j < k` with `λ(Φ^(-j) V' ∩ Φ^(-k) V') > 0`.
  - Applying measure invariance to `Φ^(-j)`, this is `λ(V' ∩ Φ^(-(k-j)) V') > 0`. So some `y ∈ V'` has
    `Φ^(k-j) y ∈ V'`, and `Φ^(k-j)(V) ∩ V ≠ ∅`. So every point is nonwandering.
- (c) is (b) applied to every injective automaton over `G`.

**Item 2.** Put `Ψ = Φ^p`, and let `U` be an upset of `R(Ψ)` with non-exact pattern `P`.
- *Absorption.* If `x(g) ∈ U`, then `Ψ(x)(g) ∈ U`. By induction `Ψ^k(x)(g) ∈ U` for all `k >= 0`.
- (a) Let `y ∈ [P]_g`. Then `y(g) = (g^(-1)y)(1) = P(1) ∉ U`, and `Ψ(y)(g) = μ_Ψ(P) ∈ U`, where `μ_Ψ` is
  the local rule of `Ψ` on `M_Ψ`. Here `P` is read as a pattern on `M_Ψ` and `[P]_g` as its cylinder. By
  absorption `Ψ^k(y)(g) ∈ U` for all `k >= 1`. Every point of `[P]_g` has its `g`-letter outside `U`, so
  `Ψ^k([P]_g) ∩ [P]_g = ∅`.
- (b) `[P]_g` is open, so each of its points is wandering for `Ψ`. If `x ∈ NW(Ψ)` and some `g` had
  `x(g) ∉ U` and `Ψ(x)(g) ∈ U`, then `P = (g^(-1)x)|_(M_Ψ)` would be a non-exact pattern with
  `x ∈ [P]_g`, a contradiction. The reverse implication `x(g) ∈ U ⇒ Ψ(x)(g) ∈ U` is the upset property.
- (c) Let `Φ_* ν = ν`. Then `Ψ_* ν = ν`. By (a), `[P]_g ∩ Ψ^(-k)[P]_g = ∅` for `k >= 1`, so the sets
  `Ψ^(-k)[P]_g`, `k >= 0`, are pairwise disjoint: `Ψ^(-j)[P]_g ∩ Ψ^(-k)[P]_g = Ψ^(-j)([P]_g ∩ Ψ^(-(k-j))[P]_g)`.
  They all have measure `ν([P]_g)`, and `ν` is finite, so `ν([P]_g) = 0`.
  - Cesàro limits: `Φ` is continuous, so every weak-* limit `ν` of `(1/K) Σ_(k<K) Φ^k_* λ` satisfies
    `Φ_* ν = ν`, since `|(1/K)(Φ^K_* λ - λ)| <= 2/K`.
  - Supports: if `x ∈ supp ν` had a non-exact pattern at `g`, then `[P]_g` is an open neighbourhood of `x`
    of measure `0`, which contradicts `x ∈ supp ν`.
- (d) If the `Φ`-orbit of `x` is finite, then `Φ^m x = x` for some `m >= 1`: `Φ` is injective, so it
  permutes the finite orbit. Then `Ψ^m x = Φ^(pm) x = x`. If `x ∈ [P]_g`, then `x ∈ Ψ^m([P]_g) ∩ [P]_g`,
  contradicting (a).
  - An `H`-periodic configuration (`hx = x` for all `h ∈ H`, with `[G:H] < ∞`) lies in the finite set
    `Fix(H)`. That set is invariant under `Φ`, because `Φ` commutes with the shift. So its orbit is finite.

**Item 3.** `A = B \ {c}` is an upset, since `c` is never created.
- (a) `Φ` maps each constant `b^G` to the constant `μ(b^M)^G`, and it is injective. So it permutes the `|B|`
  constants. The upset `A` sends each `a^G` with `a ∈ A` to a constant with letter in `A`. The `|A|`
  constants over `A` are therefore permuted among themselves, and `c^G` is left for `c^G`: `μ(c^M) = c`.
- (b) Let `x ∈ X_fin` with `A`-support `S` finite. If `hM ∩ S = ∅`, then `(h^(-1)x)|_M = c^M`, so
  `Φ(x)(h) = c`. So `supp_A(Φ x) ⊆ S M^(-1)`, which is finite. Since `A` is an upset, `S ⊆ supp_A(Φ x)`.
- (c) Let `P ∈ B^M` with `P(1) = c` and `μ(P) ∈ A`. Put `x = P` on `M` and `x = c` elsewhere. Then
  `x ∈ X_fin`, `x(1) = c`, and `Φ(x)(1) = μ(P) ∈ A`. So `supp_A(Φ x) ⊇ supp_A(x) ⊔ {1}`.
- (d) The branch is, by its definition in the cited item 4, the set of never-created letters that are
  sometimes destroyed. Only its non-emptiness is used here, not its cofinite conclusion, so nothing is
  imported. *If.* A never-created `c` that raises the count of a finite configuration is destroyed at some
  site. *Only if.* A letter of the branch is quiescent by (a), and it raises the count by (c).

**Item 4.** `A`-sites of `x` stay in `A` because `A` is an upset. The `c`-sites of `x` are all destroyed.
So `Φ(x) ∈ A^G`. If `Φ(x) = τ(z) = Φ(z)` for some `z ∈ A^G`, then injectivity gives `x = z ∈ A^G`,
contradicting that `x` has a `c`-site. So `Φ(x) ∉ Y`.
