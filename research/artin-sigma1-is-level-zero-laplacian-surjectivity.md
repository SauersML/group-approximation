---
rg: 2
id: artin-sigma1-is-level-zero-laplacian-surjectivity
kind: claim
title: "Corrected Sigma^1-conjecture: a dominant discrete character of an Artin group lies in Sigma^1 iff its level-0 dead-cut Laplacian over Z[ker chi] is onto"
distinct_from:
  artin-sigma1-is-connected-dominant-living-subgraph: that is the refuted formula 'Liv^chi connected'; this replaces connectivity by surjectivity of a Z[ker chi]-linear Laplacian on the blocks of Liv^chi, which is automatic when r = 1
  artin-sigma1-equals-dead-cut-laplacian-surjectivity: that is the proved criterion over the Novikov ring N_chi, and it proves the 'if' half of this claim; this asks for the converse, that the Novikov-level solution can be pushed down to level 0
  artin-sigma1-dead-edge-ring-obstruction: that is one certificate that L_0 is not onto; this asks whether non-surjectivity of L_0 always forces non-membership
---

**OPEN.** Let `χ : A_Γ -> R` be nonzero and dominant, and let `L_0` be the level-0 dead-cut
Laplacian of `artin-sigma1-equals-dead-cut-laplacian-surjectivity`. Its image is
independent of the choices, by part 4 there. Whether it is onto depends only on the
combinatorial type of `χ`, by part 6 there. The discrete case already carries the whole
content of the claim.

**Claim.** `[χ] ∈ Σ^1(A_Γ)` iff `L_0 : Z[H]^{Rel} -> K_r(Z[H])` is onto, where `H = ker χ`.

**What is proved.**
- The "if" half is part 3 of the established criterion.
- The claim is therefore equivalent to this statement: if `L_χ` is onto over `N_χ`, then
  `L_0` is onto over `Z[H]`.
- For `r = 2` this becomes: if the left ideal `J = Σ N g_ρ` is `N`, then
  `Σ Z[H] σ_ρ = Z[H]`.

**Structural consequence (a test).** If the claim holds, then `Σ^1(A_Γ)` is a union of
*type cells*. A type cell is the set of characters with a given sign vector and a given set
of edges with `χ(u) + χ(v) = 0`; it is a relatively open polyhedral cone. So membership
would be constant on each cell.
- The Novikov criterion alone does not visibly give this, because `N_χ` varies with `χ`
  inside a cell.
- A character in `Σ^1` and a character outside it, of the same type, would refute the
  claim.

**Consistent with every known case.**
- Meier sufficiency (`r = 1`).
- No dead edges (including right-angled Artin groups): augmentation kills every V and W
  generator. So `L_0` is onto iff `r = 1` iff `Liv_0` is connected, which is Meier's answer.
- The dihedral and prime-`p` families: `L_0` fails the augmentation test.
- `K_q` for `q` odd, and the mixed `K` (labels `4,4,4,6`): explicit level-0 identities.
- `A(3,4,6)`: it has a rank-two ring witness, so `L_0` is not onto, and `[χ] ∉ Σ^1` is
  established.

**Testable predictions.** Each of these would refute the claim if it failed.
1. *Sign symmetry.* `Σ^1 = -Σ^1`, so the claim predicts that `L_0(χ)` is onto iff
   `L_0(-χ)` is onto.
   - Replacing `χ` by `-χ` replaces each `σ_D = S_k(pq)` by `S_k(qp) = q S_k(pq) q^{-1}`,
     with a *different* conjugator `q ∉ H` for each dead edge. The V and W generators do not
     change.
   - So the prediction is a non-trivial statement about `Z[H]`.
2. *No hidden negative-level cancellation.* A Novikov combination `Σ λ_ρ g_ρ = 1` in which
   some `λ_ρ` has support at negative levels would have to be replaceable by one with
   `λ_ρ ∈ N_{≥0}`. After that, the level-0 part gives an `L_0`-identity.

## Attempts

**w17 z-follow (2026-09-17): leading-term descent. This reduces the claim to syzygy lifting.**
Let `χ` be discrete, and suppose `Σ_ρ λ_ρ g_ρ (e_a - e_b) = f_i` with `λ ∈ N^{Rel}`.
- If every `λ_ρ ∈ N_{≥0}`, take level-0 parts. Using `g_ρ = ε_ρ σ_ρ + δ_ρ` (Step 7 of the
  proof), this gives an `L_0`-identity.
- Otherwise let `m < 0` be the least level in the supports and `t ∈ G` with `χ(t) = m`.
  The level-`m` part of the identity reads `Σ_ρ λ^{(m)}_ρ ε_ρ σ_ρ (e_a - e_b) = 0`, because
  `f_i` sits at level `0 > m`. So `c = t^{-1} λ^{(m)} ∈ Z[H]^{Rel}` is a **level-0 syzygy**.
- *Lemma (proved here).* Suppose every level-0 syzygy `c` lifts: there is
  `s ∈ N_{≥0}^{Rel}` with `s ≡ c` mod `N_{>0}` and `Σ s_ρ g_ρ (e_a - e_b) = 0`.
  - Then `λ - t s` is again a solution, and its least level is `> m`.
  - Levels are integers, so after at most `|m|` steps all coefficients are in `N_{≥0}`.
  - Hence syzygy lifting implies the claim for that `(Γ, χ)`.
- *Syzygies that do lift.*
  - V and W generators equal their `σ` exactly (`δ = 0`). So every syzygy supported on V and
    W relations lifts verbatim. One example is `W = (∂r/∂w)·V` when both join the same pair
    of blocks.
  - A single D relation has no syzygy. If `c S_k(x) = 0` with `x ∈ H` of infinite order,
    then `c(x^k - 1) = 0`, and finite support forces `c = 0`.
- *Where it stops.* Syzygies that mix two or more D relations, `Σ c_ρ S_{k_ρ}(p_ρ q_ρ) = 0`,
  must lift to relations among the `S_{k_ρ}(p_ρ q_ρ)(p_ρ - 1)`. The factors `(p_ρ - 1)` differ
  and do not commute with the `c_ρ`.
  - No general lifting mechanism is known.
  - A non-lifting D-D syzygy is exactly where a counterexample would have to live: a dead
    cut that the Novikov ring closes only through negative-level cancellation.

**w19 z-follow (2026-09-17): depth hierarchy, and a kill of every shape-only descent
argument.** The claim stays OPEN.
- *Reformulation (established,
  `artin-sigma1-is-union-of-finite-depth-level-systems`).* `[χ] ∈ Σ^1` iff some finite
  `Z[H]`-system `R_m` on levels `-m..0` is solvable.
  - `R_m ⇒ R_{m+1}` and `R_0 ⟺ L_0` onto. So this claim is exactly collapse of the hierarchy
    at depth 0.
  - For `r = 2`: `R_1 ⟺ θ(J_0) + d^1(Syz_0) = Z[H]`, where `d^1(ν) = Σ_{D, χ(p)=1} ν_ρ σ_ρ h_ρ`.
    A counterexample at depth 1 is precisely a mixed D–D syzygy with `d^1(ν)` a unit mod
    `θ(J_0)` while `J_0 ≠ Z[H]`.
- *Class kill (established,
  `novikov-level-descent-fails-for-d-shaped-laplacian-systems`).* The swap toy
  `Z^2 ⋊ Z`, with `g_1 = (1+a)(ab·t - 1)` and `g_2 = (1+b+b^2)(t-1)`:
  - is Novikov onto at both signs, at depth 1;
  - is not level-0 onto at either sign (quotient `Z[ω]`);
  - has `θ`-stable ring hull equal to everything, cyclotomic `σ`, and abelian `H`.

  So no argument that uses only the D-shape, cyclotomicity, sign symmetry, ring or Alexander
  vanishing and least-level peeling can prove this claim. Every such argument dies at the
  lifting of the level-(-1) syzygy, and the invariant is `d^1`.
- *What the toy lacks* is the Artin constraint `[p, (pq)^k] = 1`, which every dead edge
  satisfies. Gate: with this constraint and `H` abelian and torsion-free, descent holds,
  because `J_0` becomes `θ`-stable and two-sided. A proof must therefore use the constraint
  with non-abelian `H`. A counterexample must realise a toy-like `d^1` under the constraint.
- *On prediction 1.* `Σ^1 = -Σ^1` is already known, so the prediction tests only the level-0
  half. The two level-0 ideals at `±χ` are related by `θ`-twists and dead-edge conjugators;
  in the toy both are proper. It gives no evidence against a depth-1 phenomenon.
