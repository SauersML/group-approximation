---
rg: 2
id: artin-sigma1-equals-dead-cut-laplacian-surjectivity
kind: claim
title: "Exact Sigma^1 criterion for every Artin group and discrete character: [chi] in Sigma^1 iff chi is dominant and the dead-cut Laplacian over the Novikov ring is onto"
distinct_from:
  artin-sigma1-is-connected-dominant-living-subgraph: that is the refuted graph-theoretic formula; this is an exact algebraic criterion that holds for every Artin group and has that formula's true half (r = 1) as a special case
  artin-sigma1-living-subgraph-bounds: those are Meier's two inclusions; this is an equivalence, and it gives both refutations and the ring obstruction as corollaries
  artin-sigma1-dead-edge-ring-obstruction: that is a sufficient condition for non-membership, via twisted Laurent homology over R((t)); this computes H_1 over the Novikov ring exactly, and a ring witness is one way of certifying that the level-0 Laplacian is not onto
  artin-k4-odd-family-dead-characters-lie-in-sigma1: that is one family with r = 2 and no dead vertices; this is the general reduction, which contains that computation (Steps 0-2 there) as the case r = 2
  artin-2x2-dead-joins-sigma1-iff-k-q-odd-family: that classifies one family of dead joins; this is a criterion for all graphs
---

**ESTABLISHED** by `artin-sigma1-equals-dead-cut-laplacian-surjectivity-proof`
(unreviewed; numerically cross-checked).

**Setting.**
- `Γ` is a finite simplicial graph with labels `l(e) >= 2`, and `A_Γ` is its Artin group.
- `χ : A_Γ -> Z` is nonzero, `H = ker χ`, and `N = N_χ` is the Novikov ring.
- `Liv_0`, dead edges, `Liv^χ` and dominance are as in
  `artin-sigma1-is-connected-dominant-living-subgraph`.
- `B_1, ..., B_r` are the connected components of `Liv^χ`, and `[v]` is the component of a
  living vertex `v`.
- `S_k(z) = 1 + z + ... + z^{k-1}`.
- `K_r(R) = {n ∈ R^r : Σ n_i = 0}` for a ring `R`. It is free of rank `r - 1`.
- If `χ` is dominant, fix for each dead vertex `w` a living neighbour `u(w)`.

**The dead-cut Laplacian.** `L_χ : N^{Rel} -> K_r(N)` sends the basis vector of a relation
`ρ` to `g_ρ (e_{a(ρ)} - e_{b(ρ)})`. The relations are:

| type | edge | `g_ρ` | joins |
|---|---|---|---|
| D | dead edge `{p,q}`, label `2k`, `χ(p) > 0` | `S_k(pq)(p-1)` | `[p]`, `[q]` |
| V | `{w,x}`, `w` dead, `x` living, label `2k'` | `w - 1` | `[x]`, `[u(w)]` |
| W | `{w,x}`, both dead | `(∂r_{wx}/∂w)(w - 1)` | `[u(w)]`, `[u(x)]` |

Here `r_{wx}` is the Artin relator of the edge and `∂` is the Fox derivative.

**Theorem.**
1. **(H_1 formula.)** If `χ` is dominant, then `H_0(A_Γ; N_χ) = 0` and
   `H_1(A_Γ; N_χ) ≅ coker L_χ` as left `N`-modules. Here `H_*` is homology of
   `N ⊗_{ZA_Γ} C_*(X̃)`, `X` is the presentation complex, and the images of the D, V and W
   generators span the same left `N`-submodule as the images of the Fox rows.
2. **(Criterion.)** `[χ] ∈ Σ^1(A_Γ)` iff `χ` is dominant and `L_χ` is onto, iff `χ` is
   dominant and `L_{-χ}` is onto, iff `ker χ` is finitely generated.
3. **(Level-0 sufficiency.)** Let `σ_D = S_k(pq)`, `σ_V = w - 1` and
   `σ_W = (∂r_{wx}/∂w)(w - 1)`. These lie in `Z[H]`. The level-0 Laplacian is
   `L_0 : Z[H]^{Rel} -> K_r(Z[H])`, sending the basis vector of `ρ` to `σ_ρ (e_a - e_b)`.
   If `χ` is dominant and `L_0` is onto, then `[χ] ∈ Σ^1(A_Γ)`.
4. **(Canonical image.)** The image of `L_0` does not depend on the choices `u(w)`. The same
   holds for the image of `L_χ`.
5. **(Real characters.)** Parts 1, 3 and 4, and the first two equivalences of part 2, hold
   verbatim for every nonzero `χ : A_Γ -> R`. Here `Z[H]` is again the level-0 quotient
   `N_{≥0}/N_{>0}`. This part uses the real-character form of Sikorav's theorem, imported
   verbatim in the proof.
6. **(Combinatorial type.)** Whether `L_0` is onto depends only on the *type* of `χ`: the
   sign vector `(sign χ(v))_v` together with the set of edges `{u,v}` with
   `χ(u) + χ(v) = 0`. So for each `Γ` there are finitely many cases. The proof is Step 11.

**Corollaries.**
- *Meier sufficiency* is the case `r = 1`, where `K_1 = 0`.
- *Cut necessity.* Let `S` be a nonempty proper set of blocks and let `J_S` be the left ideal
  `Σ N g_ρ` over the relations with exactly one end in `S`. If `J_S ≠ N`, then
  `[χ] ∉ Σ^1`. For `r = 2` this is an iff: `[χ] ∈ Σ^1` iff `J = N`.
- *Both refutations of the conjecture are level-0 identities.*
  - In `K_q` (`q` odd): `x^{2m} = S_q(x) - T S_2(ac) + T ab^{-1}(S_2(bc) - S_2(be))`.
  - In the mixed `K` (labels `4,4,4,6`, `x = ae`):
    `S_3(x) - x S_2(ac) + x ab^{-1}(S_2(bc) - S_2(be)) = 1`.
  - In both cases `L_0` is onto with coefficients in `Z[H]`.
- *Ring witnesses.* Take a ring homomorphism `Z[A_Γ] -> R` killing the `σ_ρ` across a cut
  (the dead-edge ring obstruction). It shows that `L_0` is not onto.
- *Augmentation test.* Applying `ε : Z[H] -> Z` shows that if `L_0` is onto, then the integer
  Laplacian with weight `k` on each D-relation (and `0` on V and W) is onto `K_r(Z)`. For
  `r = 2`: the gcd of the half-labels of the crossing dead edges is `1`. This matches the
  prime-`p` family.
- *What is left.* The following is not known: whether `L_χ` onto forces `L_0` onto. That is
  `artin-sigma1-is-level-zero-laplacian-surjectivity`.

**Evidence beyond the proof.** The artifacts compute `dim H_1` of the full Fox complex and
`dim coker L_χ` for random complex specializations. These are reflection representations of
the Coxeter quotients `W(m')` with `m' | l`, times `t^χ`.
- 400 of 400 random graphs agree, with both the unsimplified generators and the simplified
  generators in the table.
- `H_1 ≠ 0` in 39 of the instances of the main check and in 43 of the companion check.
- Dropping the D, V or W relations changes the answer in 56, 14 and 2 instances. So each
  relation type matters and the check has power.
