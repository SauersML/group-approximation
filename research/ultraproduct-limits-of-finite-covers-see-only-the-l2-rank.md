---
rg: 2
id: ultraproduct-limits-of-finite-covers-see-only-the-l2-rank
kind: claim
title: Ultraproduct and von Neumann limits of the finite covers of a residually finite cd-2 group see only its L2-invariants; the whole Euler characteristic sits in the ultraproduct of H_2 of the covers, which is rank-complementary to everything induced from Q[K], so a limit argument against L2-vanishing proves chi = 0 only by proving uniform generation of the relation module
distinct_from:
  rf-weak-bass-defect-is-degree-two-approximation-defect: that proves chi = D(P) = lim b_2(N_i)/[K:N_i] and the interchange formula for D; this shows that in the ultraproduct rank ring and in the tracial ultraproduct of the L(F_i) every module induced from Q[K] has its L2-dimension, locates chi as the rank of the cokernel of the comparison map and of the ultraproduct of H_2(N_i), and proves these two are rank-complementary, which kills the limit-against-L2-vanishing route
  folner-transversals-kill-local-degree-two-homology: that bounds local H_2 of a cover by Følner boundary counts; this proves the ultraproduct statement that H_2 of the covers meets the image of every finitely generated submodule of P in rank 0, from Lück approximation and b_2^(2) = 0, and uses it to show the limit object cannot see chi
  pro-p-route-cannot-see-amenability-in-cd-two: that kills the mod-p and pro-p routes (w15 exact mod-p Euler characteristics are satisfied by Kazhdan lattices); this kills the other route of the same brief, the von Neumann or ultraproduct limit of the regular summands Q[F_i]^chi
---

**ESTABLISHED** (proposed; referee pending) through
`ultraproduct-limits-of-finite-covers-see-only-the-l2-rank-proof`, from
`rf-weak-bass-defect-is-degree-two-approximation-defect` (items 1, 2(b), 2(c), 4). Recalled
imports: Lück's approximation theorem for matrices over `Q[K]` along a residual chain (Lück
1994); Cheeger–Gromov vanishing of `L²`-Betti numbers of infinite amenable groups; dimension
theory for finite von Neumann algebras, in particular Lück, *L²-invariants*, Thm 6.29: induction
along a trace-preserving normal inclusion preserves dimension; products and quotients of von
Neumann regular rings are regular.

**Setting.** `K` is infinite, finitely generated, residually finite and amenable, with
`cd_Z K <= 2` and `b_2(K) < ∞`. Fix an `n`-generator presentation with relation module `P`,
written `P = Z[K]^(ℕ) E` for a row-finite idempotent `E`; `A_m` is the first `m` rows of `E`
and `∂ : P → Z[K]^n` the Fox map. `(N_i)` is a residual chain, `F_i = K/N_i`, `ω` a nonprincipal
ultrafilter, `r = r(P)`, `χ = χ_Q(K) = D(P)` (target item 4). Put:

- `R_ω = ∏_i Q[F_i] / {x : lim_ω rk_{F_i}(x_i) = 0}`, the *rank ultraproduct*, with rank
  function `rk_ω(x) = lim_ω rk_{F_i}(x_i)` on matrices;
- `M_ω = ∏^ω L(F_i)`, the tracial ultraproduct (normalized traces);
- `Φ : R_ω ⊗_{Q[K]} P → V_ω := R_ω ⊗_{∏Q[F_i]} ∏_i (Q[F_i] ⊗ P) ≅ R_ω^r`, the comparison
  map from the induced module to the ultraproduct of the induced modules of the covers;
- `H_ω = ker(∂_ω : V_ω → R_ω^n)`, the reduced ultraproduct of the `H_2(N_i; Q)`.

For a submodule `X` of `R_ω^k`, `rk_ω X` is the supremum of the ranks of its finitely generated
submodules (these are f.g. projective since `R_ω` is regular), and `rk_ω(R_ω^k / X) = k − rk_ω X`.

1. **Every limit object induced from `K` computes `L²`-invariants of `K`.** The diagonal
   `K → M_ω` is trace-preserving and extends to a normal trace-preserving embedding
   `L(K) ↪ M_ω`. Hence `dim_{M_ω}(M_ω ⊗_{Q[K]} X) = dim_U(X)` for every `Q[K]`-module `X`, and
   `dim_{M_ω} H_k(K; M_ω) = b_k^{(2)}(K) = 0` for all `k` (for every `K` as above, with or without
   `χ = 0`). Likewise `rk_ω(A) = rk_U(A)` for every matrix `A` over `Q[K]`, and
   `rk_ω(R_ω ⊗ P) = sup_m rk_U(A_m) = d(P) = n − 1`.
2. **The comparison map carries all of `χ`.** `V_ω ≅ R_ω^r`, `rk_ω im Φ = n − 1` and

   > `rk_ω coker Φ = rk_ω H_ω = lim_ω b_2(N_i)/[K:N_i] = χ`.

3. **Rank complementarity.** `rk_ω(H_ω ∩ im Φ) = 0` and `rk_ω(H_ω + im Φ) = r`. Concretely, for
   every finitely generated submodule `M ≤ P`,

   > `dim_Q (H_2(N_i; Q) ∩ im(Q[F_i] ⊗ M → Q[F_i] ⊗ P)) = o([K:N_i])`,

   while `dim_Q H_2(N_i; Q) ~ χ[K:N_i]`. So in the limit the homology of the covers is a
   complement of everything that comes from `Q[K]`; it projects isomorphically in rank onto
   `coker Φ`.
4. **Obstruction (class killed).** Call an argument a *limit argument* if it passes from the
   covers to `R_ω`, `M_ω` or any trace-preserving extension of `L(K)`, and uses there only
   modules induced from `Q[K]`-modules together with `L²`-vanishing and Lück approximation. Every
   such input takes the same values for `χ = 0` and for a hypothetical counterexample with
   `χ >= 1` (item 1), so a limit argument yields `χ = 0` only through an extra step proving
   `rk_ω coker Φ = 0`. That step is equivalent to uniform generation of `P`
   (target item 2(c)), i.e. to the target itself. The exact point of failure is the
   identification `∏_ω(Q[F_i] ⊗ P) = R_ω ⊗ P`, which fails by rank `χ`.
5. **The brief's question on `b_2^{(2)}`.** `b_2^{(2)}(K) = 0` holds unconditionally (Cheeger–
   Gromov), and so does item 1 in every degree. The relation `χ = b_2^{(2)}` holds iff `χ = 0`.
   The correct relation is `χ = rk_ω coker Φ + χ^{(2)}(K) = rk_ω coker Φ`. Deciding
   `b_2^{(2)}(K) = 0` therefore carries no information.
6. **Calibrations.** If `K` is of type `FP_2`, `E` is finite, `Φ` is an isomorphism and
   `χ = 0`, as it should be. For a torsion-free lattice in `SL_3(Q_2)` (type `F`, cd 2,
   Kazhdan, not amenable) `Φ` is again an isomorphism and `rk_ω H_ω = b_2^{(2)} = χ > 0`: there
   `χ` sits inside `im Φ`, and item 3 fails. So amenability enters a limit argument only through
   `b_2^{(2)} = 0`, which moves `H_ω` out of `im Φ` and into `coker Φ` without bounding it.

**What it leaves.** Both routes of the brief are now dead: the mod-p route by
`pro-p-route-cannot-see-amenability-in-cd-two`, the limit route by item 4. What remains is
exactly the finite-level statement that `coker Φ` has rank 0: for every `δ > 0` a finitely
generated `M ≤ P` whose image in `Q[F_i] ⊗ P` has normalized dimension `>= r − δ` for
`ω`-almost all `i`. By item 3 this says: the covers' `H_2` is swallowed by finitely many relators
up to `δ[K:N_i]`. A proof must use an input that is not induced from `Q[K]` (for instance Følner
tilings of the covers themselves, as in `folner-transversals-kill-local-degree-two-homology`,
applied to `H_2` rather than to local relators).
