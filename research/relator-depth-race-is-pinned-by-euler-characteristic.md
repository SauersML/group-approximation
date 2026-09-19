---
rg: 2
id: relator-depth-race-is-pinned-by-euler-characteristic
kind: claim
title: The long-relation coinvariant excess of every finite cover of a cd-2 group equals chi [K:N] − 1 minus the local H_2, so at the Følner radius it is pinned to within n eps [K:N] of chi [K:N]; relator depth is either eventually 0 or beyond the Følner radius, one cover decides which, and a counterexample carries chi regular representations of every finite quotient in its long relations
distinct_from:
  folner-transversals-kill-local-degree-two-homology: that reduces chi_Q(K) = 0 to the upper bound ell^delta <= rho_eps along a residual chain; this proves that bound has no content beyond chi_Q(K) = 0 itself, since the coinvariant excess it asks to control is an exact function of chi_Q(K) and the local H_2, and the depth takes only the values 0 or > rho_eps
  rf-weak-bass-defect-is-degree-two-approximation-defect: that identifies the defect with lim b_2(N_i)/[K:N_i] and with uniform generation of P; this computes, scale by scale, the two terms of the long-relation comparison separately (b_1 of the covers of the truncated presentations tends to dim_U A_L, which tends to 0) and the finite-quotient module structure of H_2 and of the long-relation coinvariants of a counterexample
  amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar: that shows a two-dimensional counterexample has no infinite elementary amenable quotient; this uses that for every finite-index subgroup to get b_1(N) = 0 and the exact Q[K/N]-module structure of H_2(N; Q)
---

**ESTABLISHED** (proposed; referee pending) through
`relator-depth-race-is-pinned-by-euler-characteristic-proof`, from
`rf-weak-bass-defect-is-degree-two-approximation-defect` (items 1, 3, 4),
`folner-transversals-kill-local-degree-two-homology` (items 1, 3) and
`amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar` (item 3(c)). Recalled imports: the
five-term exact sequence and its naturality; Maschke's theorem and Krull–Schmidt cancellation for
finite-dimensional `Q[F]`-modules; Lück's approximation theorem for finite free `K`-CW complexes
along a residual chain (Lück 1994); dimension-flatness of `N(K)` over `C[K]` for amenable `K`
(Lück, *L²-invariants*, Thm 6.37); additivity and cofinality of `dim_U`; Weiss's Følner
transversals; Kropholler–Linnell–Lück (finitely generated elementary amenable groups of cd 2 are
`BS(1,m)`).

**Notation** (as in `folner-transversals-kill-local-degree-two-homology`). `K = ⟨S | R⟩`,
`n = |S|`, `Γ_L = ⟨S | R_{≤L}⟩`, `M_L = ker(Γ_L → K)`, `Y_L` the presentation complex of `Γ_L`.
For finite-index `N <= K`, `N_L` is its preimage in `Γ_L`, `I_L(N) = im(H_2(N_L;Q) → H_2(N;Q))`,
and

> `A_L = H_1(M_L; Q)`, `e_L(N) = dim_Q H_0(N_L; A_L) − b_1(N_L)` (the *long-relation excess*).

`ℓ^δ` and `ρ_ε` are the relator depth and Følner radius of that node. Throughout, `K` is finitely
generated with `cd_Z K <= 2` and `b_2(K) < ∞`, and `χ = χ_Q(K)`.

1. **The excess is an exact function of `χ` and the local classes (no amenability).** For every
   finite-index `N`, every `L` and every transversal `T` of `N`,

   > `e_L(N) = χ[K:N] − 1 − dim I_L(N)`, hence `χ[K:N] − 1 − n|TB_L \ T| <= e_L(N) <= χ[K:N] − 1`.

   In particular, for `L <= ρ_ε(N)`: `|e_L(N) − (χ[K:N] − 1)| <= nε[K:N]`.
2. **The race step is the target, with no slack.** Let `δ, ε >= 0`, `δ + nε < 1`.
   - (a) *One cover decides.* If `ℓ^δ(N) <= ρ_ε(N)` for a single finite-index `N` with
     `(1 − δ − nε)[K:N] > 1`, then `χ <= 0`. The same holds if `e_L(N) <= δ[K:N]` for one such `N`
     and one `L <= ρ_ε(N)`. If `K` is also amenable and residually finite, this gives `χ = 0`.
   - (b) *Dichotomy of relator depth.* Let `K` be infinite, residually finite and amenable, with
     a residual chain `(N_i)`. If `χ = 0`, then `ℓ^δ(N_i) = 0` for all large `i` and every `δ > 0`,
     and `e_L(N_i) < 0` for all `i, L`. If `χ >= 1` and `ε > 0`, then for all large `i`,
     `ℓ^δ(N_i) > ρ_ε(N_i)`, where `ρ_ε(N_i) → ∞`, and `e_L(N_i) >= (χ − nε)[K:N_i] − 1` for all
     `L <= ρ_ε(N_i)`. No residual chain, and no finite
     cover, sees an intermediate behaviour.
   - (c) So bounding the long-relation coinvariants `H_0(N_{i,L}; A_L)` against `b_1(N_{i,L})` at
     `L = ρ_ε(N_i)`, to within `δ[K:N_i]`, is equivalent to `χ = 0` through item 1 alone. Any
     proof of it is a proof that `b_2(N_i) <= (δ + nε)[K:N_i]`, and conversely.
3. **Equivariant shape of a counterexample.** Let `K` be amenable with `χ >= 1`. Then every
   finite-index `N` has `b_1(N) = 0` and `b_2(N) = χ[K:N] − 1`. If `N` is normal and `F = K/N`,
   then as `Q[F]`-modules

   > `H_2(N; Q) ⊕ Q ≅ Q[F]^χ`, and for every `L`: `H_0(N_L; A_L) ⊕ I_L(N) ⊕ Q ≅ Q[F]^χ ⊕ H_1(N_L; Q)`.

   So, beyond `H_1` of the cover of the truncated presentation, the long relations carry `χ`
   copies of the regular representation of every finite quotient, up to a summand of dimension
   `<= n|TB_L \ T| + 1`. In twisted coefficients: `dim H_2(K; V) = χ dim V − dim V_K` and `H_1(K; V) = 0` for
   every finite-dimensional `Q[K]`-module `V` with finite image.
4. **The two terms of the comparison, scale by scale.** Let `K` be infinite, residually finite and
   amenable, with residual chain `(N_i)`, and put `β_1(L) = dim_U(U ⊗ A_L)`. Then `β_1(L)` is
   non-increasing with limit `0`, and for every fixed `L`

   > `b_1(N_{i,L}) = β_1(L)[K:N_i] + o([K:N_i])`, `dim_Q H_0(N_{i,L}; A_L) = (χ + β_1(L))[K:N_i] + o([K:N_i])`.

   So at each fixed scale the long-relation module `A_L` violates degree-0 approximation by
   exactly `χ`, independently of `L`, while its `L²`-dimension tends to `0`.
5. **Calibrations.**
   - (a) *Elementary amenable and solvable `K`* (the case to try first). These are `Z²`, the Klein
     bottle group and `BS(1,m)`, all finitely presented, so `ℓ^0(N) <=` the maximal relator
     length, `χ = 0`, and item 2(b) gives `ℓ^δ(N_i) = 0` eventually. The race is empty there, and
     item 3 shows why no explicit Følner sets from elementary amenable quotients reach a
     counterexample: every finite-index subgroup of one has `b_1 = 0` and no infinite elementary
     amenable quotient.
   - (b) *`Z² = ⟨a,b | [a,b]⟩`, `N = (mZ)²`.* For `L < 4`: `Γ_L = F_2`, `A_L ≅ Q[K]`,
     `H_0(N_L; A_L) = Q[F]` of dimension `m²`, `b_1(N_L) = m² + 1`, so `e_L = −1`. For `L >= 4`:
     `A_L = 0`, `b_1(N_L) = 2`, `e_L = −2 = −1 − dim I_L`. Item 1 holds exactly.
   - (c) *Kazhdan lattice in `SL_3(Q_2)`* (cd 2, type F, `χ = V`, relators of length 3; not
     amenable). Item 1 needs no amenability: `e_L(N) = V[Γ:N] − 1` for `L < 3` and `e_L(N) = 0`
     for `L >= 3`. The lattice has `b_1(N) = 0` for every finite-index `N` by property (T), so the
     module formula of item 3 holds for it verbatim: `H_2(N; Q) ⊕ Q ≅ Q[F]^V`. Hence the finite
     quotient module structure of item 3 is realized by a non-amenable cd-2 group, and any proof
     of the statement left in "What remains" must use amenability.

**Obstruction (the race step of the programme).** The comparison proposed after
`folner-transversals-kill-local-degree-two-homology` — bound `H_0(N_{i,L}; H_1(M_L;Q))` against
`b_1(N_{i,L})` at `L = ρ_ε(N_i)` — does not reduce the problem. Item 1 shows the difference of
the two quantities is `χ[K:N] − 1` minus a term that item 1 of the Følner node already bounds by
`nε[K:N]`. So the comparison is the target itself, and relator depth (item 2(b)) cannot be bounded
by any geometric radius without being bounded by `0`. Every route through truncated presentations
must show, in some form, that the long relations of `K` cannot carry `χ` regular representations
of every finite quotient (item 3).

**What remains.** Item 3 turns the residually finite case into one module-theoretic statement:
for a finitely generated residually finite amenable `K` of cd 2, the finite-quotient modules
`H_2(N_i; Q)` along a residual chain cannot be `Q[F_i]^χ ⊖ Q` with `χ >= 1`. That is, `K` cannot
have `H_1(K; V) = 0` and `dim H_2(K; V) >= dim V − dim V_K` for all `V` with finite image.
