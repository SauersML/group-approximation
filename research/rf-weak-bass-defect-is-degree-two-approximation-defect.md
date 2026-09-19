---
rg: 2
id: rf-weak-bass-defect-is-degree-two-approximation-defect
kind: claim
title: Over a residually finite group the weak-Bass defect of a big projective of finite rational rank is nonnegative and equals its Lück-approximation defect; for amenable groups of cd 2 it is lim b_2(N_i)/[K:N_i], so Kropholler's question for residually finite groups is Lück approximation in degree 2, and an L2-Swan step through an amenable quotient only moves the defect
distinct_from:
  l2-finite-projectives-over-amenable-groups-satisfy-weak-bass: that is the open inequality D(C) <= 0; this proves the reverse inequality D(C) >= 0 over residually finite groups and identifies D(C) with the failure of Lück approximation for C, so over residually finite groups the open inequality is an approximation statement
  flat-weak-bass-holds-exactly-for-locally-indicable-groups: that uses Swan's theorem to pass weak Bass up finite index; this uses Swan's theorem together with Bass's big-projectives theorem on every finite quotient at once, and combines it with Lück approximation
  amenable-cd-two-bass-defect-equals-euler-characteristic: item 3(c) there computes D(res_N P) only for groups without free subsemigroups; this proves chi_Q(N) = [K:N] chi_Q(K) for every finitely generated group of cd 2 with b_2 finite, and shows D(P) = lim b_2(N_i)/[K:N_i] in the residually finite amenable case
  amenable-cd-two-groups-have-an-l2-rank-gap: that records no result for residually finite groups; this reduces the residually finite case, in both directions, to Lück approximation of b_2 along a residual chain
---

**ESTABLISHED** (proposed; referee pending) through
`rf-weak-bass-defect-is-degree-two-approximation-defect-proof`, from
`amenable-cd-two-bass-defect-equals-euler-characteristic` (item 1),
`amenable-cd-two-kropholler-iff-locally-indicable` (items 2 and 3(i)) and
`flat-weak-bass-holds-exactly-for-locally-indicable-groups` (§4(c) of its proof). Recalled
imports: Bass's theorem that non-finitely-generated projective `Z[F]`-modules are free (`F`
finite; Bass 1963); Swan's theorem that `Q ⊗ P` is `Q[F]`-free for finitely generated projective
`Z[F]`-modules `P` (Swan 1960); Lück's approximation theorem for matrices over `Q[K]` along a
residual chain (Lück 1994); additivity and cofinality of `dim_U`; vanishing of `L²`-Betti numbers
of infinite amenable groups (Cheeger–Gromov); Kropholler–Linnell–Lück (a finitely generated
elementary amenable group of cd 2 is `BS(1,m)`, `m ≠ 0`).

**Notation.** `K` is a group, `U = U(K)`, `⊗ = ⊗_{Z[K]}`. `C` is a countably generated projective
`Z[K]`-module, written `C = Z[K]^(ℕ) E` for a row-finite idempotent matrix `E` acting by right
multiplication. `A_m` is the matrix of the first `m` rows of `E`. Put

> `r(C) = rank_Q(Q ⊗ C)`, `d(C) = dim_U(U ⊗ C)`, `D(C) = r(C) − d(C)` (the Bass defect).

For a finite quotient `F = K/N` and a `Q[F]`-module `M`, `dim_F M = dim_Q M / |F|`, and
`rk_F(A)` is the normalized rank of `A mod N`. A *residual chain* is a nested sequence of
finite-index normal subgroups `N_i` with trivial intersection; `F_i = K/N_i`.
`χ_Q(K) = 1 − b_1(K) + b_2(K)` with `b_k = dim_Q H_k(−; Q)`. `P` is the relation module of an
`n`-generator presentation.

1. **Finite-quotient Swan for big projectives.** For every group `K`, every `C` with
   `r(C) < ∞` and every finite quotient `F = K/N`,

   > `Q[F] ⊗ C ≅ Q[F]^{r(C)}`, hence `rank_Q(Q ⊗_{Z[H]} C) = [K:H] r(C)` for every finite-index `H`.

   No amenability, torsion-freeness or bound on `d(C)` is needed.
2. **Weak Bass is an approximation statement over residually finite groups.** Let `K` be
   residually finite with a residual chain `(N_i)`, and `r(C) < ∞`.
   - (a) *Reverse inequality:* `d(C) <= r(C)`. So `d(C)` is automatically finite and
     `D(C) ∈ [0, r(C)]`.
   - (b) *Interchange formula:* `rk_{F_i}(A_m) <= r(C)` for all `i, m`,
     `sup_m rk_{F_i}(A_m) = r(C)` for every `i`, and

     > `D(C) = lim_i sup_m rk_{F_i}(A_m) − sup_m lim_i rk_{F_i}(A_m)`.

   - (c) Hence the following are equivalent: WBB for `C` (`D(C) <= 0`); `D(C) = 0`;
     *Lück approximation for `C`*, i.e. `lim_i dim_{F_i}(Q[F_i] ⊗ C) = d(C)`; *uniform
     generation*, i.e. for every `δ > 0` there is a finitely generated submodule `M ≤ C` with
     `lim_i dim_{F_i} im(Q[F_i] ⊗ M → Q[F_i] ⊗ C) >= r(C) − δ`.
3. **Euler characteristics of cd-2 groups are multiplicative without finite presentability.** Let
   `K` be finitely generated with `cd_Z K <= 2` and `b_2(K) < ∞`. For every subgroup `H` of finite
   index, `b_2(H) < ∞` and

   > `χ_Q(H) = [K:H] χ_Q(K)`, and `D(res_H P) = [K:H] D(P)` whenever `d(P) < ∞`.

   If `b_1(K) = 0`, then `b_2(H) = [K:H](1 + b_2(K)) − 1 + b_1(H) >= [K:H] − 1`.
4. **Bass defect = degree-2 approximation defect.** Let `K` be infinite, finitely generated,
   residually finite and amenable, with `cd_Z K <= 2` and `b_2(K) < ∞`. Along every residual
   chain, `b_1(N_i)/[K:N_i] → 0` and

   > `lim_i b_2(N_i)/[K:N_i] − b_2^{(2)}(K) = χ_Q(K) = D(P) >= 0.`

   In particular `b_1(K) <= 1 + b_2(K)` for every such `K`.
5. **Reduction, both directions.** The following are equivalent.
   - (a) Kropholler's question for residually finite groups of cd at most 2: every residually
     finite amenable group of `cd_Z <= 2` is elementary amenable.
   - (b) *Lück approximation in degree 2:* every finitely generated residually finite amenable
     group `K` of cd 2 has `b_2(N_i) = o([K:N_i])` along some (equivalently every) residual chain.
   - (c) `l2-finite-projectives-over-amenable-groups-satisfy-weak-bass` for relation modules of
     finitely generated residually finite amenable groups of cd 2.

   A residually finite counterexample `K` with finite abelianization (it exists by item 3(i) of
   `amenable-cd-two-kropholler-iff-locally-indicable` if (a) fails) has
   `b_2(N) >= [K:N] − 1` for every finite-index `N`, and `b_2(N_i)/[K:N_i] → 1 + b_2(K) >= 1`,
   while `b_2^{(2)}(K) = 0`.
6. **Obstruction: an L²-Swan step through an infinite amenable quotient moves the defect and
   does not remove it.** Let `K` be finitely generated with `cd_Z K <= 2` and
   `b_2(K) < ∞`, `N ⊴ K`, `Γ = K/N` infinite, and `P_Γ = Z[Γ] ⊗ P`. Write `β_k = dim_{U(Γ)} H_k(K; U(Γ))` and
   `χ^{(2)}(K; Γ) = β_0 − β_1 + β_2` (assume `β_2 < ∞`). Then

   > `D_Γ(P_Γ) = χ_Q(K) − χ^{(2)}(K; Γ)` and, if `K` is amenable, `D_K(P) = D_Γ(P_Γ) + χ^{(2)}(K; Γ)`.

   - (a) The L²-Swan statement for `(K, N, P)` is literally weak Bass for `P_Γ` over `Γ`, i.e.
     `χ^{(2)}(K; Γ) >= χ_Q(K)`. For finite `Γ` it holds with equality (item 1); for `Γ = K` it is
     the target.
   - (b) To pass from `Γ` to `K` one needs `dim_{U(Γ)}(U(Γ) ⊗ P) <= dim_U(U ⊗ P)`, i.e.
     `χ^{(2)}(K; Γ) <= 0`. In an amenable counterexample (`χ_Q(K) >= 1`) the L²-Swan statement
     and this lifting inequality cannot both hold for any `Γ`, since together they give
     `D_K(P) <= 0`.
     So L²-Swan, even proved for all infinite amenable quotients, does not give the target. The
     missing piece is `L²`-approximation of `χ^{(2)}` from `Γ`-covers to `K`, the analogue of
     item 5(b).
   - (c) The lifting inequality is false for finitely presented modules: `K = Z²`, `N = Z × 0`,
     `M = Z[K]/Z[K](x − 1)` has `dim_{U(K)} = 0 < 1 = dim_{U(Γ)}`. So it must use projectivity.
   - (d) If `b_1(K) = 0` and `Γ` is locally indicable, then `Γ = 1`. The quotients reachable by
     `flat-weak-bass-holds-exactly-for-locally-indicable-groups` are virtually locally indicable
     with finite abelianization.

**Calibrations.**

- *`Z²`, `BS(1,m)`, free groups, surface groups:* `χ_Q` is multiplicative, and `D(P) = 0` for
  the amenable ones. Consistent with items 3–4.
- *Flat modules violate item 2(a).* Over `K = Z = ⟨t⟩`,
  `M = colim(Z[K] →·(t−1) Z[K] →·(t−1) ⋯)` is flat with `r(M) = 0` and `d(M) = 1`, so
  `D(M) = −1 < 0`. The Hantzsche–Wendt flat module `M_B` of
  `amenable-cd-two-bass-defect-equals-euler-characteristic` has `D = +1` and violates item 1:
  `Q[F] ⊗ M_B` is not `Q[F]`-free. So both signs of the defect occur for flat modules over
  residually finite groups. Items 1 and 2(a) use projectivity (Bass + Swan): over a residually finite
  group projectivity already pins `D` to `[0, r]`.
- *Finitely generated `C`* (e.g. `P` for `K` of type `FP_2`): `E` can be taken finite, so
  `A_m = E` for large `m`, the two limits in item 2(b) commute, and `D(C) = 0`. This is the
  weak Bass conjecture for finitely generated projectives over residually finite groups, a known
  case, recovered here from Swan + Lück.

**What this changes.** Over residually finite groups the target inequality has no content beyond
Lück approximation: `D(C) >= 0` always, and `D(C) = 0` is exactly uniform approximation for
`C`. For Kropholler's question the residually finite case is now one named statement: the
normalized second Betti numbers of a residual chain of a finitely generated amenable group of cd 2
tend to `b_2^{(2)} = 0` (known for type `FP_2`, open without it). A residually finite
counterexample must have linear growth of `b_2`, with slope exactly `1 + b_2(K)`. The proposed
L²-Swan route through infinite amenable quotients cannot close the gap by itself (item 6).

## Attempts

- **2026-09-18 (lane `w17-112`): the Følner-tiling scheme for the degree-2 approximation. The local
  part is proved, and the rest is a race between relator depth and Følner radius.** See
  `folner-transversals-kill-local-degree-two-homology` (proposed ESTABLISHED).
  - *Local bound, for any group.* Let `I_L(H)` be the part of `H_2(H; k)` carried by relators of
    length `<= L`. Then `dim I_L(H) <= n|T B_L \ T|` for every transversal `T` of every
    finite-index `H`. The proof: a 2-cycle of the universal cover supported on `T` is a
    boundary, so it dies in `X_H`, and rank-nullity on `k[T]^c` leaves room only on the Følner
    boundary. With Weiss's Følner transversals, `dim I_L(N_i) = o([K:N_i])` for every fixed `L`,
    for every residually finite amenable `K`, of any cd.
  - *Kazhdan check.* For the `SL_3(Q_2)` lattice `Γ` of `pro-p-route-cannot-see-amenability-in-cd-two`,
    the bound reads `|T B_3 \ T| >= (V[Γ:N] − 1)/(6V + 1)`. This is true, since `Γ` is
    non-amenable. So the scheme fails for `Γ` only at the choice of a small-boundary transversal,
    which is exactly the amenability input.
  - *What dies.* Any Følner-tiled control of `H_2` of `P ⊗ Z[K/N_i]` using relators of bounded
    length. In a counterexample, the part of `H_2(N_i)` it misses is
    `χ_Q(K)[K:N_i] + o([K:N_i])`.
  - *Reduction, both directions.* Using integrality of `χ`, the target for `K` is equivalent to
    this: for some `δ + nε < 1`, the relator depth `ℓ^δ(N_i)` is at most the Følner radius
    `ρ_ε(N_i)` for infinitely many `i`. By the five-term sequence, the missing part is
    `dim H_0(N_{i,L}; H_1(M_L)) − b_1(N_{i,L}) + b_1(N_i)`, where `M_L = ker(⟨S | R_{≤L}⟩ → K)`.
  - *Next step.* Bound these coinvariants of the long relations at `L = ρ_ε(N_i)`.
- **2026-09-18 (lane `w18-112`): the relator-depth versus Følner-radius race is the target itself,
  with no slack.** See `relator-depth-race-is-pinned-by-euler-characteristic` (proposed
  ESTABLISHED).
  - *Excess identity.* This holds for any fg `K` of cd 2 with `b_2 < ∞`, without amenability. The
    long-relation excess `e_L(N) = dim H_0(N_L; H_1(M_L)) − b_1(N_L)` equals
    `χ[K:N] − 1 − dim I_L(N)` exactly. At `L <= ρ_ε(N)` it lies within `nε[K:N]` of `χ[K:N] − 1`.
    So the proposed bound on the coinvariants at the Følner radius is equivalent to `χ = 0`.
  - *Dichotomy.* Along a residual chain, `ℓ^δ(N_i)` is eventually `0` if `χ = 0`, and eventually
    `> ρ_ε(N_i) → ∞` if `χ >= 1`. A single cover `N` with `ℓ^δ(N) <= ρ_ε(N)` and
    `(1 − δ − nε)[K:N] > 1` already forces `χ = 0`. Relator depth cannot be bounded by any radius
    without being bounded by `0`.
  - *Shape of a counterexample.* Every finite-index `N` has `b_1(N) = 0`. For normal `N`,
    `H_2(N; Q) ⊕ Q ≅ Q[K/N]^χ`, and the long-relation coinvariants carry `Q[K/N]^χ` at every
    scale, beyond `H_1(N_L)`. For fixed `L`, `b_1(N_{i,L})/[K:N_i] → dim_U A_L → 0`, while the
    coinvariants grow like `(χ + dim_U A_L)[K:N_i]`.
  - *Elementary amenable first.* These are all `BS(1,m)`, which are finitely presented, so the race
    is empty there. A counterexample has no elementary amenable quotient that could supply
    explicit Følner sets.
  - *Calibration.* The `SL_3(Q_2)` Kazhdan lattice also satisfies `H_2(N) ⊕ Q ≅ Q[F]^V`.
  - *Next step.* Rule out `H_2(N_i; Q) ⊕ Q ≅ Q[F_i]^χ`, `χ >= 1`, along a residual chain of a
    residually finite amenable cd-2 group. Equivalently: `H_1(K; V) = 0` and
    `dim H_2(K; V) = χ dim V − dim V_K` for all finite-image `V`. Any proof must use amenability
    beyond Følner transversals of bounded radius.
- **2026-09-18 (lane `w19-112`): the ultraproduct / von Neumann limit route is dead: the
  limit sees only the `L²` rank.** See `ultraproduct-limits-of-finite-covers-see-only-the-l2-rank`
  (proposed ESTABLISHED, obstruction).
  - *Induced data are `χ`-blind.* `L(K) ↪ ∏^ω L(F_i)` preserves the trace, so every module
    induced from `Q[K]` has its `L²`-dimension there, and so does every module induced into the
    rank ultraproduct `R_ω` of the `Q[F_i]`. The induced Fox complex has profile `(n − 1, n, 1)`
    with homology of rank 0, whatever `χ` is.
  - *Where `χ` lives.* `χ = rk coker(Φ : R_ω ⊗ P → ∏_ω Q[F_i] ⊗ P) = rk ∏_ω H_2(N_i)`, and
    `∏_ω H_2(N_i) ∩ im Φ = 0`. The covers' `H_2` meets the image of every finitely generated
    `M ≤ P` in dimension `o([K:N_i])`.
  - *Brief's question.* `b_2^{(2)} = 0` is unconditional. `χ = b_2^{(2)}` holds iff `χ = 0`, so
    forcing `b_2^{(2)} = 0` decides nothing.
  - *Next step.* Prove `rk coker Φ = 0` at the finite level, from structure of the covers that
    is not induced from `Q[K]`: `H_2(N_i)` swallowed by finitely many relators up to `δ[K:N_i]`.
- **2026-09-18 (lane `w20-112`): the finite-level `coker Φ` step is the target, and Følner
  tilings compute `χ` rather than bound it.** See
  `folner-tile-collapse-of-cycle-module-computes-chi-exactly` (proposed ESTABLISHED,
  obstruction).
  - *Exact collapse.* In the Cayley-cycle model `Q[X] ⊗ P → Q[X]^n → Q[X]`, every tile, at every
    scale and with no relator-length condition, spans an acyclic subcomplex whose 2-cycles meet
    `H_2(N)` in `0`. Hence `H_2(N) ≅ H_2(C/T_*)`, with quotient dimensions
    `(χ[K:N] + β − c, β, 0)` for a transversal. Also `b_1(N) <= β − c + 1`.
  - *Blindness.* Følner transversals give `b_2(N_i)/[K:N_i] → χ` with no Lück approximation, and
    every estimate from the collapse has the form `b_2 = χ[K:N] + O(β)`. `χ` enters only through
    Swan's `r = χ + n − 1`. Covering `H_2(N_i)` by finitely many relators up to `δ[K:N_i]` is
    equivalent to `χ <= δ`, so the step has no content beyond the target. The relator-depth race
    becomes the single number `r`.
  - *Next step.* Bound `dim H_0(N_i; Q ⊗ P) <= (n − 1)[K:N_i] + o` from a non-tiling input. On
    the escape side, look for a torsion-free, amenable, non-elementary-amenable group of cd 2
    whose finite-index subgroups all have `b_1 = 0`.
- **2026-09-19 (lane `w21-112`): the Swan-rank step through `Z`-quotients (Alexander modules).**
  See `cd-two-z-kernels-have-zero-or-free-alexander-h2` (proposed ESTABLISHED; reduction and
  obstruction).
  - *Idea.* Replace the finite quotients by `φ : H ↠ Z`. Then `Λ = Q[t^{±1}]` is a PID, so
    `Λ ⊗ P` is free of rank `r`. Swan and Lück hold exactly there, with no amenability or
    residual finiteness.
  - *Results.* `H_2(ker φ; Q)` is a free `Λ`-module, so it is `0` or infinite-dimensional. The
    Alexander formula `χ_Q = rk H_2(ker) − rk H_1(ker)` holds. Along the cyclic tower,
    `b_2(H_m) = mρ_2 + O(1)`, and `H_2(H_m)` contains `Q[Z/m]^{ρ_2}`.
  - *Construction kill.* Every virtually (finite-`b_2`)-by-`Z` group has `χ <= 0`. This covers
    ascending HNN extensions over arbitrary bases of finite `b_2`.
  - *Escape-side dichotomy.* A counterexample is either (I) virtually rationally perfect, with
    `H_2(N) ⊕ Q ≅ Q[F]^χ`, or (II) fibred, with every virtual `Z`-kernel non-fg, non-EA and with
    `H_2 ≅ Λ^{ρ_2}`, `ρ_2 >= [K:H]`.
  - *Class result.* If every fg subgroup with finite abelianization is virtually
    (finite-`b_2`)-by-`Z`, the group is solvable.
  - *Effect on the target.* For `Γ = Z`, item 6(a) holds with equality, and 6(b) becomes
    `ρ_2 <= ρ_1`. The induced module structure on the remainder is free of rank `ρ_2`, so it
    cannot make `H_2` small.
  - *Next step.* (II): prove `rk_Λ H_2(L) <= rk_Λ H_1(L)` for one amenable Z-kernel `L`.
    `F_2 × F_2` has `A_2 = Λ²` and shows amenability is needed. (I): decide whether a
    residually finite amenable cd-2 group can have `b_1 = 0` on every finite-index subgroup.
- **2026-09-19 (lane `w22-112`): the Ore/Følner step for the fibred type (II) is blocked.**
  See `fibred-ore-rank-comparison-is-local-indicability` (proposed ESTABLISHED; obstruction).
  - *Result.* For `φ : G ↠ Z`, the comparison `rank_{Q(t)} φ(A) <= rk_U(A)` holds for all
    matrices exactly when `G` is locally indicable. It then already holds on `Q[ker φ]`, where it
    is the augmentation comparison. In a fibred counterexample, the fibre contains a
    finitely generated rationally perfect counterexample `J`. The Fox matrix of `J` is constant
    in `t` and breaks every Ore, Følner or specialization rank comparison over `Q[L] ⋊ ⟨t⟩`.
  - *Calibrations.* `Z ≀ Z` (amenable, comparison holds, cd `∞`) has `ρ_2 = ∞ > ρ_1 = 1`.
    `F_2 × F_2` (cd 2, comparison holds, not amenable) has `ρ_2 − ρ_1 = 1`. So
    `ρ_2 <= ρ_1` needs amenability, cd 2 and a comparison valid only on projective summands,
    all at once.
  - *Effect on the target.* Item 6(b) for `Γ = Z` on the relation module is equivalent to
    `χ <= 0`, and no easier than the core inequality for L²-finite projectives. Type (I) remains
    open.
  - *Next step.* Use the splitting `P ⊕ P'' = Q[H]^{(∞)}` together with the `Λ`-freeness of
    `Λ ⊗ P`, or show that fibre descent ends in a type (I) counterexample.
- **2026-09-19 (lane `w23-112`): fibre descent stops after one step; the finite-index step is the gap.**
  See `zero-divisor-support-is-fibre-conserved` (proposed ESTABLISHED; obstruction).
  - *Result.* For any `φ : H ↠ Z`, the minimal zero-divisor support satisfies
    `μ(ker φ) = μ(H)`. Normalized minimal pairs lie in every fibre at once, hence in the
    rational derived core, and generate a finitely generated `J` with `b_1(J) = 0`. In an
    amenable cd-2 counterexample every finite-index `J' ≤ J` is again a counterexample, with
    `μ(J') >= μ(J)`. If `b_2(J) < ∞`, then `χ(J') = [J:J'] χ(J) >= [J:J']`, and a fibred `J'` has
    free Alexander `H_2` of rank `ρ_2 >= ρ_1 + [J:J']`.
  - *Obstruction.* Along descent, `μ` and every zero-divisor infimum are non-decreasing. For
    `i >= 1`, `cd = 2`, `b_1 = 0` and `χ >= 1` at every step. So termination in type (I) needs a
    Hirsch-length-type invariant. Restricting a minimal pair to finite index gives only
    coset-matrix zero divisors.
  - *Calibrations.* `D_∞`: finite index can kill all element zero divisors. Hantzsche–Wendt: a
    non-locally-indicable group with no type (I) subgroup, whose descent exits through a
    locally indicable fibre; that exit is closed in cd 2.
  - *Next step.* Exclude fibred finite-index subgroups of a minimal-pair group `J`, using the
    linear growth of their Alexander `H_2`. Alternatively, build a strictly decreasing invariant.
