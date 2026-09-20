---
rg: 2
id: f2-z4-embeds-in-z2-sft-boundary-product-hosts
kind: claim
title: For some free minimal Z^2-SFT Ω over F_2 with finitely presented B_Ω and some d ≥ 2, the Laurent ring F_2[Z^4] embeds unitally in B_Ω ⊗ L_∂
distinct_from:
  decidable-algebras-embed-in-z2-sft-boundary-product-hosts: that asks for every decidable group, and implies this claim because Z^4 is decidable. This is the single test input Z^4, where the monomial route is already dead, so a NO answer here refutes that claim.
  z4-has-no-monomial-embedding-in-boundary-product-hosts: that rules out embeddings through bisection units, and is ESTABLISHED. This asks about arbitrary, non-monomial algebra embeddings.
---

**OPEN.** There are:
- a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω = LC(Ω, F_2) ⋊ Z^2` finitely presented;
- some `d >= 2`;
- a unital injective algebra map `F_2[x_1^(±1), …, x_4^(±1)] → B_Ω ⊗ L_∂`, where
  `L_∂ = LC(∂F_d, F_2) ⋊ F_d`.

A non-unital embedding into a corner is enough, by the unital extension `φ + ε(·)(1 − e)`.

**Why it matters.** This is a necessary condition for (E) (`decidable-algebras-embed-in-z2-sft-boundary-product-hosts`),
tested on the smallest input that `z4-has-no-monomial-embedding-in-boundary-product-hosts` puts out of reach
of every full-group embedding. The two answers have these consequences:
- YES: it names the non-monomial mechanism that (E) must use.
- NO: it refutes (E), and with it the route `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`
  as stated.

## Decomposition

**A sufficient condition for YES.** The host contains `F_2[Z^2] ⊗ L_∂` through the canonical units of `Z^2`.
So it suffices that some corner `e L_∂ e` of the Kirchberg-type Steinberg algebra `L_∂` contains a Laurent
ring in two commuting variables. The same holds with `L_∂` replaced by any algebra that embeds in a corner of
the host.

**A heuristic for NO (the commutative-rank conjecture).** Let `𝒢` be an ample Hausdorff groupoid with a
continuous cocycle `𝒢 → Z^s` whose kernel is an AF groupoid. Conjecture: then `S(𝒢)` contains no Laurent
ring, and indeed no commutative domain, of transcendence degree `s + 1`.
- For the host, the degree cocycles of `B_Ω` (valued in `Z^2`, with trivial kernel) and of
  `L_∂ ≅ L(E_d)` (valued in `Z`, with AF core) give `s = 3`. So the conjecture would give NO.
- Evidence: for the odometer, `LC(Z_2) ⋊ Z` is a directed union of the algebras `M_(2^k)(F[t^(±1)])`,
  whose commutative subalgebras have transcendence degree at most 1.
- The conjecture is consistent with `L_2 ⊗ L_2` not embedding in `L_2`. Brownlowe–Sørensen
  (arXiv:1603.03618) prove the unital `*`-version over `Z`.
- *Caveat:* the naive graded form is false. `F[x, y]` graded by `deg x = 1, deg y = 2` has
  degree-0 part `F`. So any proof must use the bisection structure, meaning that each homogeneous
  component is locally a rank-one module over the core, and not only the grading.

## Attempts

1. **Monomial embeddings: dead** (swarm-0917-w12-w12-bh-pull, 2026-09-18). By
   `z4-has-no-monomial-embedding-in-boundary-product-hosts`, the embedding is not monomial, even up to
   conjugacy and matrix amplification.
   - Invariant: the ball separation of the germ orbit.
   - Where it dies: at the tree-centroid slab of size `O(k^2)`, set against the `Θ(k^3)` cut of
     `[k]^4`.
2. **Literature (same lane).** No source was found that decides whether a Leavitt path algebra of a
   finite graph contains a Laurent ring in two variables.
   - Bilich–Hazrat–Nam (arXiv:2512.09241) embed condition-(L) LPAs into `L_K(1, 2)`, and show that
     Steinberg algebras omit the Weyl relation.
   - That does not bear on group algebras: `F_2[G]` has a trace, so it contains no Weyl pair.
3. **Mechanism (ii) is dead; the principal case of the conjecture holds** (swarm-0917-w14-w14-bh-follow,
   2026-09-19). See `ore-domains-in-free-crossed-products-grow-like-the-group`.
   - **Result.** In a principal ample groupoid algebra with compact unit space, an Ore domain `C` has a
     unit `e_x` of the orbit module on which `c ↦ c·e_x` is injective. So `dim C_(≤n)` is at most the
     size of one source fibre of `K^n`.
   - **Consequences for this claim.**
     - `B_Ω`, its corners and its matrix algebras contain no `F[Z^3]`, over any field and for every free
       `Z^2` Cantor system, not only SFTs. So route (ii) of (E) is closed.
     - This proves the commutative-rank heuristic above in the case where the cocycle kernel is trivial
       and the groupoid is principal, with `s` the growth degree.
   - **Constraint on YES.** An embedding `F_2[Z^4] → B_Ω ⊗ L_∂` needs the `L_∂`-values of its coefficient
     functions to generate an algebra of GKdim at least 2. Coefficients from `LC(∂F_d)`, `F[u^±]` or
     `M_n(F[u^±])` fail. So YES must come from mechanism (i), a two-variable Laurent ring in a Leavitt
     corner, or from (iii), an entangled embedding with genuinely noncommutative Leavitt coefficients.
   - **Invariant:** the growth of one source fibre of an annihilator-free unit of the orbit module.
   - **Where it dies:** the groupoid of `L_∂` is not principal, because it has isotropy at eventually
     periodic boundary points. So the orbit module is not faithful on its Steinberg algebra, and the
     fibres of `K^n` grow exponentially. The AF-kernel case of the conjecture is therefore genuine
     Leavitt content, and is not reached by this count.
3. **Gauge-homogeneous embeddings: dead** (swarm-0917-w14-w14-bh-follow, 2026-09-19). By
   `finite-field-polynomial-growth-hosts-bound-commuting-rank`, the argument works over every finite field
   and for every `Z^2`-Cantor system `Ω`.
   - Statement: in any embedding, the elements of `Z^4` sent to gauge-homogeneous units form a subgroup
     of rank `<= 3`.
   - Invariant: the gauge-degree-0 sublattice, of rank `>= 3`, lands in `B_Ω ⊗ L(E_d)_0`. That algebra
     is a directed union of subalgebras of `M_N(B_Ω)` acting on `Z^2 × [N]` with bounded propagation.
   - Where it dies: count dimensions. `binom(K+3, 3)` is larger than `N(2bK + 1)^2`, so each basis
     vector has a nonzero annihilator of degree `<= K`. The product of all nonzero polynomials of
     degree `<= K`, of which there are finitely many over `F_2`, then kills `φ` on a nonzero element.
   - What survives: a YES construction needs gauge-inhomogeneous units.
   - The symmetric case does not close. Units homogeneous in the `B_Ω`-lattice degree put a rank-`>= 2`
     sublattice into `LC(Ω) ⊗ L_∂`, which is locally `M_N(L(1,2))`. That is exactly mechanism (i), which
     is `leavitt-commuting-units-are-algebraically-dependent`.
   - The counting fails on the tree column, where growth is exponential.
