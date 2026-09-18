---
rg: 2
id: profinitely-closed-linear-coefficients-rank-condition
kind: claim
title: A skew group ring over the fraction field of the symmetric algebra of a module that is residually finite along finite quotients has the rank condition, with no soficity, so generalized Bernoulli fields over separable coset spaces such as primitive vectors under SL_3(Z) give no rank failure
distinct_from:
  finite-field-point-models-give-the-rank-condition: its part (B1) builds random point models for free Bernoulli fields along sofic approximations; this builds exact periodic point models on coinvariants of finite quotients, which reaches non-free coefficient modules such as permutation modules on coset spaces and needs no soficity of the group.
  birational-skew-group-rings-have-the-rank-condition: that needs finitely generated orbit fields and counts points by Lang-Weil; here the orbit fields have infinite transcendence degree and the count is Schwartz-Zippel on a linear space of periodic points.
  virtually-biorderable-crossed-products-rank-condition: that restricts the group and allows any cocycle; this allows any group, including SL_3(Z), with trivial cocycle and linear coefficients.
---

Let `G` be a group and `R` either `Z` or a finite field `F_q`. Let `M` be a finitely generated `R[G]`-module that
is free as an `R`-module (automatic for `R = F_q`). Put `A = Sym_R(M)`, a polynomial ring on an `R`-basis of `M`
on which `G` acts, and `K = Frac A`. So `K` is the purely transcendental field `F_q(M)`, or `Q(M ⊗ Q)` for
`R = Z`. Let `K ⋊ G` be the skew group ring (`α = 1`).

**Definition.** For a prime `p` (`p = char F_q` when `R = F_q`), `M` is **residually finite mod `p`** if every
finite subset of `M` lies in a finitely generated `R`-submodule `W` for which some finite-index normal subgroup
`N ⊴ G` makes `W/pW -> (M/pM)_N` injective. Here `(-)_N` denotes coinvariants.

**ESTABLISHED 2026-09-17** by [[profinitely-closed-linear-coefficients-rank-condition-proof]].

**Theorem.**
1. **(Point models.)** Suppose `R = F_q` and `M` is residually finite mod `p`, or `R = Z` and `M` is residually
   finite mod `p` for infinitely many primes `p`. Then `K` has finite-field point models over `G` in the sense of
   `finite-field-point-models-give-the-rank-condition`, with an exact action of the finite group `G/N`.
2. **(Rank condition.)** Then `K ⋊ G` has the rank condition, and so does `F ⋊ G` for every `G`-stable subfield
   `F ⊆ K`. Examples of such subfields are `Frac Sym_R(M')` for submodules `M' ⊆ M`. The conclusion also holds for
   directed unions of such fields.
3. **(Closure criterion.)** For `R = F_q` and `M = F_q[G]^n / J`, `M` is residually finite mod `p` if and only if
   `J` is closed in the profinite topology, that is `J = ∩_N (J + ker(F_q[G]^n -> F_q[G/N]^n))`.

**Examples covered.**
- **Permutation modules.** `M = R[G/L]` for a separable subgroup `L` (an intersection of finite-index subgroups),
  for every prime `p`. The field `K = k(x_c : c ∈ G/L)` with `g·x_c = x_(gc)`, over `k = Q` or `F_q`, is a
  generalized Bernoulli field.
- **Bernoulli fields over residually finite groups.** `L = 1`, with finite or infinite index sets through finite
  direct sums and directed unions. No sofic approximation is used.
- **Primitive vectors.** `G = SL_3(Z)` and `L` the stabilizer of `e_1`, so `G/L` is the set of primitive vectors of
  `Z^3` and `K = Q(x_v : v ∈ Z^3 primitive)`. `L = ∩_m Γ(m)L` because `Γ(m)L` fixes `e_1` modulo `m`.
- **Finite direct sums** of modules that are residually finite mod `p` for all but finitely many `p`.
- **Finite-rank lattices** `M ≅ Z^n` with any action (for all `p`, via `N = ker(G -> GL_n(F_p))`). This is
  consistent with `birational-skew-group-rings-have-the-rank-condition`.

**Consequences for `some-field-crossed-product-fails-the-rank-condition`.**
- `virtually-biorderable-crossed-products-rank-condition` leaves groups like `SL_3(Z)` alive. Over `SL_3(Z)`, and
  over every group, no skew group ring with linear coefficients from a residually finite module is a witness.
  This includes Bernoulli fields, generalized Bernoulli fields on separable coset spaces, and all their `G`-stable
  subfields.
- **Exact failing step for a linear-coefficient witness with `α = 1`.** The coefficients must not lie in any
  `G`-stable subfield of `Frac Sym_R(M)` for a residually finite `M`. In particular a coefficient field
  `F_q(F_q[G]^n / J)` needs `J` not closed in the profinite topology. Some finite window of the module must then
  collapse in every finite quotient `G/N`. For `R = Z` this must happen modulo almost every prime.
- **Surviving regimes.**
  - Non-closed relation modules, for example over groups with few finite quotients.
  - Nonlinear coefficient primes, such as function fields of algebraic subshifts cut out by nonlinear equations.
  - Nontrivial cocycles, such as the ternary Leavitt route.
- **Profile consequence.** Via `twisted-linear-profile-deficits-are-rank-condition-failures`, skew group rings over
  profinitely closed linear coefficient fields give no twisted linear profile with `Phi -> 0`.

**Scope.** Only the rank condition is proved, not stable finiteness. The theorem uses `α = 1`, linear
coefficients, and exact finite quotients through which a finite window of `M` injects.

**Calibration.** The Steinberg algebra `LC(X,k) ⋊ F_2` of a paradoxical action fails the rank condition, and its
coefficient ring is Boolean, not a symmetric algebra.
- Points of a Boolean ring take values `0` and `1`, so a nonzero indicator vanishes on a fixed positive fraction of
  points however large `F_Q` is.
- The step that fails there is the Schwartz–Zippel bound `D/Q` on zeros, which is exactly where the linear
  structure of `Sym(M)` is used.
