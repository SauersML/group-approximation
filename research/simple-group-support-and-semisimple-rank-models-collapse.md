---
rg: 2
id: simple-group-support-and-semisimple-rank-models-collapse
kind: claim
title: For finitely presented simple groups, weak models with support lengths are sofic models and weak models with rank lengths are linear sofic models
distinct_from:
  thompson-v-not-sofic: that uses simplicity to reduce soficity of V to one word moving a fixed proportion of points in normalized Hamming models; this treats un-normalized lengths (any monotone subadditive function of support, or of rank in a semisimple representation) for every finitely presented simple group, and shows they collapse to the normalized ones.
  hamming-transports-of-weak-sofic-models-are-soficity: that shows uniform normalized Hamming transports of arbitrary weakly sofic models give soficity, for every group; this concerns models whose own length is a support or rank function, without normalization, and uses simplicity to normalize on the moved part.
  glebsky-fin-case-instantiation: that explains why weak soficity of a general group needs Glebsky's generic capped conjugation word length; this proves that for simple groups the natural local lengths add nothing beyond soficity and linear soficity.
  weak-soficity-survives-every-corpus-obstruction: that lists mechanisms realized inside weakly sofic groups; this is a positive collapse theorem for one class of lengths on simple groups.
---

**ESTABLISHED.** Let `G = <X | R>` be an infinite finitely presented simple
group and `g_0 != 1` in `G`. A *weak model with parameter `eps`* in a finite
group `H` with a conjugation-invariant pseudo-length `l` is a tuple
`a in H^X` with `l(r(a)) <= eps` for `r in R` and `l(g_0(a)) >= 1`. Because
`G` is simple, `G` is weakly sofic iff such models exist for every `eps > 0`
(a nontrivial homomorphism into a metric ultraproduct is injective).

Let `f : {0,1,2,...} -> [0, infinity)` be nondecreasing and subadditive with
`f(0) = 0`.

- **(P) Support type.** `l(h) = f(|supp_Omega(h)|)` for a finite `H`-set `Omega`.
- **(L) Rank type.** `l(h) = f(rk(rho(h) - 1))` for a representation
  `rho : H -> GL(V)` over a field `F`, in any characteristic. (The first version of
  this node required `char F` not dividing `|H|`; the moved-quotient argument of the
  proof removes that hypothesis. The id keeps the old word.)

`H`, `Omega`, `rho`, `V` and `f` may change from model to model. In (L) the field
`F` is fixed.

**Theorem.**
1. `G` has weak models of support type for every `eps` iff `G` is sofic.
2. If `G` has weak models of rank type over `F` for every `eps`, then `G` is
   `F`-linear sofic. For a finite field `F` the converse holds, so rank-type weak
   soficity over `F_q` is `F_q`-linear soficity.
3. Quantitatively: if `G` is not sofic, there is `eps_0 = eps_0(G, X, R) > 0`
   such that every tuple of permutations `a` of a finite set satisfies
   `max_(r in R) |supp r(a)| >= eps_0 |supp <a>|`, and no support-type model has
   `eps < 1/ceil(1/eps_0)`. If `G` is not `F`-linear sofic, there is `delta_0 > 0`
   such that every tuple `a in GL(V)^X` over `F` satisfies
   `max_r rk(r(a) - 1) >= delta_0 max_x rk(a_x - 1)`.
4. **Projective form.** With `rho(g) = min_(lambda in F) rk(g - lambda)`, the rank
   distance to the scalars, the same hypothesis gives
   `max_r rho(r(a)) >= (delta_0 / 2) min(max_x rho(a_x), n/2)` for every tuple in `GL_n(F)`.
   This is item 3 applied to the adjoint tuple on `End(V)`, using
   `n min(rho(g), n/2) <= rk(Ad(g) - 1) <= 2 n rho(g)`. The cap `n/2` accounts for eigenvalues
   outside `F`. No hypothesis on the Schur multiplier is needed.

**The mechanism.**
- In a permutation tuple the moved set of the whole group is the union of the
  generators' supports.
- In a linear tuple the moved quotient `V/U`, with `U` the common fixed space, has
  dimension at most the sum of the generators' ranks.
- Normalizing on the moved part turns an un-normalized model into a normalized one.
- In the linear case one alternative remains: every generator acts almost trivially
  on `V/U` and all rank sits in the corner `Hom(V/U, U)`. There the tuple is
  almost abelian, and perfection of `G` bounds each generator's rank by a fixed
  multiple of the relator ranks.
- Otherwise some generator keeps normalized rank bounded below on `V/U`, and simplicity
  makes the ultraproduct homomorphism injective.

**Consequences.**
- The binary Leavitt unit group `R^x` (finitely presented, simple, nonsofic:
  `leavitt-unit-group-is-simple-fa-nonsofic`) has no weak models of support
  type. Un-normalized Hamming models, logarithmic or square-root support
  lengths, and truncations `min(1, |supp|/m)` with `m` far below the model size
  are all excluded.
- `R^x` has weak models of rank type over `F_q` iff it is `F_q`-linear sofic. So
  truncated-rank weak soficity of `R^x` over `F_2` is the Gottschalk gate
  `binary-leavitt-unit-group-is-f2-linear-sofic`, and
  `leavitt-el3-rank-models-over-finite-fields-are-trivial` would kill it in every
  characteristic `p` model.
- For Thompson's group `V`, support-type weak soficity is equivalent to
  soficity, so it is `thompson-v-is-sofic` itself.
- So for a simple group, weak soficity beyond soficity and linear soficity must
  come from lengths that no single permutation action or linear representation
  determines. An example is Glebsky's capped conjugation word length on finite
  groups with large normal subgroups.

**Scope limits.**
- Finite sums or maxima of boundedly many support-type or rank-type lengths
  reduce to (P) or (L).
- Non-simple groups are not covered. The homomorphism on the moved part may have
  a kernel.

Derivation: `simple-group-support-and-semisimple-rank-models-collapse-proof`.
