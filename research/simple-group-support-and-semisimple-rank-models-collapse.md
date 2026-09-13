---
rg: 2
id: simple-group-support-and-semisimple-rank-models-collapse
kind: claim
title: For finitely presented simple groups, weak models with support lengths are sofic models and weak models with semisimple rank lengths are linear sofic models
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
- **(L) Semisimple rank type.** `l(h) = f(rk(rho(h) - 1))` for a representation
  `rho : H -> GL(V)` over a field `F` whose characteristic does not divide `|H|`
  (for example `F = C`).

`H`, `Omega`, `rho`, `V` and `f` may change from model to model. In (L) the field
`F` is fixed.

**Theorem.**
1. `G` has weak models of support type for every `eps` iff `G` is sofic.
2. If `G` has weak models of semisimple rank type over `F` for every `eps`,
   then `G` is `F`-linear sofic.
3. Quantitatively: if `G` is not sofic, there is `eps_0 = eps_0(G, X, R) > 0`
   such that every tuple of permutations `a` of a finite set satisfies
   `max_(r in R) |supp r(a)| >= eps_0 |supp <a>|`, and no support-type model has
   `eps < 1/ceil(1/eps_0)`. The same holds with ranks in semisimple
   representations if `G` is not `F`-linear sofic.

**The mechanism.** In a permutation tuple the moved set of the whole group is the
union of the generators' supports. In a semisimple representation the moved
subspace `[P, V]` is the sum of the generators' images of `rho(h) - 1`, and it
carries all the rank. Normalizing the length on that moved part turns a
un-normalized model into a normalized one in which some generator stays at
distance `1/|X|`. Simplicity makes the resulting homomorphism injective.

**Consequences.**
- The binary Leavitt unit group `R^x` (finitely presented, simple, nonsofic:
  `leavitt-unit-group-is-simple-fa-nonsofic`) has no weak models of support
  type. Un-normalized Hamming models, logarithmic or square-root support
  lengths, and truncations `min(1, |supp|/m)` with `m` far below the model size
  are all excluded.
- Any semisimple rank weak model of `R^x` over `C` would make `R^x` `C`-linear
  sofic.
- For Thompson's group `V`, support-type weak soficity is equivalent to
  soficity, so it is `thompson-v-is-sofic` itself.
- So for a simple group, weak soficity beyond soficity (resp. beyond
  linear soficity in coprime characteristic) must come from lengths that no
  single permutation action or semisimple representation determines. Examples
  are Glebsky's capped conjugation word lengths on groups with large normal
  subgroups, and ranks in the defining characteristic, where unipotent blocks
  carry rank off the moved part.

**Scope limits.**
- Finite sums or maxima of boundedly many support-type lengths reduce to (P).
- Truncated ranks on `GL_n(F_q)` in the defining characteristic are not covered.
  The block `[[1, N], [0, 1]]` has rank `rk N` while acting trivially on every
  semisimple subquotient.
- Non-simple groups are not covered. The homomorphism on the moved part may have
  a kernel.

Derivation: `simple-group-support-and-semisimple-rank-models-collapse-proof`.
