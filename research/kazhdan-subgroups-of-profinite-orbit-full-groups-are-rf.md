---
rg: 2
id: kazhdan-subgroups-of-profinite-orbit-full-groups-are-rf
kind: claim
title: Every Kazhdan subgroup of the full group of an ergodic profinite action of any countable group is residually finite, so profinite orbit hosts never certify a full-radical Kazhdan kernel
distinct_from:
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that needs an amenable acting group and finite-range cocycles, and concludes finite orbits through hyperfiniteness; this allows every countable acting group, Kazhdan ones included, and countable-range cocycles. Orbits stay infinite here (the acting group sits in its own full group), and residual finiteness comes from finite permutation actions on clusters of a Kazhdan-invariant near-copy of the same-atom relation.
  irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups: that needs a Haagerup acting group, a free action and IRS rigidity of the Kazhdan group; this needs a profinite action and no hypothesis on either group beyond property (T) of the subgroup.
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that is Kirchberg--Valette for U(R); the von Neumann algebra of a profinite action of a non-amenable group is not hyperfinite, so that theorem does not apply, and the proof here is measure-theoretic.
  ioana-profinite-cocycle-superrigidity: Ioana untwists cocycles of a Kazhdan group whose own action is profinite; here the Kazhdan group acts through the full group of someone else's profinite action and need not preserve any finite partition, and no untwisting or rigidity theorem is used.
  kazhdan-profinite-untwisting-is-virtual-splitting: that untwists scalar 2-cocycles over a profinite action of the Kazhdan group itself; this concerns Kazhdan subgroups of the orbit full group of a profinite action of another group.
---

**ESTABLISHED** by `kazhdan-subgroups-profinite-orbit-full-groups-rf-proof`. It is unreviewed, and the
proof is self-contained: it imports no theorem beyond the definition of property (T) and martingale
convergence.

**Setting.**
- `H` is any countable group.
- `X_1 <- X_2 <- ...` is a tower of finite transitive `H`-sets with equivariant surjections, and
  `n_i = |X_i|`.
- `X = lim X_i` is the inverse limit, with maps `p_i : X -> X_i` and the inverse-limit `mu` of the
  uniform measures. This is the general ergodic profinite p.m.p. action.
- `[R_H]` is the full group: measure-preserving Borel bijections `g` of `X`, modulo null sets, with
  `g x in H x` for a.e. `x`.
- No freeness is assumed, and no finite-range condition on cocycles.

**Theorem.** Let `K` be a countable group with property (T) and `rho : K -> [R_H]` a homomorphism.
Then `rho(K)` is residually finite. In particular every Kazhdan subgroup of `[R_H]` is residually
finite.

**Consequences.**
1. **No profinite orbit host for a quotientless Kazhdan group.** If `K` has (T) and no nontrivial
   finite quotient, every homomorphism `K -> [R_H]` is trivial. This applies to:
   - every group satisfying (P1) of `automorphic-sofic-kazhdan-kernel-with-full-mf-radical`;
   - the (L1) kernels of `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`;
   - every infinite simple Kazhdan group, including the Pestov 9.1 group and the Titz Mite--Witzel
     kernels.
2. **Sharpness in the acting group.** The acting group `H` may itself have (T), for example
   `SL_3(Z)` on `SL_3(Z_p)`. Then `H` embeds in `[R_H]` with infinite orbits, so the finite-orbit
   conclusion of the amenable case fails, and residual finiteness is the correct conclusion.
3. **What is left of the orbit-full-group certificate for (P1).** The graph now kills three kinds of
   host for Kazhdan groups without finite quotients:
   - amenable acting groups (`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`);
   - Haagerup acting groups, provided the Kazhdan group is IRS-rigid
     (`irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups`);
   - profinite actions of arbitrary groups (this claim).

   The surviving hosts are non-profinite actions, such as Bernoulli shifts, of sofic acting groups
   that are neither amenable nor Haagerup. For these the certificate is circular unless the acting
   group's soficity is known independently.

**The invariant and where every member dies.** The invariant is the normalized indicator
`f_i = sqrt(n_i) 1_{Y_i}` of the same-atom relation `Y_i = {(x, y) : p_i(x) = p_i(y)}` in the
diagonal Koopman representation on `L^2(X x X)`. Each `g in [R_H]` is piecewise an element of `H`,
and `H` maps atoms to atoms. So `f_i` is almost invariant under any finite set as `i -> infinity`.

Property (T) turns this into an exactly `K`-invariant set `E` that is close to `Y_i` at scale
`1/n_i`. The fibre map `x -> E(x)` carries `mu` to a `K`-invariant measure on the measure algebra.
Its heavy points split into at most `2 n_i` clusters, which `K` permutes. That permutation action is
a genuine finite quotient, and it detects every `g` moving a set of measure much larger than the
approximation error. Every candidate host dies at this step: the finite cluster action.
