---
rg: 2
id: finite-subgroup-rank-data-cannot-force-two-root-identity
kind: claim
title: Rank data of a model on finite subgroups, with all conjugacies, is consistent with free behaviour, so it cannot force N_23 N_12 = 0
distinct_from:
  dyadic-root-displacement-data-admit-trivial-plus-free-models: that realizes displacement data on the dyadic root group by actual models; this assigns the free profile to every finite subgroup of the whole group, compatibly with every conjugacy, and concludes that a proof of the root identity must use the model on an infinite subgroup.
  fd-represented-coefficients-violate-two-root-identities: that covers group relations over finitely represented coefficient subrings; this covers relations with arbitrary coefficients, unital Leavitt families included, provided each relation lives in a finite subgroup.
  leavitt-isometry-commutators-constrain-el3-rank-models: that records the operator identities from [x_12(t_i), x_23(s_j)] = x_13(delta_ij); this shows every such identity holds inside a finite subgroup, so no combination of them with conjugacy and per-subgroup ranks can force the root identity.
  rank-modelled-coefficients-violate-two-root-identities: that builds genuine natural-tensor-natural rank models of EL_3 over any coefficient ring with a rank model; this is a per-finite-subgroup profile over the Leavitt unit group itself, compatible with conjugation by all of it, which no actual model is claimed to realize.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Let `G` be any group containing `D = <h, g>`, a dihedral group of order `8` with `h`, `g`
involutions and `hg` of order `4`. For example `G = EL_3(L_(F_2)(1,2))` with `g = x_12(1)` and
`h = x_23(1)`. For every finite subgroup `K` of `G` define the free profile

```text
r_K(alpha) = rank( lambda_K(alpha) ) / |K|,    alpha in F_2[K],
```

where `lambda_K` is left multiplication on `F_2[K]`. Then:

1. **Realizable.** Each `r_K` is the rank function of a homomorphism `F_2[K] -> M` into a rank
   ultraproduct over `F_2`: the regular representation, in the constant ultraproduct.
2. **Restriction.** `r_L` restricted to `F_2[K]` equals `r_K` for finite `K <= L`.
3. **Conjugation.** `r_(xKx^-1)(x alpha x^-1) = r_K(alpha)` for every `x` in `G`, and more
   generally for every isomorphism between finite subgroups.
4. **Value.** `r_D((h - 1)(g - 1)) = 3/8`.

**Consequence.** Take any argument that proves `N_23 N_12 = 0` for rank models `sigma` of `G`
using only:
- relations holding inside finite subgroups;
- conjugacy between finite subgroups by elements of `G`;
- inclusions among finite subgroups;
- the rank data of `sigma` on each finite subgroup separately.

The free profile satisfies all of that and violates the conclusion, so no such argument exists.

For `G = EL_3(L_(F_2)(1,2))` in characteristic two, the following therefore cannot force the
identity:
- every Steinberg relation, whatever its coefficients, since `<x_ij(a), x_jk(b)>` is finite;
- the isometry commutator identities of `leavitt-isometry-commutators-constrain-el3-rank-models`;
- the splitting `x_12(1) = x_12(e_0) x_12(e_1)`;
- conjugacy by Leavitt and Thompson units, including
  `shifted-root-pair-conjugates-to-idempotent-root-pair`;
- involution-class and displacement counting on level groups.

A proof of `rank-models-of-el3-satisfy-the-two-root-identities` must use the model on a subgroup
of `G` that is not contained in any finite subgroup. Example:
`<diag(u, u^-1, 1), x_12(1)>` with `u` a unit of infinite order, which contains `x_12(u^(2k))`
for all `k`. Or it must use joint rank inequalities between elements of finite subgroups that
together generate an infinite subgroup.

Proof: `research/artifacts/el3-two-root-identities-2026-09-12.md`, Section 6.3.
