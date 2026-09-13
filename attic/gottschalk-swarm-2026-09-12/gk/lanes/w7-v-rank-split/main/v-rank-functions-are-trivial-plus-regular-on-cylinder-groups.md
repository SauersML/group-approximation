---
rg: 2
id: v-rank-functions-are-trivial-plus-regular-on-cylinder-groups
kind: claim
title: Every rank function on a group algebra of Thompson's V is trivial plus regular on each finite cylinder group, in every characteristic
distinct_from:
  v-rank-models-are-trivial-plus-free-on-odd-cycle-trees: that is the torsion law on elementary abelian odd-cycle groups whose order is prime to the characteristic; this covers every finite cylinder group in every characteristic, and uses that law only on an auxiliary odd-cycle group.
  v-rank-order-char-cycles-are-trivial-plus-regular: that is the Jordan profile of one clopen p-cycle in characteristic p; this is the whole rank function on every finite cylinder group, and gives that profile as a corollary.
artifacts:
  - research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md
---

**OPEN.** The candidate proof is Section 1 of the artifact. It is held open until `w3-vf-linear` re-derives it.

**Setting.**
- `F` is any field, `rk` a Sylvester matrix rank function on `F[V]`, and `phi_V = 1 - rk col(1 - [s] : s in S)` for
  a finite generating set `S`.
- A *cylinder group* is a finite `G <= V` with a finite partition `Pi` of `X` into cylinders such that every
  `g in G` maps each cylinder of `Pi` onto a cylinder of `Pi` by prefix replacement.
- For `A in M_n(F[G])`, `eps(A)` is the augmentation and `Reg(A) in M_(n|G|)(F)` is left multiplication by `A` on
  `F[G]^n`.

**Claim.** For every cylinder group `G` and every `A in M_n(F[G])`,

```text
rk(A) = phi_V rank_F eps(A) + (1 - phi_V) rank_F Reg(A) / |G|.
```

**Scope.** By `finite-subgroups-of-thompson-v-permute-a-canonical-partition` (ESTABLISHED), every finite subgroup of
`V` is a cylinder group. So the claim covers every finite subgroup of `V`.

**Consequences** (artifact Sections 0 and 4).
- **The order-characteristic law, for every prime.** A clopen `p`-cycle `s` in characteristic `p` has
  `rk((1 - [s])^j) = (1 - phi_V)(p - j)/p` for `1 <= j <= p`. This is
  `v-rank-order-char-cycles-are-trivial-plus-regular`, including `p = 2`, where `rk(1 + [t]) = (1 - phi_V)/2`,
  and `p = 3`.
- **Torsion is fully spent.**
  - `phi_V` alone pins a rank function on every finite cylinder group, and so on every locally finite union of them.
  - Those values are sofic permutation-module ranks mixed with the augmentation rank. So by
    `sofic-configurations-cannot-force-v-rank-triviality`, no argument confined to them can force a gate.
- **What it doesn't do.** It decides neither `thompson-v-has-no-nontrivial-f2-rank-model` nor
  `thompson-v-ternary-rank-functions-are-augmentation`.

## Attempts

- **Candidate proof** (w7-v-cycle-c2, artifact Section 1).
  - **Auxiliary group.** Build `Q = (Z/p)^Pi` from one clopen `p`-cycle inside each cylinder, for an odd prime
    `p != char F`, transported by `G`. `G` normalizes `Q` and permutes its coordinates, and `Q` is a clopen-cycle
    subgroup.
  - **Torsion input.** The torsion law and `v-rank-torsion-constant-equals-global-fixed-rank` give
    `rk(e_chi) = phi_V [chi = 1] + (1 - phi_V) p^(-|Pi|)` after scalar extension.
  - **Trivial character.** `rk col(e_Q(1 - [g])) <= rk(e_Q) - phi_V`, so on that block `G` acts trivially up to
    rank `n(1 - phi_V) p^(-|Pi|)`.
  - **Free orbits of characters.** The equivalence `f_O ~ I_|G| ⊗ e_chi` turns `f_O A` into `Reg(A) ⊗ e_chi`.
  - **Counting.** At most `(|G| - 1) p^(|Pi| - 1)` characters are not free. The total error is at most `4n|G|/p`;
    let `p -> infinity`.
  - **Where it stops.** The proof is complete on paper and held OPEN pending re-derivation. After a PASS:
    - route `v-rank-trivial-plus-regular-on-cylinder-groups-proof` for this claim, requiring
      `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees` and `v-rank-torsion-constant-equals-global-fixed-rank`;
    - route `v-rank-order-char-cycle-law-proof` for the law node, requiring this claim.
- **Cross-check in characteristic two** (artifact Section 2). This uses dihedral configurations `<c, t>` with
  `t c t = c^(-1)`, `c` a clopen `p`-cycle, and `e = sum_i [c]^i`. The identity
  `1 - e = u(1 + [t]) + (1 + [t]) u'`, with `u = sum_(i=1)^((p-1)/2) [c]^i` and `u' = [t] u [t]`, gives
  `(1 - phi_V)(p - 1)/(2p) <= rk(1 + [t]) <= (1 - phi_V)(p + 1)/(2p)`. No characters are needed.
- **The 2-group alone can't do it** (artifact Section 3).
  - **Construction.** Take `K = F_2(lambda_1, lambda_2, ...)` purely transcendental and embed
    `E_infinity -> (K, +) <= GL_2(K)`.
  - **What it satisfies.** The resulting rank function on `F_2[E_infinity]` is invariant under every
    disjoint-support endomorphism, and `rk(1 + [g]) = 1/2` for every `g != 1`.
  - **Where it breaks the law.** Its fixed rank is `1/2` at every level, so it is not trivial plus regular. A proof
    has to use odd cycles normalized by the 2-group.
