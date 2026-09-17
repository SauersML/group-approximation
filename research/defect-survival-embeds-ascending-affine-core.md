---
rg: 2
id: defect-survival-embeds-ascending-affine-core
kind: claim
title: A surviving arithmetic defect embeds the whole ascending affine core, so no CAT(0) or hyperbolic group contains a routed output
distinct_from:
  torsion-free-router-forces-nonhyperbolic-output: that needs a Baumslag--Solitar relation on the routed word itself; the arithmetic defect w=[tct^-1,p_0] satisfies none, and here faithfulness on the non-finitely-generated core (Gamma(3) x| Z[1/m]^3) x| Z is forced by rational irreducibility plus torsion-freeness, which gives the CAT(0) exclusion as well.
  defect-forces-proper-self-embedding: that constrains which cores can carry a defect in the source; this constrains every torsion-free image in which the defect survives, and shows the core stays faithful there.
  a-t-menable-groups-have-no-rigid-compression-defect: that excludes a-T-menable ambients through rigid pairs; this excludes CAT(0)-cocompact and hyperbolic ambients through a forced non-finitely-generated abelian subgroup.
---

**ESTABLISHED (obstruction, host-geometry family).**

**Setting.** Let `n >= 2`, `m >= 2`, and let `Gamma <= SL_n(Z)` have no nonzero proper
`Gamma`-invariant subspace of `Q^n`. Put `P = Gamma ltimes Z^n`, `alpha(g,v) = (g, m v)`, `V_m = Z[1/m]^n`, and

```text
L_m = (Gamma ltimes V_m) x| <tau>,     tau (g,v) tau^-1 = (g, m v).
```

`L_m` is the ascending HNN extension `<P, t | t p t^-1 = alpha(p)>`, with `t -> tau`.

**Theorem.** Let `G` be torsion-free, `iota : P -> G` a homomorphism and `s in G` with
`s iota(p) s^-1 = iota(alpha(p))` for all `p`. Let `psi : L_m -> G` be the induced map.

- **(A)** If `iota(Z^n) != 1`, then `psi` is injective.
- **(B)** Let `c in G` commute with `iota(P)`, and suppose `[s c s^-1, iota(v_0)] != 1` for
  some `v_0 in Z^n`. Then `iota(Z^n) != 1`, so (A) applies, and
  `((g,v), k) -> iota(g,v) c^k` is an injective homomorphism `P x Z -> G`.

**Corollary (the arithmetic router).** Take `n = 3`, `Gamma = Gamma(3)`, the source `R` of
`sofic-preserving-single-defect-kazhdan-router`, and `sigma = w = [t c t^-1, p_0]`,
`p_0 = (1, e_1)`. For every torsion-free quotient `q : R ->> Q` with `q(w) != 1`, in
particular for every output of `(SPR1)` and of `(ADS1)`:

1. `q` is injective on `L_m`, which contains `BS(1,m) = <e_1, tau>` and the
   non-finitely-generated abelian group `Z[1/m]^3`, and on `B = P x <c>`. The artifact's
   remark "`iota` need not be injective" is therefore vacuous: nontrivial torsion-free outputs are always faithful on the core.
2. `Q` is not a subgroup of any group acting properly and cocompactly by isometries on a CAT(0)
   space (`cat0-group-solvable-subgroups-are-virtually-abelian`: the solvable subgroup `Z[1/m]^3` would be finitely generated).
   This rules out Titz--Witzel and Caprace--Remy Kac--Moody lattices, cocompact lattices in
   rank-one and higher-rank groups, and cocompactly cubulated groups, whether they have torsion or not.
3. `Q` is not a subgroup of a word-hyperbolic group (Fact H of
   `torsion-free-router-forces-nonhyperbolic-output`, applied to `BS(1,m) <= Q`).

**Kill.** Consider any host-geometry approach that gets soficity or approximation data for the output, or for a
torsion-free intermediate quotient in which the defect survives, by *embedding* it into a
CAT(0)-cocompact or hyperbolic group. Every such approach dies at the survival step: `q(w) != 1`
forces `Z[1/m]^3 <= Q`. The invariant is the forced non-finitely-generated solvable subgroup. In
particular, the arithmetic route and the Titz--Witzel route cannot be merged by realizing
the routed arithmetic quotient inside a Titz--Witzel lattice or its kernel.

**Scope.** The theorem says nothing about soficity of `Q` itself. `L_m` and `P x Z` are
linear and residually finite.

DERIVATION
[[defect-survival-embeds-ascending-affine-core-proof]]
