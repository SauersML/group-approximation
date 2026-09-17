---
rg: 2
id: hyperbolic-local-embedding-kills-compression-certificates
kind: claim
title: Groups locally embeddable into hyperbolic groups kill every compression defect and never contain two commuting non-LEF subgroups
distinct_from:
  hyperbolic-compression-centralizer-rigidity: that is the statement inside one genuine hyperbolic group for a non-elementary compressed subgroup; this is the statement for every group locally embeddable into hyperbolic groups (marked limits, lacunary hyperbolic groups, free Burnside groups), for every finitely generated compressed subgroup, elementary or not
  expander-matching-mechanism-has-no-hyperbolic-instance: that shows a Kazhdan subgroup of a hyperbolic group has finite commuting partners, so the witness does not embed; this shows the witness is not even a local limit of hyperbolic groups, with no property (T), because one of any two commuting finitely generated subgroups must be LEF
  sofic-groups-kill-rigid-compression-defects: that kills rigid defects in sofic groups and needs property (T) of the compressed and compressor groups; this kills all compression defects of finitely generated subgroups in local hyperbolic limits with no property (T)
  locally-residually-finite-targets-kill-compression-defects: that kills the defect in the image of a homomorphism to a locally residually finite group; this kills it inside the source group itself whenever the source is locally embeddable into hyperbolic groups, a class containing non-residually-finite groups such as free Burnside groups
  nonsofic-hyperbolic-group: that is the open target; this closes transfer of compression-certified nonsoficity into the hyperbolic class through any local-embedding step
---

**ESTABLISHED** through `hyperbolic-local-embedding-kills-compression-certificates-proof`.

## Definitions

A group `K` is **locally embeddable into hyperbolic groups (LEH)** if for
every finite `F subset K` there are a word-hyperbolic group `H` and an
injective map `psi : F -> H` with `psi(xy) = psi(x) psi(y)` whenever
`x, y, xy in F`. Every subgroup of a hyperbolic group is LEH. Every marked
limit of subgroups of hyperbolic groups is LEH; this includes lacunary
hyperbolic groups and the free Burnside groups `B(m,N)` of large odd exponent
(`free-burnside-is-a-limit-of-hyperbolic-groups`). The class is closed under
subgroups and under marked limits.

For `L <= K` let `P_K(L) = { u in K : u L u^-1 <= L }` and let

```text
D_K(L) = << [u c u^-1, l] : u in P_K(L), c in C_K(L), l in L >>_K
```

be the compression defect.

## Theorem R (compression rigidity)

Let `K` be LEH and let `Gamma <= K` be finitely generated. Every `u` in
`P_K(Gamma)` satisfies

```text
u C_K(Gamma) u^-1 = C_K(Gamma).
```

So the whole group `<P_K(Gamma)>` normalizes `C_K(Gamma)`, and
`[g z g^-1, gamma] = 1` for all `g in <P_K(Gamma)>`, `z in C_K(Gamma)` and
`gamma in Gamma`. In particular `D_K(Gamma) = 1`, and so is the rigid defect
of `sofic-groups-kill-rigid-compression-defects`. No property (T) is needed.

## Theorem B (commuting pairs)

Let `K` be LEH and let `A, B <= K` be finitely generated with `[A, B] = 1`.
Then `A` or `B` is LEF.

## Consequences

1. **No Thompson F.** No LEH group contains Thompson's group `F`. The
   group `F` contains `F x F`, it is finitely presented and not residually
   finite, hence not LEF. So `F`, `T`, `V`, `L_(F_2)(1,2)^x`, the
   eighteen-relator Steinberg group, and every group containing any of them
   are not LEH.
2. **Kun--Thom witnesses.** Every group whose nonsoficity is certified by a
   nontrivial rigid compression defect is not LEH. This covers the coset
   wreath of `kun-thom-wreath-carries-rigid-defect`, the free-lamp amalgams of
   `weak-mf-groups-can-carry-rigid-defects`, and the graph wreaths of
   `kt-lef-graph-wreaths-surjunctive-and-nonsofic`.
3. **Expander-matching witnesses.** Take a group with a Kazhdan subgroup
   `Gamma`, a commuting non-LEF `J`, and a compressor moving `J` into `Gamma`,
   as in `one-sided-compression-nonsofic-criterion`. It is not LEH. The reason
   is that `Gamma` contains a copy of `J`, so neither `Gamma` nor `J` is LEF.
   This includes the Fournier--Facio torsion-free group
   (`fournier-facio-torsion-free-skeleton`), where `J` is isomorphic to a
   finitely presented infinite simple group.
4. **Obstruction to transfer.** By `local-approximation-properties-are-marked-closed`, a
   nonsofic LEH group gives a nonsofic hyperbolic group
   (`nonsofic-hyperbolic-question-reduces-to-one-fixed-host`). A route that
   builds a nonsofic group from any compression-defect or commuting-factor
   certificate fails at one step: realizing that group as a local limit of
   hyperbolic groups. Examples of such realizations are small cancellation
   over a hyperbolic group, lacunary limits, periodic quotients, or embedding
   in a hyperbolic group. The approximating hyperbolic groups would have to
   carry a compression that moves a centralizer, which they cannot do.
   A nonsofic hyperbolic group, if one exists, needs a certificate that is not
   a compression defect and not a pair of commuting non-LEF subgroups.

**Calibration.** LEF groups are LEH, and for them Theorem R is the
identity-map case of `locally-residually-finite-targets-kill-compression-defects`.
`BS(1,2) = <a,t | t a t^-1 = a^2>` is residually finite. There `t` strictly
compresses `<a>`, and `C(<a>) = Z[1/2]` is normalized by `t`, as Theorem R
predicts. The free group `F_2 x F_2` is LEF, and it is consistent with
Theorem B because both factors are LEF.

**What it does not say.** It does not decide whether hyperbolic groups are
sofic. It does not touch certificates that are neither defects nor commuting
pairs: local testability and Cheeger thresholds, hyperlinear Burnside
finiteness, or HS-stability of Kazhdan hyperbolic groups.

No literature survey for novelty was done. Not Lean-verified.
