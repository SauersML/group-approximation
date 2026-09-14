---
rg: 2
id: fournier-facio-one-compressor-subgroup-reduces-to-gamma
kind: claim
title: The Fournier--Facio one-compressor subgroup carries the whole compression triple and is hyperlinear exactly when Gamma is
distinct_from:
  fournier-facio-group-contains-simple-wreath-shift: That records the subgroups J_k, S wr Z and the self-similar tail inside G; this observes that all of them lie in the one-compressor subgroup <Gamma,t_1>, which has no property (T) and reduces to Gamma.
  fournier-facio-regular-models-carry-commutant-shift: That computes the proper commutant shift in every tracial model of G; this shows the shift is a relation of <Gamma,t_1> and is therefore realized whenever Gamma is hyperlinear.
artifacts:
  - research/artifacts/fournier-facio-one-compressor-reduction-2026-09-11.md
---

**ESTABLISHED.**  Let `G`, `Gamma`, `t_1`, `t_2`, `S` and `J_k` be as in
`fournier-facio-torsion-free-skeleton` and
`fournier-facio-group-contains-simple-wreath-shift`, and put
`H_i = <Gamma, t_i>`.

1. `H_1` contains `pi(S)`, `J = J_0`, every `J_k`, the internal wreath
   product `S wr Z`, and `Gamma x (+)_(k<=0) J_k`.  Every relation used by
   `fournier-facio-regular-models-carry-commutant-shift` holds in `H_1`.
2. `t_1 Gamma t_1^-1 != Gamma`, since `Gamma >= J_1 x t_1 Gamma t_1^-1` with
   `J_1 != 1`.  Hence `H_1` has no property (T).
3. `H_1` is hyperlinear if and only if `Gamma` is, and sofic if and only if
   `Gamma` is.  The same holds for `H_2`.

**Reading for the negative branch.**  Any normalized-HS argument that uses
only one compressor proves that the compression subgroup `Gamma` is
nonhyperlinear.  This covers property (T) of `Gamma`, the nesting
`t_1 (Gamma x J) t_1^-1 <= Gamma`, simplicity or non-LEF of `J`, and the
commutant shift with growing relative commutants.  If `Gamma` is hyperlinear,
the Hilbert-hotel shift on the `Gamma`-commutant is realized in regular
models of `H_1` in `R^omega`, so it is not by itself an obstruction.  The
soficity statement says the same about OpenAI Proposition 2.3: its
ambient-(T) hypothesis cannot be dropped for `H_1` unless `Gamma` is already
nonsofic.  A no-go for `G` that does not pass through `Gamma` must use the
second compressor essentially.  In the permutation proof the second
compressor enters only through property (T) of `G`, in the median
size-matching step (artifact, Section 3(c)).  Whether two compressors without
ambient (T) already escape the reduction is not decided here.  In the
pre-quotient double HNN extension `E`, the kernel of `E -> F_2` contains
amalgams `P^(u_1) *_P P^(u_2)` over the Kazhdan subgroup `P`, where
`P^(u_i) = u_i^-1 P u_i`, and no elementary permanence theorem covers those
(artifact, Section 3(e)).

Proof: `fournier-facio-one-compressor-reduction-proof`.
