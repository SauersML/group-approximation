---
rg: 2
id: stage-one-lamp-difference-radical
kind: claim
title: The first collapse stage has an explicitly computed, nontrivial radical
distinct_from:
  compression-wreath-five-radicals-coincide: That identifies one kernel with five residuals once the defect quotient is known to be residually finite; this computes a concrete piece of that kernel, as lamp differences, with no hypothesis on the quotient.
  profinite-twins-opposite-mf: That compares two groups; this is a statement about one, naming the subgroup that separates them.
artifacts:
  - GroupApproximation/Sofic/AscendingHNNTelescopeRadical.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

For the ascending-HNN wreath product `W = K^(V/Gamma) x| V` with an involutive
lamp value `k`, the collapse commutator of the witness lamp is not an abstract
element of the defect: it is a **lamp difference**,

    [iota gamma, witnessLamp k] = lampDiff (iota gamma . tGamma) (tGamma) k,

the configuration carrying `k` at one site and `k^-1` at another.  That single
identity converts the compression-collapse theorem into a statement about the
coset space.

Consequences, all unconditional given property (T) of the base and properness
of the self-embedding:

- Conjugation transports a difference to any translate of its site pair, so
  every base-move difference at every site lies in the involutive collapse
  defect.
- The subgroup they generate -- the **first-stage radical** -- lies in the
  literal MF radical, by the involutive endpoint, with no analytic hypothesis
  left.
- It is nontrivial exactly when the self-embedding is proper.
- When the first-stage quotient is MF, the inclusion is an equality, so the MF
  radical of `W` is computed outright.

The first stage does **not** reach the whole telescope: a base move shifts a
coset by the level `-1` copy `t^-1 iota(Gamma) t` only.  That turns out not to
matter, because the collapse applies to each level on its own rather than by
iteration -- see [[full-telescope-radical-in-mf-radical]], which proves the
inclusion for every pair of sites of equal height.
