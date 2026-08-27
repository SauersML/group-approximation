---
rg: 2
id: maslov-central-regular-lifts-have-diverging-positive-order
kind: claim
title: Maslov central-regular maps lift with diverging finite positivity order
artifacts:
  - research/artifacts/maslov-generator-operator-system-lp-sources-2026-08-22.md
distinct_from:
  fixed-chevalley-prefix-grams-give-only-tracial-positivity: that treats each fixed prefix atlas separately; this constructs one coordinate lift sequence passing matrix-order tests of an order tending to infinity.
  maslov-generator-complete-order-model-is-llp-strength: that fences full operator-system LP models; this identifies exactly how much positivity is automatic in the genuinely tracial quotient without implying LLP.
  strict-psd-regularization-has-no-uniform-hs-affine-error-bound: that gives a generic cone-angle counterexample; this uses the actual tracial ultraproduct quotient and preserves the central-regular Maslov trace profile.
---

**ESTABLISHED.** Let `S` be any finite-dimensional operator system and let

```text
Theta:S -> prod_omega M_(d_n)                            (DPO1)
```

be ucp.  There are integers `k_n ->_omega infinity` and unital `k_n`-positive
maps

```text
phi_n:S -> M_(d_n)                                      (DPO2)
```

such that `[(phi_n(x))_n]=Theta(x)` for every `x in S`.

Apply this to the canonical generator system `S_alpha` and a homomorphism
from a nontrivial Maslov fibre.  By
`deligne-maslov-sector-traces-are-central-regular`, after the residual central
cut its trace is the unique central-regular trace `tau_eta`.  The lifts can be
chosen so that

```text
tr_(d_n)(phi_n(x)) ->_omega tau_eta(x)                   (DPO3)
```

for every `x in S_alpha`.  Thus central-regular trace rigidity and positivity
at every fixed amplification level are automatic simultaneously; neither is
the missing ucp correction.

The remaining scale is exact.  A map into `M_(d_n)` is completely positive
once it is `d_n`-positive, but `(DPO2)` supplies only an unspecified diverging
`k_n`.  Common amplification `x |-> phi_n(x) tensor I_(m_n)` preserves
normalized traces, normalized Hilbert--Schmidt defects, and the exact largest
finite positivity order while replacing the coordinate dimension by
`m_n d_n`.  Hence no criterion depending only on

- the central-regular scalar trace profile;
- finitely many normalized `2`-norm word defects; and
- any fixed matrix-amplification level

can furnish a lower bound of the form `positivity order >= c d_n`.  Such data
are invariant under an amplification which makes
`k_n/(m_n d_n)` arbitrarily small.  This does not rule out a direct
arithmetic theorem implying complete positivity without passing through a
dimension-relative positivity estimate.

This is a precise fence, not a refutation of
`maslov-sector-tracial-generator-ucp-liftability`.  A surviving tracial proof
must either provide positivity through level `d_n` from arithmetic relations,
or prove complete positivity by a genuinely amplification-stable structural
argument.  More finite root atlases or scalar central-regular moment
identities supply neither.
