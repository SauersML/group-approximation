---
rg: 2
id: locally-finite-centralizer-derived-subgroup-is-mf-invisible
kind: claim
title: Commuting compressed conjugates force the derived subgroup of a locally finite centralizer into the MF radical
distinct_from:
  locally-finite-defect-subgroup-dies-in-every-corona: that asks for a locally finite normal subgroup anywhere in the compression defect; this needs a specific centralizer and commuting-conjugate configuration, assumes no normality, and kills only its derived subgroup.
  uniform-finite-support-rank-gap-upgrades-compression-collapse: that requires a uniform rank bound across a locally finite normal exhaustion; this works separately in each fixed finite subgroup and uses the actual ranks of corner commutators, with no such bound.
  finite-noncommutative-packet-compression-collapse: that assumes a finite packet normalized by the Kazhdan subgroup; this uses two commuting conjugates of a centralizing packet which need not be normalized after compression.
artifacts:
  - research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md
  - research/artifacts/affine-perfect-lamp-wreath-recheck-2026-09-08.md
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

Let `G` be countable and suppose

```text
L<=G has property (T),
uLu^-1<=L,
C<=C_G(L) is locally finite,
[uCu^-1,ell uCu^-1 ell^-1]=1 for some ell in L.
```

Then every homomorphism of `G` to a norm matrix corona kills
`[C,C]`, and consequently every homomorphism to an MF group does
so. Thus `C` nonabelian implies `G` is not MF, and `C` perfect
implies its whole image is trivial. Normality of `C` is unnecessary.
The conclusion remains valid if the last condition is required
separately for each finite `F<=C`, with `ell` depending on `F`.

The proof uses a Kazhdan spectral projection for `L` and a support
rank normalization for each fixed finite derived subgroup. There
is no lower bound on support proportion and no bound on matrix
dimension. It is a written proof with independent mathematical
review, not a new Lean endpoint. It is explicitly not a proof
avoiding property `(T)`, nor the unrestricted locally finite
normal-subgroup upgrade.

**Independent recheck, 2026-09-08.** A separately forwarded dossier
derived this same criterion, with the same four hypotheses and the same
conclusion, and its derivation was re-verified against this statement in
`research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md`.
Three load-bearing points agree. The normalization is by the support rank
`r_n=rank(p_n)`, so the estimate carries no `sqrt(d_n/r_n)` factor. The
finite-dimensional reversal `||(I-P)UP||=||(I-P)U*P||`, from `B*B` and
`BB*` having equal eigenvalue lists for a square `B=PUP`, is what
transports the Kazhdan spectral projection through the compressor in the
direction actually needed. And the exact correction of an approximate
representation of a fixed finite group is dimension-independent, so it
applies inside each finite `F<=C` separately. The recheck adds no
hypothesis and weakens none. A second instance of the criterion is
`dyadic-perturbation-group-mf-radical-is-finitary-alternating`.

DERIVATION
locally-finite-centralizer-support-rank-proof
