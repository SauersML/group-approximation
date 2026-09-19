---
rg: 2
id: shifted-scale-recovery
kind: claim
title: Locally finite commutants recover at shifted scales
invalidates: [separate-commutant-recovery]
---

Reynolds averaging over slowly-growing finite unitriangular envelopes puts
every fixed finite family from the ultraproduct commutant within `o(1)` of
exact coordinate commutants (the Reynolds identity is formalized in
`PropertyT/FiniteGroupAverage.lean`). But the compressor shifts the
exhaustion: `α(K_m) ≤ K_{r(m)}` yields only `C_{r(m)} ≤ D_m = U C_m U*`;
for the unilateral binary shift, `dim(D_m) = 2·dim(C_{m+1})` exactly.
Separate recovery is closed; the live gate is quantized-scale-index.
