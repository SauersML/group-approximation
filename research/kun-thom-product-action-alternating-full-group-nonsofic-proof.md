---
rg: 2
id: kun-thom-product-action-alternating-full-group-nonsofic-proof
kind: route
title: Rigid-stabilizer commutators put the lamps and the commutator of a finite-index normal subgroup into the alternating full group
target: kun-thom-product-action-alternating-full-group-is-nonsofic
requires:
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/kun-thom-alternating-full-group-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

1. **Rigid stabilizers.** If `q in A(Y)` moves a clopen `U` off itself, then `[[Y]]_U' <= A(Y)`, since
   `[a,b] = [a,[b,q]]` for `a, b` supported in `U`, and `A(Y)` is normal in `[[Y]]`.
2. **Lamps.** Each lamp restricted to a small cylinder lies in the Klein group `[Alt(4), Alt(4)]` of flips on two
   further coordinates. Cylinder 3-cycles move those cylinders off themselves, so every lamp lies in `A(Y)`.
3. **The normal subgroup.** `K` preserves every layer `C x {p}`. Layer 3-cycles move layers off themselves, so
   `[K,K] <= A(Y)`.
4. **Finite index.** `K` has (T), so `[G : [K,K]]` is finite.
5. **Nonsofic.** The image of `W` is a Kun--Thom wreath over `(G/Z, Gamma/Z)`, `Z = core_G(Gamma) ∩ K`, and is
   nonsofic by Theorem A. Soficity passes to finite extensions, so its finite-index subgroup inside `A(Y)` is nonsofic.

**Verification.** `w3-vf-positive` passed this route (Section 12 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`). Theorem A hypotheses for the quotient pair `(G/Z, Gamma/Z)` are checked in 12.1.
