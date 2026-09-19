---
rg: 2
id: stw99-lxvi-tracial-free-constructions-are-stably-finite
kind: claim
title: Trace-preserving reduced free constructions over CAR are stably finite
distinct_from:
  stw99-lxvi-finite-index-car-envelopes-are-stably-finite: that requires a finite Watatani quasi-basis and embeds the envelope into one matrix corner over CAR; this permits infinite-index inclusions and instead uses the faithful vacuum trace of a reduced free construction.
  stw99-lxvi-finite-seed-has-no-quasitrace: that gives an abstract necessary condition on any simple finite seed with an infinite amplification; this identifies broad crossed-product and free-product construction classes in which the forbidden faithful trace is automatic.
  stw99-lxvi-central-matrix-sequence-obstruction: that rules out asymptotically central CAR tails; no centrality or approximate commutation is assumed here.
artifacts:
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

Let `D=M_(2^infinity)` and let `tau_D` be its unique tracial state.

1. For every action `alpha:G actson D` of an arbitrary discrete group, the
   reduced crossed product `D crossed_product_(alpha,r) G` is stably finite.
   If the full crossed product `D crossed_product_alpha G` is simple, it too
   is stably finite.
2. More generally, let `(A_i,E_i)` be a finite or countable family of unital
   C*-algebras containing the same unital copy of `D`, where each
   `E_i:A_i->D` is a faithful conditional expectation and

   ```text
   tau_i=tau_D after E_i
   ```

   is tracial on `A_i`.  Their reduced amalgamated free product over `D` is
   stably finite.  If the corresponding full amalgamated free product is
   simple, it is stably finite as well.
3. In particular, the reduced unamalgamated free product of CAR with any
   finite or countable family of unital C*-algebras carrying faithful
   tracial states is stably finite; so is the full free product whenever it
   is simple.

Consequently none of these crossed-product, reduced-free-product, or simple
full-free-product constructions can produce the finite non-stably-finite
CAR seed equivalent to Problem LXVI.  Nor can one repair simplicity by
passing to a unital hereditary corner of one of the reduced constructions:
all matrix algebras and all corners remain finite.  Combining this with
`stw99-lxvi-injective-limits-cannot-create-instability` also excludes
injective inductive limits of such corners.  The obstruction allows
genuinely infinite Watatani index and makes no nuclearity, exactness, `K_0`,
or centrality assumption.
