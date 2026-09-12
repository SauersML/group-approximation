---
rg: 2
id: child-carrier-relative-pauli-holonomy
kind: claim
title: Compress the named parent-absence Pauli pair to the child carrier and return it with constant HS cost
artifacts:
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
  - experiments/minimal_rank_one_support_compiler.py
  - experiments/schur_packet_hnn_flow_search.py
distinct_from:
  fixed-scale-contextual-multiplicity-holonomy: that asks for a return network for arbitrary Schur-Clifford predicate packets; this fixes a named core/relative factor and only asks to localize it to one child projection.
  relative-rank-one-fanizza-groupification: that includes the full Turing recurrence and separated-mark interface; this is its local finite packet/holonomy theorem.
---

Construct a fixed finitely presented group gadget containing the conditional
packet of `conditional-parent-absence-packet-exposes-relative-pauli`, a named
child selector `z_f`, and finitely many transport words, such that every
sufficiently accurate normalized-HS microstate has the following property.

If `q` is the spectral mass of the sector

```text
J=-1, z_e=+1, z_f=-1
```

(parent absent, child active), then the fixed relative pair `(p_2,q_1)` induces
three endpoint-sharing rank-one transports and

```text
sum_(r in R_local)||r(U)-I||_2^2 >= c q-o(1)           (CRH1)
```

for a universal `c>0`.  On the harmless sector `(e,f)=(0,0)`, the same
relative Pauli pair must admit zero-energy transport, so the estimate is truly
child-carrier-localized.

Once the three endpoint charts exist, their approximate marginal bookkeeping
is no longer an open loss: `robust-rank-one-endpoint-marginal-floor` gives
failure mass at least `q-sqrt(2 E_end)`.  The remaining content of this claim
is therefore the group-word compression itself and an upper payment bound for
the three resulting failure masses.

## Attempts

- **Uncompressed return fails.**  The relative pair is also Pauli on `(0,0)`,
  so any holonomy that charges it without reading `z_f` destroys allowed exact
  models.
- **Scalar phase switching fails.**  A central relation trying to activate the
  holonomy only when both `Jz_e=-1` and `z_f=-1` is an AND constraint and falls
  back into the affine selector barrier.
- **Full-center HNN transport cancels the desired bit.**  The complete
  `GL_3(F_2)` packet search finds five involutive Pauli charts from the
  forbidden rank-two character to distinct rank-one characters.  However, a
  stable letter carrying the full selector center directly equates the two
  central-sector Hilbert dimensions.  Both restrictions then have edge-spin
  multiplicity `dim(H_k)/2`, so the ambient `4`-versus-`2` simple dimensions
  cancel.  A finite graph of these charts has exact regular-flow models with
  positive forbidden mass.  See
  `full-center-hnn-transport-cancels-schur-multiplicity`.
- **Live attack.**  Use the three fixed subgroup pivots found by the conditional
  MSI search as endpoint charts, retain the common fixed core, and make the
  child projection select the relative multiplicity corner before applying
  `rank-one-no-signaling-pairing-floor`.  The missing step is a group-word
  realization of that compression whose relator cost controls the compressed
  intertwiner Laplacians.  The endpoint charts must retain only shared
  marginals, not the full central atom, or the transport must pass through a
  genuinely non-Bass--Serre compressor before returning to the fixed baseline
  packet.
