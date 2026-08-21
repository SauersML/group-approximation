---
rg: 2
id: one-product-holonomy-does-not-sew-four-bs-clocks
kind: claim
title: One product holonomy does not sew four Baumslag--Solitar clocks
distinct_from:
  split-higman-cycle-has-haar-marginals-and-maximal-role-gap: that leaves the four clocks completely uncoupled; this adds one ordinary mixed word involving all four edges and still gives an exact countermodel.
  periodic-bs-clock-defeats-spectral-first-hit-checksum: that constructs one exact doubling clock; this alternates the clock with an inverse-mismatch conjugate so the mixed cycle product cancels exactly.
  common-source-orthogonal-partial-swap-star-compiler: that asks for a positive trace product inequality on authenticated partial swaps; the word here controls only a product of four unitary occurrence mismatches and does not control their individual HS energies.
---

Take four split Baumslag--Solitar edges

```text
E_i=<c_i,z_i | c_i z_i c_i^(-1)=z_i^2>,
```

and add the single mixed cycle word

```text
h=(c_0z_0^(-1))(c_1z_1^(-1))
  (c_2z_2^(-1))(c_3z_3^(-1))=1.                     (OPH1)
```

For arbitrarily large odd prime dimensions `q`, this five-relator system
has an exact unitary representation in which

```text
||c_i-z_i||_2^2=2-2/q                                (OPH2)
```

for every `i`.  Along primes tending to infinity, every `c_i` and `z_i`
has Haar limiting marginal moments.

Hence one scalar product-holonomy relation coupling all four local clocks
does not produce a dimension-free Hilbert--Schmidt floor for the individual
occurrence identifications.  The four large mismatch energies can cancel
inside the word exactly.

This is a no-go for the direct one-word repair of the independent-clock
model, not for the actual Higman presentation.  Actual cyclic gluing imposes
four operator identifications between the incoming and outgoing occurrences.
A successful compression of those four identifications to one word would
need a positivity mechanism preventing inverse cancellation--for example,
orthogonal syndrome blocks or a trace-positive common-carrier product.  An
unlocalized unitary product has no such mechanism.

