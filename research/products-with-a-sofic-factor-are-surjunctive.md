---
rg: 2
id: products-with-a-sofic-factor-are-surjunctive
kind: claim
title: The product of a surjunctive group and a sofic group is surjunctive
distinct_from:
  finite-direct-products-of-surjunctive-groups-are-surjunctive: that allows two arbitrary surjunctive factors; this requires one factor to be sofic, where sofic models give a transplant of the automaton onto the other factor.
  products-with-lef-permanence-closure-factors-are-surjunctive: that is the proved case of a factor in the LEF permanence closure, realized exactly on finite sets; this allows every sofic factor, realized only approximately.
artifacts:
  - research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md
---

**OPEN.** If `G` is surjunctive and `K` is sofic, then `G x K` is surjunctive.

**Place in the graph.**
- It is implied by `finite-direct-products-of-surjunctive-groups-are-surjunctive`, and so by the conjecture.
- It is open only when `K` lies outside the LEF permanence closure, and no sofic group is known to
  lie outside it, so there is no concrete test instance.

## Attempts

- **Sofic fibre device with stored bad points (w4-free-pos-b).**
  - **Setup.** Transplant the automaton onto `G` with alphabet `A^V` for a sofic model `V` of `K`, storing
    the input on bad points.
  - **Single-fibre case.** It closes when some Garden of Eden pattern lies in one fibre `{g} x K`
    (`strict-product-automata-have-no-single-fibre-garden-of-eden`).
  - **Multi-fibre case.** It gives an injective automaton over `G` into `n` copies of a proper subshift times a
    full shift larger by `q^(epsilon |V|)`. It closes exactly under quantitative surjunctivity of `G`
    (`sofic-factor-products-via-quantitative-surjunctivity`).
  - **Where it dies.** Plain surjunctivity of `G` constrains only maps between equal full shifts.
