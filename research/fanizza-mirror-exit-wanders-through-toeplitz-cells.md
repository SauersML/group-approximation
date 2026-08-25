---
rg: 2
id: fanizza-mirror-exit-wanders-through-toeplitz-cells
kind: claim
title: Decode the Fanizza complement exit into arbitrarily many wandering Toeplitz cells
distinct_from:
  toeplitz-coordinate-paulis-localize-cells-and-grams: that places the source Gram near the old-spin commutant using addressed Pauli rows; this must place the chord-dependent complement exit in distinct addressed cells and obtain pairwise overlap decay.
  diagonal-difference-shift-propagates-pauli-incidence: that propagates commutation between the two clocks without identifying them; this needs a mixed incidence between the decoded complement exit and the moving coordinate PVM.
  fanizza-matrix-coordinate-source-full-compression: that asks to make the source Gram full directly; this asks only for many nearly orthogonal copies of the finite mirror exit and then uses finite trace capacity.
---

Construct a finitely presented extension of the native Fanizza/Toeplitz cell
with the following effective finite-coordinate decoding property.  For every
matrix microstate of defect `delta`, packet exactification gives

```text
H<=E,       F=E-H,       Q=UEU^*,       A=(1-E)Q(1-E),
tr(H)=1/8+o_delta(1),       ||QH||_2<=omega(delta),     (FMW1)
```

and a computable depth `N(delta)->infinity` with decoded positive
contractions

```text
A_i=V_i A V_i^*                 (0<=i<N(delta))         (FMW2)
```

for unitary moving-coordinate words `V_i`, such that

```text
max_(i!=j)||A_i^(1/2)A_j^(1/2)||_2<=omega(delta),
omega(delta)->0.                                           (FMW3)
```

The exact countably amplified HALT representation extends the cell with
`Q=F`.  Hence `A=0` there and every wandering incidence is exact.  The
relations must authenticate `(FMW2)--(FMW3)` only after finite packet and
Toeplitz-coordinate decoding; they must not assert that the fixed
group-algebra corner `(1-E)UEU^*(1-E)` vanishes.

`wandering-complement-contractions-pay-fanizza-mirror` then gives

```text
1/8-o(1)<=omega(delta)^2+1/N(delta)+omega(delta),       (FMW4)
```

which is impossible as `delta->0`.

## Attempts

- **Existing diagonal-difference incidence stops at the commutant.**  It
  proves that the source Gram is close to the old-spin commutant, but the
  scalar reset spectator lies in that commutant and can carry the whole
  mirror exit.  The new relation must locate `A`, not merely commute it with
  addressed Paulis.
- **One selected coordinate is density-zero.**  A single Toeplitz cell at
  depth `N` has normalized mass of order `1/N`; selecting it cannot carry the
  native `1/8` guard.  The compiler must produce the full family `(FMW2)` and
  use its aggregate capacity, rather than pick one moving cell.
- **A literal complement relation hits the regular firewall.**  Declaring
  `A=0`, or declaring the full oriented row to be a relator, forces the
  positive D8 guard to vanish in the regular finite trace.  The only live
  syntax is a decoded moving-cell incidence whose number of tested cells is
  chosen from the matrix defect.
- **Amenable finite-window periodization is not by itself a countermodel.**
  The safe infinite completion has `A=0`; the finite balanced mirror has
  `tr(A)=1/8`.  Periodizing a fixed window either dilutes the mirror mass or
  pays a positive density of moving-cell overlap.  What remains unproved is
  the ordinary-word mechanism forcing that dichotomy on the decoded native
  chord.
