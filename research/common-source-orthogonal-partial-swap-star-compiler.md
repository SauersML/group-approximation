---
rg: 2
id: common-source-orthogonal-partial-swap-star-compiler
kind: claim
title: Compile one common-source orthogonal partial-swap star into ordinary words
distinct_from:
  common-partial-isometry-swap-game-compiler: that authenticates a common swap and then compiles a fixed static game; this asks only for two orthogonal children of one source and uses the canonical trace of their swap product as the breaker.
  affine-leavitt-steinberg-hs-coefficient-decoder: that reconstructs an approximate relative Leavitt cell and ties its active projection to the affine mark; this asks only for the two involutive swap words and one common-source/orthogonal-range chart.
  cyclic-conjugacy-does-not-synchronize-swap-sources: that gives an exact stationary model for transported but separate sources; this explicitly requires a literal common source in the decoded matrix chart.
  central-marked-swap-star-has-two-word-trace-floor: that weakens this compiler by allowing arbitrary action outside one central marked sector and isolates the sector with two ordinary word traces.
---

**OPEN.**  Construct a finite presentation `Gamma=<X|R>` and two words
`j_1,j_2` with the following properties.

1. An exact infinite-dimensional representation decodes one projection
   `Q`, two partial isometries `S_1,S_2` with

   ```text
   S_i^*S_i=Q,
   (S_1S_1^*)(S_2S_2^*)=0,                            (OSC1)
   ```

   and sends `j_i` to the partial-isometry swap `J_(S_i)`.  In particular
   `h=j_1j_2` is nonidentity.
2. Every sufficiently accurate canonical-trace matrix model, after
   exactifying only fixed finite packets, yields data satisfying `(OSC1)`
   and

   ```text
   ||j_i(U)-J_(S_i)||_2=o(1)                          (OSC2)
   ```

   with a dimension-independent modulus.

Then `even-partial-swap-star-has-canonical-trace-floor` gives

```text
Re tr(h(U))>=1/4-o(1),                                (OSC3)
```

whereas canonical microstates of the nonidentity word `h` require
`tr(h(U))->0`.  Hence the output group is non-hyperlinear.

The target is deliberately smaller than a coefficient-ring decoder and
smaller than a static-game transducer.  It is the two-child finite-matrix
shadow of a properly infinite corner, expressed entirely through two
involutive words and one trace moment.

The load-bearing clause is the **literal common source**.  Coxeter relations
`j_i^2=1`, `(j_1j_2)^3=1` alone define a finite packet and admit regular
finite-dimensional representations.  Cyclic or expander transport of
separately decoded sources is also insufficient by
`cyclic-conjugacy-does-not-synchronize-swap-sources`.  The compiler must
make the two swaps share the same bottom source coordinate and place their
top ranges in orthogonal named sectors.

The affine--Leavitt Steinberg lane is a natural host: its coefficient algebra
already contains two isometries with the relations `(OSC1)`, and elementary
matrix formulas supply exact swap words.  What is not yet proved is that
normalized-HS microstates decode those words into one common finite
multiplicity reservoir.  Thus this node isolates a one-word boundary target;
it does not claim that the old rectangular escape has disappeared.

There is now a strictly weaker marked-sector target.  It is enough to add a
central nontrivial involution `y`, recover `(OSC1)--(OSC2)` only on
`p=(1-y)/2`, and prove both `h=j_1j_2` and `yh` nonidentity.  By
`central-marked-swap-star-has-two-word-trace-floor`,

```text
Re(tr(h)-tr(yh))>=1/4(1-tr(y))-o(1).                 (OSC4)
```

Canonical microstates make the left side tend to zero and the right side to
`1/4`.  Consequently the compiler no longer has to control the diagonal
complement signs or any action on the unmarked finite-packet characters.

This weakening does not make a fixed finite packet sufficient.
`finite-normalizer-star-no-go` computes
the marked Plancherel trace and shows that no finite packet, nor any
self-similar actuator acting only by packet automorphisms, can saturate its
whole marked sector with a nonzero binary star.  A proper-corner, mixed
holonomy, or genuinely matrix-only selected-carrier return is still needed.

## Attempts

- **Only the abstract swap/Coxeter group.**  Its regular representation is
  an exact finite model; it does not remember the two-copy chart.
- **Conjugate context sources around a cycle.**  The coordinate-shift model
  gives zero defect with orthogonal sources.
- **Separate finite packet types for the two children.**  This can enlarge
  the recovered label alphabet while shrinking multiplicity, reproducing
  rectangular escape.
- **Trace ledger after decoding.**  This part is complete: `(OSC3)` has a
  fixed `1/4` margin and needs no recursive accumulation estimate.
- **Use a central mark but leave the unmarked packet uncontrolled.**  This
  is now safe by the two-word checksum `(OSC4)`; complement cancellation is
  removed exactly.
- **Normalize one finite packet by a Thompson/branch action.**  Its regular
  representation extends through every packet automorphism, so it retains
  an exact stationary Plancherel countermodel.
