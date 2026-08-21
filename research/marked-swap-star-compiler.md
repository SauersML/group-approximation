---
rg: 2
id: marked-swap-star-compiler
kind: claim
title: Authenticate one common-source orthogonal swap star only inside a central marked sector
distinct_from:
  common-source-orthogonal-partial-swap-star-compiler: that asks the two swap words to have the prescribed chart on the whole matrix; this permits arbitrary action on the complementary central sector.
  finite-normalizer-star-no-go: that rules out solving the marked-sector target by a finite packet or an automorphism-only self-similar actuator; this records the remaining positive compiler interface.
---

**OPEN.**  Construct a finite presentation `Gamma=<X|R>`, a central
involution `y`, and involution words `j_0,j_1`.  Put

```text
p=(1-y)/2,                  h=j_0j_1.                 (MSC1)
```

Require:

1. an exact infinite-dimensional representation in which `y`, `h`, and
   `yh` are all nonidentity and the marked sector contains a nonzero binary
   common-source orthogonal-range swap star;
2. every sufficiently accurate canonical-trace matrix model, after
   exactifying fixed finite packets, yields on `pH` partial isometries
   `S_0,S_1` with

   ```text
   S_i^*S_i=Q,
   (S_0S_0^*)(S_1S_1^*)=0,                            (MSC2)
   ```

   and `j_i|_(pH)=J_(S_i)+o(1)` with a
   dimension-independent modulus.

No condition is imposed on `(1-p)H`.  By
`central-marked-swap-star-has-two-word-trace-floor`, these clauses already
imply nonhyperlinearity.

One may replace the involution `y` by a fixed finite central subgroup and
work in one character projection.  The finite central Fourier extension of
the same theorem then uses the fixed word list `{ch:c in C}`; this is often
the native form of a Pauli/Schur selected carrier.

The natural local seed is `pauli-two-child-transfer-packet`, which has one
exact source and two orthogonal ranges.  The missing assertion is promotion
of that selected Pauli carrier to the whole marked source in finite matrix
models.  The promotion cannot consist only of finite packet restriction
tables or self-similar automorphisms: `finite-normalizer-star-no-go` leaves
their marked Plancherel model exact.

## Attempts

- **Use one finite S3/D8 role packet.**  Its marked regular sector has the
  exact conditional moment `(FNA2)` and cannot be a nonzero star.
- **Copy the packet by Thompson or branch normalizers.**  Packet
  automorphisms preserve the same finite regular model; finite prefix clone
  patterns also have locally finite stationary models.
- **Leave the unmarked characters uncontrolled.**  This is no longer an
  obstruction: the two-word checksum cancels them exactly.
- **Use a proper-corner or mixed-holonomy actuator.**  This remains live.
  It must fail on the regular packet and prove selected-carrier saturation
  only for finite matrix extensions.
