---
rg: 2
id: toeplitz-defect-rejects-tensor-dilution-only-after-square-decoding
kind: claim
title: The Toeplitz defect rejects canonical tensor dilution exactly after square coefficient decoding
distinct_from:
  canonical-packet-traces-do-not-place-old-commutant-density: that constructs the canonical tensor dilution before coefficient coupling; this determines whether the actual Toeplitz head relation excludes it.
  positive-toeplitz-head-is-square-defect-or-rectangular-escape: that proves the abstract contraction inequality and its rectangular sharpness; this applies it to the proposed PCD coefficient cell and identifies the ordinary-group decoding debt.
  hs-schur-toeplitz-root-defect-collapse: that asks for collapse of the named root word in arbitrary HS microstates; this proves that any square coefficient decoder would already settle that endpoint without an old-commutant-density argument.
---

**ESTABLISHED AUDIT.**  Let `P_f` be the forbidden Schur projection in the
packet-headed Toeplitz relation

```text
yx=1,                    1-xy=P_f.                     (TDT1)
```

Suppose a proposed ordinary-word coefficient cell decodes contractions
`X,Y` and the packet projection `P` on one finite matrix reservoir, with
defects

```text
epsilon_l=||YX-1||_2,
epsilon_h=||P-(1-XY)||_2.                              (TDT2)
```

Then the sharp trace-cyclicity estimate is

```text
tau(P)<=epsilon_l+epsilon_h,
epsilon_l^2+epsilon_h^2>=tau(P)^2/2.                   (TDT3)
```

Consequently the canonical tensor dilution of
`canonical-packet-traces-do-not-place-old-commutant-density` cannot extend
such a square decoder with vanishing defect while retaining fixed forbidden
mass.  This remains true if `X,Y` entangle the old and packet tensor factors;
only their residence in the same square matrix algebra is used.

Thus the actual Toeplitz coefficient relation does visibly exclude the
tensor countermodel in its genuine coefficient semantics.  But `(TDT3)` is
already terminal: positive canonical forbidden mass directly pays a fixed
relator floor.  No Schur Reynolds placement in the old commutant, bounded
old-group type, or property `(T)` density argument is then needed.

The current elementary/Steinberg group presentation does not furnish the
hypothesis of `(TDT2)` for arbitrary normalized-HS unitary microstates.  Its
root words obey multiplication commutators, but an arbitrary unitary
representation need not arise from a ring homomorphism

```text
R_f -> M_d(C).
```

In particular the decoded source and target coefficient blocks can be
rectangular Morita reservoirs.  Coordinate inclusion and projection then
satisfy `(TDT1)` with zero error and positive `P`, as in
`positive-toeplitz-head-is-square-defect-or-rectangular-escape`; all pasted
mixed Steinberg triangles remain exact by
`mixed-steinberg-loops-admit-morita-rectangular-model`.

Therefore the existing Toeplitz relations yield the following exact fork:

```text
square coefficient decoder  => immediate HS contradiction by (TDT3),
no square decoder            => the established coefficient/Steinberg
                                identities admit the rectangular escape.  (TDT4)
```

This does not construct a counterrepresentation of the full Toeplitz group:
doing so with the canonical root mark alive would solve the open endpoint in
the opposite direction.  It proves that PCD has no shorter deduction from
the already established coefficient identities.  Its proposed covariance
cell must itself authenticate the same reservoir or charge the rectangular
change; once it does, `(TDT3)` supersedes `(PCD1)`.
