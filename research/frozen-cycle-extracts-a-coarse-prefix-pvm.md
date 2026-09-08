---
rg: 2
id: frozen-cycle-extracts-a-coarse-prefix-pvm
kind: claim
title: A frozen coordinate cycle gives a quantitative auxiliary S3 anchor and a coarse prefix PVM
distinct_from:
  leavitt-has-an-explicit-finite-c-killing-certificate: That identifies the actual finite packet and excludes exact marked models; this rounds only its auxiliary j word while fixing the coordinate cycle and identifies the missing two-child projection transport.
  frozen-leavitt-curvature-has-no-small-invariant-hull: That obstructs reducing containment for a localized residual under unchanged actors; this extracts a coarse covariant PVM from two small auxiliary S3 defects, without requiring it to contain a residual.
artifacts:
  - research/artifacts/frozen-cycle-coarse-prefix-receiver-2026-09-08.md
---

Let `C,J` be unitaries on `C^n`, with `n=3m`, `C^3=I`, and each
cube-root eigenspace of `C` of dimension `m`. Write

```text
r=||(JC)^2-I||_2,       s=||J^2-I||_2.
```

There is an auxiliary unitary `J_0` in the same dimension, with `C`
unchanged, such that

```text
J_0^2=(J_0 C)^2=I,
||J-J_0||_2 <= sqrt(2/3) r +(1/sqrt(2)+2/sqrt(3)) s
             <= 2(r+s).
```

There is a PVM `Q_00,Q_01,Q_1`, each projection of rank `m`, on which
`C` cycles the labels `00 -> 01 -> 1 -> 00`, while `J_0` interchanges
`00,01` and preserves `1`. Preservation of a cell does not assert
pointwise identity on its range.

For every orthogonal refinement `Q_1=Q_10+Q_11` and every unitary `B`,

```text
||B Q_01 B^*-Q_11||_2^2 + ||B^* Q_01 B-Q_10||_2^2 >= 1/3.
```

Thus one of the two prescribed child transports has error at least
`1/sqrt(6)`. The constant is attained by an explicit six-point model
also satisfying `B^3=(J_0 B)^4=I`.

There is also a source-authenticated frozen model in dimension
`672=24*28`, from the regular representation of
`GL_3(F_2) times C_2^2`, in which the actual compiled `B` equals `I`.
All eight retained packet rows except `rho_5,rho_8` hold exactly;
those two evaluate to `D,c`, respectively, and each has HS defect
`sqrt(2)`. For every coarse PVM and refinement, the two child squared
errors then sum to exactly `1`. Thus the other six retained rows,
including `rho_6,rho_7`, do not force the fine receiver. This makes
no assertion about omitting just one of `rho_5,rho_8`.

For the native Leavitt packet, substitute `J=j(B_1,B_2,B_3,C)` and
the compiled `B` word. The theorem does not modify the original `B_i`
to realize `J_0`, or derive the child transports from their relators.
Extracting those transports with a controlled error remains open; no
uniform packet gap follows from the coarse PVM alone.
