---
rg: 2
id: some-nonexact-group-has-a-k-inexact-module-triple
kind: claim
title: Some countable group has a module quotient whose reduced crossed-product K-theory sequence is not exact in the middle
distinct_from:
  k-inexact-module-triple-refutes-trivial-coefficient-bc: that is the established implication from a K-inexact module triple to a trivial-coefficient counterexample; this is the open existence of such a triple.
  baum-connes-counterexample-group-exists: that is the root; this is a sufficient condition for it that lives entirely in crossed products by one group G with coefficients dual to Z[G]-modules.
---

**OPEN.** There are a countable group `G`, a countable `Z[G]`-module `V` and a submodule `W`
such that, with `X = V^`, `Z = W^perp` and `U = X \ Z`, the sequence

```text
K_j(C_0(U) ⋊_r G)  ->  K_j(C*_r(V ⋊ G))  ->  K_j(C*_r((V/W) ⋊ G))
```

is not exact at the middle for some `j`. By
`k-inexact-module-triple-refutes-trivial-coefficient-bc`, this refutes the Baum--Connes
conjecture with trivial coefficients for `V ⋊ G` or for `(V/W) ⋊ G`.

**Necessary features.**
- `G` is not exact (Kirchberg--Wassermann; context, not imported).
- The C*-sequence `0 -> C_0(U) ⋊_r G -> C(X) ⋊_r G -> C(Z) ⋊_r G -> 0` is not exact, since
  K-theory is half exact on exact sequences of C*-algebras.
- The extension `W -> V ⋊ G -> (V/W) ⋊ G` is not split in any way that forces exactness.
  A module splitting `V = W ⊕ V/W`, a finite quotient `V/W`, or `G` co-amenable in
  `(V/W) ⋊ G` each makes the C*-sequence exact. That argument is a separate claim of this
  lane.

## Attempts

- **Direct transplant of the Higson--Lafforgue--Skandalis triple.**
  - Dies twice.
    - Its witness is a ghost, and `M_n(C*_r G)` contains none
      (`reduced-group-algebras-contain-no-nonzero-ghosts`).
    - Its ideal is the crossed product of a proper open orbit. A compact dual group `X` with
      `G` acting by automorphisms has no wandering open set, because Haar measure is
      invariant.
  - So any module witness must be detected by something other than counting rank along
    far-away pieces of a proper orbit.
- **Wreath quotients over a Gromov monster.**
  - Example: `V = F_p[G]` and `V/W = F_p[G/H]` with `H` infinite amenable, giving
    `F_p wr G -> F_p wr_(G/H) G`.
  - These survive every splitting criterion found so far.
  - No mechanism produces a non-exact element.
- **Where every attempt stops.** A C*-defect needs an element of `C(X) ⋊_r G` that dies on
  `Z` but is not approximable from `C_0(U)`. A K-defect additionally needs an invariant on
  `K_0(C(X) ⋊_r G)` that vanishes on the image of the ideal. Traces from invariant measures
  cannot separate the two: a trace vanishing on the ideal is supported on `Z`, so it also
  vanishes on every element that dies on `Z`.
