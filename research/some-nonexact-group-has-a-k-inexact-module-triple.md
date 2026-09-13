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
- `G` **fails Baum--Connes with coefficients** (`module-defect-needs-non-k-exact-host`). Steps
  3--4 of `k-inexact-module-triple-refutes-trivial-coefficient-bc-proof` make the failure
  specific: in the degree `j` of the defect, `mu_(G, C(X))` is not surjective or `mu_(G, C(Z))`
  is not injective. So `G` violates the conjecture at the commutative dual-module coefficient
  `C(V^)` or `C((V/W)^)`. In particular `G` is not a-T-menable
  (`osajda-monster-hosts-for-bc-module-route`, items (3) and (5)). That rules out Osajda's
  non-exact a-T-menable groups and the whole a-T-menable class: non-exactness alone is not enough.
- The C*-sequence `0 -> C_0(U) ⋊_r G -> C(X) ⋊_r G -> C(Z) ⋊_r G -> 0` is not exact, since
  K-theory is half exact on exact sequences of C*-algebras.
- The extension `W -> V ⋊ G -> (V/W) ⋊ G` is not split in any way that forces exactness.
  By `split-quotients-give-exact-reduced-crossed-products`, a module splitting
  `V = W ⊕ V/W`, a finite quotient `V/W`, or `G` co-amenable in `(V/W) ⋊ G` each makes the
  C*-sequence exact.

## Attempts

- **Direct transplant of the Higson--Lafforgue--Skandalis triple.**
  - Dies twice.
    - Its witness is a ghost, and `M_n(C*_r G)` contains none
      (`reduced-group-algebras-contain-no-nonzero-ghosts`).
    - Its ideal is the crossed product of a proper open orbit. A compact dual group `X` with
      `G` acting by automorphisms has no wandering open set
      (`module-dual-actions-have-no-wandering-open-sets`).
  - So any module witness must be detected by something other than counting rank along
    far-away pieces of a proper orbit.
- **Wreath quotients over a Gromov monster.**
  - Example: `V = F_p[G]` and `V/W = F_p[G/H]` with `H` infinite amenable, giving
    `F_p wr G -> F_p wr_(G/H) G`.
  - Part (D) of `split-quotients-give-exact-reduced-crossed-products` shows they escape
    every criterion there:
    - there is no equivariant completely positive splitting;
    - `G` is not co-amenable in the quotient.
  - No mechanism produces a non-exact element.
- **A sufficient C*-criterion, still unrealized.**
  `window-defect-forces-module-triple-inexactness` needs:
  - a local self-adjoint `D` gapped at `0` on every boundary configuration of `Z`;
  - approximate kernels of `D` in configurations that agree with boundary configurations on
    growing windows.

  For finitely generated `W`, `Z` is an algebraic subshift of finite type. So a witness needs
  locally admissible patches that do not extend to global solutions, at the places where `D`
  has approximate kernel. The criterion holds for the non-module triple `(βG, ∂βG)` of an
  embedded large-girth expander. No module instance is known, and a C*-defect does not by
  itself give a K-defect.
- **The base group must fail BC with coefficients.**
  `module-defect-needs-non-k-exact-host` (established) reads the diagram chase of
  `k-inexact-module-triple-refutes-trivial-coefficient-bc-proof` in the direction that
  constrains `G`: a group satisfying Baum--Connes with coefficients is K-exact, so every module
  triple over it is K-exact. A witness cannot be sought among a-T-menable groups, even the
  non-exact ones. The remaining hosts are expander monsters. Their only known coefficient failure
  sits on a proper open orbit (`monster-bc-detector-lives-on-a-proper-orbit-ideal`), exactly the
  structure a dual-module action lacks (`module-dual-actions-have-no-wandering-open-sets`). The
  open crux is `monster-bc-failure-at-measured-coefficient-is-the-module-crux`.
- **C*-inexactness without a K-defect.** Take a non-exact group that satisfies Baum--Connes with
  coefficients, such as Osajda's a-T-menable groups without property A. Context, not imported:
  without property A the translation action on `βG` is not amenable (Higson--Roe). So `C*_r(G)`
  is not exact (Ozawa, arXiv:math/0002185, Theorem 3), and `⋊_r` fails to preserve some exact
  sequence (Kirchberg--Wassermann Theorem 5.2, as cited there). Every such sequence is still
  K-exact, because `G` is K-exact. So C*-inexactness without a K-defect does occur for general
  coefficients, and `window-defect-forces-module-triple-inexactness` cannot give a K-defect on its
  own. Whether some **module** triple over such a group is C*-inexact is not known.
- **Where every attempt stops.** A C*-defect needs an element of `C(X) ⋊_r G` that dies on
  `Z` but is not approximable from `C_0(U)`. A K-defect additionally needs an invariant on
  `K_0(C(X) ⋊_r G)` that vanishes on the image of the ideal. Traces from invariant measures
  cannot separate the two: a trace vanishing on the ideal is supported on `Z`, so it also
  vanishes on every element that dies on `Z`.
