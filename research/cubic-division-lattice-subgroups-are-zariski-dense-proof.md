---
rg: 2
id: cubic-division-lattice-subgroups-are-zariski-dense-proof
kind: route
title: A proper A_1 subgroup would give a quadratic subfield or a first-kind involution of a cubic division algebra
target: cubic-division-lattice-subgroups-are-zariski-dense
requires: []
artifacts:
  - research/artifacts/sl3z-invariant-vector-witnesses-2026-09-12.md
---

Let `H <= Gamma_D` be nonamenable, `Z` its Zariski closure.  `H cap Z^0` has
finite index in `H`, so `Z^0` is not solvable and contains a `Q`-simple
semisimple subgroup `S`.  Over `Qbar`, `SL_1(D)` becomes `SL_3`, whose simple
subgroups are `SL_3`, a block `SL_2` (reducible) or `SO_3` (irreducible).

* **Reducible `A_1`.**  The centralizer of a block `SL_2` in `SL_3` is the
  one-dimensional torus `diag(t,t,t^(-2))`, unique, hence Galois-stable and a
  `Q`-torus `T` of `SL_1(D)`.  The `Q`-span of `T` in `D` is a commutative
  subalgebra that becomes `Qbar x Qbar` after extension, a quadratic subfield
  of `D`.  A division algebra of degree 3 has no quadratic subfield (subfields
  have degree dividing 3).  Contradiction.
* **Irreducible `A_1`.**  `S` preserves a nondegenerate symmetric bilinear form
  `b` on `Qbar^3`, unique up to scalar by Schur.  For a Galois element `s`,
  `s(b)` is `s(S) = S`-invariant, so `s(b) in Qbar^x b` and the adjoint
  involution of `b` on `D (x) Qbar = M_3(Qbar)` is Galois-stable.  It descends
  to an involution of the first kind on `D`, so `D = D^op` and `[D]` has order
  at most 2 in `Br(Q)`.  The exponent of a degree-3 division algebra is 3.
  Contradiction.

So `S = SL_1(D)` and `H` is Zariski dense.

The setting.  Every degree-3 algebra splits over `R` (`Br(R) = Z/2`), so
`D (x) R = M_3(R)`; `D` is `Q`-anisotropic, so `Gamma_D` is cocompact
(Godement); lattices in `SL_3(R)` have property (T) (Kazhdan).  `D` splits at
all but finitely many `p`, giving `O_D/pO_D = M_3(F_p)`.  The consequence uses
strong approximation for finitely generated Zariski-dense subgroups
(Matthews--Vaserstein--Weisfeiler; Weisfeiler) after passing to a free
subgroup (Tits alternative).  These imports are not re-read here.
