---
rg: 2
id: printed-ultraproduct-ambient-for-kazhdan-transport
kind: claim
title: The ambient of the printed ultraproduct proof of Kazhdan transport exists
distinct_from:
  kazhdan-asymptotic-commutant-transport: that is the transport theorem itself, already established by the quantitative finite-stage proof; this is the *ambient* the manuscript's printed proof builds before it argues at all, and it can fail to exist without touching the truth of the transport statement.
  coordinate-ultraproduct-transport: that transports a property between coordinate models and their metric ultraproduct in the tracial setting; this asks for one specific object, a Hilbert-space ultraproduct of matrix `L^2` spaces carrying a faithful action of the operator-norm corona.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/UltraproductAdjointAmbient.lean
  - GroupApproximation/Sofic/UltraproductDedekindFinite.lean
  - GroupApproximation/Sofic/UltraproductKazhdanProjection.lean
  - GroupApproximation/Sofic/UltraproductKazhdanTransport.lean
---

OPEN.  Fix a countable group `H`, an element `s`, dimensions `d_n`, and
unitaries `U_n : H -> U(M_{d_n}(C))`.  For every free ultrafilter `omega` on
`N` the printed proof of `thm:kazhdan-transport` (`non_mf_groups_exist.tex`,
lines 516--636) assumes the following package exists, and this claim asserts
that it does:

- **KT.02** the Hilbert-space ultraproduct `K_omega = prod_omega K_n` of the
  spaces `K_n = L^2(M_{d_n}(C), tr_{d_n})`, together with the class map
  `[xi_n]_omega` of a uniformly Hilbert--Schmidt-bounded family and the
  criterion that two classes agree exactly when their difference vanishes in
  normalized Hilbert--Schmidt norm along `omega`;
- **KT.03/KT.04** an action of the norm ultraproduct
  `B_omega = prod_omega B(K_n)` on `K_omega` which is multiplicative and
  faithful enough that an inclusion of ranges of projections can be read back
  as the algebraic absorption `Q P = P`, `P Q = P`.

In Lean this is exactly a term of
`Sofic/UltraproductKazhdanTransport.UltraproductAdjointModel` for every
`omega` refining the cofinite filter.  That structure is currently a
*hypothesis* of `ultraproductKazhdanTransport` and of
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport_ultraproduct`; nothing
in the repository constructs one, so the printed road to the transport theorem
is open at precisely this point and nowhere else.

## What is already machine-checked

The rest of the printed ambient is in place, and unconditionally:

- the adjoint model in coordinates, `Ad U(xi) = U xi U*` as the doubled-index
  matrix `conjDouble U`, its invariance of the normalized Hilbert--Schmidt
  norm, and the dimension-free estimate making `g |-> Ad U_n(g)` again an
  operator-norm asymptotic representation (`UltraproductAdjointAmbient`,
  `kt_01_*`);
- `B_omega` itself as a genuine unital C-star algebra: the repository's
  `NormMatrixCStarCorona` on the doubled models, with the corona norm equal to
  the limsup of the coordinate operator norms and the absorption dictionary
  `(1 - q) p = 0 <-> q p = p and p q = p` (`kt_04_norm_eq_limsup`,
  `kt_04_absorb_of_range_le`);
- `pi(g) = [Ad U_n(g)]_omega` as an honest group homomorphism into the
  unitaries of `B_omega` (`adjointCoronaHom`, KT.05);
- finiteness of `B_omega`: the manuscript's polar-correction sentence
  (`kt_06_ultraproduct_finite`) and the stronger Mathlib-shaped instance
  `IsDedekindFiniteMonoid B_omega`, proved by Neumann inversion at each
  coordinate (`UltraproductDedekindFinite`, KT.06);
- the Kazhdan projection in an *abstract* unital C-star algebra carrying
  `pi : H ->* unitary B`, with the manuscript's own constant
  `1 - kappa^2/(2|S|)` rather than a surrogate rate, the spectral inclusion
  `sp(h) subset [-1, 1 - kappa^2/(2|S|)] cup {1}`, and the one-sided
  compression identities `Q P = P`, `P Q = P`
  (`UltraproductKazhdanProjection`, KT.07--KT.09);
- the endgame: `KT.10` (`sigma = r + (1 - Q)` is an isometry, finiteness makes
  it unitary, `sigma sigma* = P + (1 - Q)` forces `Q = P`) and `KT.11` (a fixed
  class descends to the asserted Hilbert--Schmidt vanishing along `omega`),
  with the manuscript's by-contradiction skeleton run in full
  (`UltraproductKazhdanTransport`).

So the missing datum is a single construction, not an argument: a Hilbert-space
ultraproduct of finite-dimensional inner-product spaces with a faithful action
of the corresponding operator-norm corona.  Mathlib has no completed tensor
product or ultraproduct of Hilbert spaces at the pinned revision, which is why
this is separated out rather than inlined.

## Why this is worth a node rather than a footnote

`docs/NON_MF_PROOF_LEDGER.md` records as its first headline finding that the
printed proof of `thm:kazhdan-transport` was *not* the formalized proof.  The
modules above close all of that finding except this one object, and the
distinction matters for the trust surface: the transport theorem itself is
established (by the finite-stage proof, see
[[kazhdan-asymptotic-commutant-transport]]), while the *printed route* to it
remains conditional on the construction asserted here.
