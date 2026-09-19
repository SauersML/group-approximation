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
  - GroupApproximation/Sofic/UltraproductModelConstructionAssembly.lean
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
---

ESTABLISHED (2026-08-17).  Fix a countable group `H`, an element `s`, dimensions `d_n`, and
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

In Lean this is exactly a term of the `UltraproductAdjointModel` structure for
every `omega` refining the cofinite filter.  That structure is a *hypothesis* of
`ultraproductKazhdanTransport`, and **the hypothesis is now discharged by a
construction**:

- `UltraproductModelConstruction.nonempty_ultraproductAdjointModel` and its
  choice form `.ultraproductAdjointModel`
  (`Sofic/UltraproductModelConstructionAssembly.lean`) build the model at every
  ultrafilter `omega` with `(omega : Filter N) <= cofinite`, from property (T)
  of `Gamma`, the compression `s iota(Gamma) s^-1 <= iota(Gamma)`, positivity of
  the dimensions, and operator-norm asymptotic multiplicativity of `U` — that
  is, from the transport theorem's own hypotheses and nothing else;
- `manuscriptKazhdanTransport` (`Sofic/ManuscriptKazhdanTransport.lean`) closes
  the loop: it states Kazhdan transport in the manuscript's coordinates with no
  `ambient` argument at all and supplies it by that constructor, so the
  **printed** proof — not merely the finite-stage one — is unconditional.

Both modules sit in the root import closure (`GroupApproximation.lean` imports
`Sofic.ManuscriptKazhdanTransport`, which imports the assembly), so they are
inside what `lake build` and the kernel audit cover, and neither carries a
`sorry` or an `axiom`.  This node was written when nothing constructed the
object; that gap is closed, and the earlier note recording it as the one open
point of the printed road no longer describes the repository.

The 2026-08-16 note that `Sofic/UltraproductKazhdanTransport` did not elaborate
(unknown projections on the bundle, an unsolved goal in the descent, a
field-notation failure on `kt_11_descend`) is likewise stale: that module is
imported by the root today, alongside the three cited above.

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
The endgame — `KT.10` (`sigma = r + (1 - Q)` is an isometry, finiteness makes it
unitary, `sigma sigma* = P + (1 - Q)` forces `Q = P`) and `KT.11` (a fixed class
descends to the asserted Hilbert--Schmidt vanishing along `omega`), plus the
manuscript's by-contradiction skeleton — is in the build as well.  KT.10's
calculation itself is not new: it lives in
`Analysis/ProperIsometryFromCompression`.

The datum that was missing was a single construction, not an argument: a
Hilbert-space ultraproduct of finite-dimensional inner-product spaces with a
faithful action of the corresponding operator-norm corona.  Mathlib has no
completed tensor product or ultraproduct of Hilbert spaces at the pinned
revision, which is why it was built here by hand and separated out as a node
rather than inlined.

## Why this is worth a node rather than a footnote

`docs/NON_MF_PROOF_LEDGER.md` records as its first headline finding that the
printed proof of `thm:kazhdan-transport` was *not* the formalized proof.  The
modules above close that finding entirely.  The distinction it drew still
matters for reading the trust surface, and both halves are now on the same
side of it: the transport theorem is established by the finite-stage proof
(see [[kazhdan-asymptotic-commutant-transport]]) **and** the printed
ultraproduct route to it is formalized, ambient included.
