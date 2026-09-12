---
rg: 2
id: relative-commutant-collapse-for-sl2-pair
kind: claim
title: In any matrix ultraproduct the relative commutant of L(SL2(Z)) equals that of L(SL2(Z[1/2]))
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  approximate-collapse-for-kt-compressor: that is the same statement for the EL_r(F_q[x]) compressed Kazhdan copy; this is the explicit arithmetic pair SL_2(Z) <= SL_2(Z[1/2]), where commensuration and character rigidity are available.
  iwahori-local-global-defect-question: that is the representation-variety (flexible stability) form; this is the intrinsic II_1-factor form, weaker to state and possibly easier because it never leaves the ultraproduct.
---

Let `M = prod_U M_(d_n)` be a tracial matrix ultraproduct and
`pi : SL_2(Z[1/2]) -> U(M)` any trace-preserving (regular-trace)
representation, `pi(SL_2(Z))'' = L(SL_2(Z))`, `pi(SL_2(Z[1/2]))'' =
L(SL_2(Z[1/2]))`.  Then

```text
pi(SL_2(Z))' cap M  =  pi(SL_2(Z[1/2]))' cap M.                         (RCC)
```

Equivalently, no unitary of `M` commutes with `L(SL_2(Z))` but fails to
commute with `L(SL_2(Z[1/2]))`. This commutant equality does not itself
assert a quantitative spectral gap. By
`arithmetic-hnn-nonhyperlinearity-equals-global-collapse`, it is
equivalent to nonhyperlinearity of the centralizer HNN group, scalar
non-relative-embeddability, and exact quasi-regular leak exclusion.
These assertions remain OPEN.

## Attempts

- **Commensuration.**  `SL_2(Z)` is commensurated by `SL_2(Z[1/2])` with
  Schlichting completion `SL_2(Q_2) supseteq SL_2(Z_2)`; the inclusion
  `L(SL_2(Z)) subseteq L(SL_2(Z[1/2]))` is the associated Hecke inclusion.
  Popa's spectral-gap/mixing criteria for such inclusions are the tool.
- **Character rigidity boundary.** The known hyperfinite stability
  statements concern representations whose limiting actor algebra is
  amenable. The canonical actor algebra here is nonamenable. They
  therefore do not correct arbitrary tuples in this claim. The
  amenability of the auxiliary commutant alone does not decide which
  actor representations those stability theorems cover.
- **Relation to flexible stability.**  Flexible HS-stability of
  `SL_2(Z[1/2])` implies `(RCC)` (correct microstates, then co-density);
  `(RCC)` may be strictly weaker since it only asks about the commutant of a
  fixed subalgebra, not correction of the whole representation.
- **Relatively-icc form (2026-08-21).**  For group von Neumann algebras,
  `L(H)' cap L(G) = C` when the subgroup `H` is relatively icc in `G` (every
  `g != e` has infinite `H`-conjugacy class); `SL_n(Z)` is relatively icc in
  `SL_n(Z[1/p])` (a non-central `g` has INFINITE-INDEX `SL_n(Z)`-centralizer
  -- its centralizer is the `Z`-points of a proper Zariski-closed subgroup
  and `SL_n(Z)` is Borel dense, see `arithmetic-pair-ultrapower-no-leak-proof`
  Step 2 -- so infinite conjugacy class; the earlier "finite centralizer"
  was false, e.g. `e_12(1)` centralizes `e_12(Z)`; corrected 2026-08-21).
  The exact identity is `L(C)' cap L(A)=L(Z(A))`; rank two has the
  nontrivial center `{I,-I}`, so these full group algebras are not
  irreducible II_1 subfactors. `(RCC)` asks that the relative
  commutant, on passing from the actor algebra to the ambient
  matrix ultraproduct `M`, must not acquire anything outside `B' cap M`.
  In a canonical HNN embedding the subgroup commutant contains the
  stable letter and is nontrivial. The content is its inclusion in
  the actor commutant, which that stable letter violates. No assertion
  about the complete group centralizer is needed.
- **Entropy boundary.** Entropy bounds on extensions do not by
  themselves exclude free-group-factor subalgebras in a commutant.
  The CE model `L(A) tensor L(F_2)` contains such a factor in both
  commutants and has no leak from that factor. The corrected
  discussion in `sl3-pair-relative-commutant-route` keeps the focus
  on the actor's action on the commutant.
- **Proper proximality.**  `SL_2(Z)` (and `SL_3(Z)`) are properly proximal
  (Boutonnet--Ioana--Peterson, arXiv:1809.01881), so `L(SL_2(Z))` is
  solid/rigid and its commutants are controlled; a properly-proximal
  criterion for relative commutants inside a matrix ultraproduct (as opposed
  to a crossed product) is the missing form.  Alekseev--Thom Open Problem
  6.2 is exactly this collapse in general; `(RCC)` is its most explicit
  instance, so it is genuinely open, not a known theorem.
- **What a counterexample is.**  A faithful `pi` and a unitary `k in M`
  with `[k, pi(SL_2(Z))] = 0` but `[k, pi(diag(2,1/2))] != 0`; such a `k`
  would make the HNN group hyperlinear and would refute both `(RCC)` and,
  through it, DV-style stability.
- **Explicit falsification gate.**
  `coset-bernoulli-ce-refutes-relative-commutant-collapse` shows that Connes
  embeddability of

  ```text
  L^infinity(K^(A/C)) rtimes A,
  A=SL_2(Z[1/2]), C=SL_2(Z),
  ```

  would refute `(RCC)`: the coordinate at `C` commutes with `C` but is moved
  by every element of `A-C`.  This is conditional, because soficity/CE of
  this generalized Bernoulli action with nonamenable stabilizer is not known.
