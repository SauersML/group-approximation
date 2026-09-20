---
rg: 2
id: relative-elementary-quotients-inherit-flexible-hs-stability
kind: claim
title: Flexible HS stability of E_n over a finitely generated ring passes to its quotient by the relative elementary subgroup of any finitely generated ideal
distinct_from:
  flexible-hs-stability-passes-to-kazhdan-kernel-quotients: that needs the kernel itself to have property (T); here the kernel E_n(S,I) is usually not Kazhdan and need not be finitely generated as a group, and relative rigidity comes from property (T) of E_n of the fibre-product ring S x_(S/I) S.
  flexible-p-stability-passes-to-fg-normal-quotients: that is Alekseev--Thom's permutation statement for kernels finitely generated as groups; this is the unitary normalized-HS statement for kernels that are only finitely normally generated, namely by the root elements of a finitely generated ideal.
  relative-elementary-fng-iff-level-ideal-fg: that says E_n(S,I) is finitely normally generated exactly when I is finitely generated; this transports flexible HS stability across that kernel, which finite normal generation alone does not do in the Hilbert--Schmidt setting.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that derives residual finiteness from stability of one group; this transports stability itself from E_n(S) to E_n(S)/E_n(S,I).
---

**ESTABLISHED** (proof route `relative-elementary-quotient-flexible-descent-proof`).

Let `S` be a finitely generated unital associative ring, `n >= 3`, and `I` a two-sided ideal of `S`
that is finitely generated as a two-sided ideal. Write `E_n(S,I)` for the normal closure in `E_n(S)`
of `{x_ij(a) : a in I, i != j}`, and put

```text
Q_I = E_n(S) / E_n(S,I).
```

If `E_n(S)` is flexibly Hilbert--Schmidt stable in the Dogon--Vigdorovich sense (every asymptotic
representation `σ_k -> U(d_k)` in normalized HS norm is pointwise close to corners `P λ_k P*` of
genuine representations `λ_k : E_n(S) -> U(D_k)`, `D_k >= d_k`), then so is `Q_I`.

The proof keeps dimension control. If the correcting representations of `E_n(S)` can be chosen with
`D_k/d_k -> 1`, then so can those of `Q_I`. So the statement holds verbatim for the ratio-one
variant used in `el-r-polynomial-vertex-not-flexibly-hs-stable`.

**Mechanism.**
- Let `D = S x_(S/I) S` be the fibre-product ring. It is finitely generated, because `I` is, so
  `E_n(D)` has property (T) (`ershov-jaikin-kassabov-steinberg-groups-have-property-t`).
- `E_n(D)` acts on Hilbert--Schmidt operators by `T -> λ(p_1 g) T λ(p_2 g)*`.
- The stable corner projection `p` is almost invariant under a finite generating set.
- The Kazhdan projection of `p` is a self-adjoint intertwiner `T` of `λ`. Its range is fixed
  pointwise by `E_n(S,I)`, and `||T - p||_2 <= δ/κ`.
- The spectral projection `1_(T > 1/2)` is therefore a subrepresentation of `λ` that factors
  through `Q_I` and lies within `2δ/κ` of `p`.
- A trivial summand of dimension at most `d(2δ/κ)^2` absorbs the defect.

This is the corner version of the wave-22 kernel bound `(QN)` for the Leavitt cone half, which was
recorded on a side branch for one ideal. There it was stated for representations that are almost
trivial on the whole space. Here it is stated for an arbitrary ring and ideal, and for corners of
larger representations, which is what stability needs.

## Consequences

- With `hyperlinear-flexibly-hs-stable-group-is-residually-finite`: if `E_n(S)` is flexibly HS
  stable, then every `Q_I` with `I` a finitely generated ideal is residually finite or not
  hyperlinear.
- `universal-lattice-flexible-stability-forces-nonhyperlinear-group` is the case where `S/I` is
  simple and infinite. There `Q_I` has no nontrivial finite-dimensional unitary representation, so
  flexible stability of `E_n(S)` makes `E_n(S/I)` non-hyperlinear.
- **Contrapositive screen.** A single finitely generated ideal `I` for which `Q_I` is hyperlinear
  and not flexibly HS stable refutes flexible HS stability of `E_n(S)`. For `S` a free algebra,
  every finitely presented ring on the same number of generators supplies such a test.
