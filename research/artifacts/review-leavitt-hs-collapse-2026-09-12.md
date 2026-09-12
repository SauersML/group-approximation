# Independent review: the Khanh collapse of the Leavitt–Steinberg fork

Reviewer lane `reviewer`, 2026-09-12. This is an adversarial review of the claims that turn the Leavitt–Steinberg fork into "`L^×` is normalized-HS stable iff `L^×` is nonhyperlinear", where `L = L_(F_2)(1,2)`:

- `leavitt-unit-hs-stable-iff-nonhyperlinear` and `leavitt-unit-hs-stable-iff-nonhyperlinear-proof` (landed f7200406e);
- `steinberg-hs-stability-equals-nonhyperlinearity`, its proof route, and the 2026-09-12 update 89511e146;
- `leavitt-steinberg-hs-stability-fork` (update 448ad75f7) and `leavitt-steinberg-hs-unstable` (update cb311d832);
- `leavitt-unit-hyperlinear-iff-projective-hs-model` and `leavitt-unit-projective-hs-lift-proof`;
- the inputs:
  - `leavitt-steinberg-map-iso-from-rank-three` (Khanh Theorem 5.4);
  - `leavitt-unit-group-finitely-presented` (Khanh Theorem 6.1);
  - `binary-leavitt-unit-group-is-simple`;
  - `binary-leavitt-unit-group-is-minimally-almost-periodic`;
  - `leavitt-gl-equals-el-and-perfect-unit-group`;
  - `pointwise-hs-stability-from-no-hyperlinear-quotient`.

## Verdicts

| claim | verdict | trust surface |
| --- | --- | --- |
| `leavitt-unit-hs-stable-iff-nonhyperlinear` | **PASS** | Khanh Theorem 5.4 (read, not refereed); simplicity via Lean theorem, axiom closure not audited here |
| `steinberg-hs-stability-equals-nonhyperlinearity` | **PASS** for this ring | its general 3 ⟹ 2 step cites Thom's central-quotient permanence, not re-verified here; moot after Khanh because `Z(U) = 1` |
| `leavitt-unit-hyperlinear-iff-projective-hs-model` | **PASS** | Khanh Theorem 4.4 at rank one (`H_2(L^×;Z) = 0`) |
| `binary-leavitt-unit-group-is-minimally-almost-periodic` | **PASS** | independently confirmed by Malcev plus simplicity (Section 3) |
| `pointwise-hs-stability-from-no-hyperlinear-quotient` | **PASS** | none |

**Bottom line.** The collapse is sound. After Khanh, `St_5(L)`, `EL_4(L)` and `L^×` are one simple, finitely presented, minimally almost periodic group. For that group, normalized-HS stability, in the strict sense or the flexible sense (they coincide here), is equivalent to nonhyperlinearity, and instability is equivalent to hyperlinearity. Instability is therefore exactly a hyperlinear nonsofic group, i.e. Q3.4. Neither side is decided.

**Normalized versus plain HS.** Every equivalence here is for the normalized trace metric `‖T‖_2 = tr(T*T)^(1/2)` with `tr` normalized by the dimension. That is the metric of tracial ultraproducts. None of it transfers to the unnormalized Frobenius norm. There, vanishing defects bound the operator-norm defect, and the relevant limit object is not a tracial ultraproduct. The graph asserts nothing about that notion. Strict versus flexible (Dogon–Vigdorovich's "HS stable" is flexible, Becker–Lubotzky's is strict) makes no difference for `L^×`: every genuine finite-dimensional representation is trivial, so a flexible correction is a compression of `1`.
