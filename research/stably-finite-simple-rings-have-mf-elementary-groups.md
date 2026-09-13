---
rg: 2
id: stably-finite-simple-rings-have-mf-elementary-groups
kind: claim
title: Is stable finiteness of a simple ring enough for its elementary groups to be MF in every rank?
distinct_from:
  mf-elementary-groups-force-stably-finite-simple-rings: that proves stable finiteness is NECESSARY for stably MF elementary groups; this asks whether it is SUFFICIENT
  stably-mf-elementary-groups-force-matricial-rings: that asks for the opposite strengthening, that stably MF elementary groups force exact matricial embeddability; the two open claims bracket the true ring-level condition
---

**OPEN.** Let `R` be a countable simple unital ring that is stably finite. Is `EL_N(R)` MF for every `N >= 3`?
The weaker form asks whether `EL_N(R)` has a nontrivial MF quotient for every `N`.

Either answer sharpens the UN boundary (`research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md`
§0):
- **If true.** For simple rings, stable MF of the Kazhdan groups `EL_N(R)` is exactly stable finiteness. That is
  a ring-level characterization of operator-norm approximability for this class. With
  `mf-elementary-groups-force-stably-finite-simple-rings` it would be an equivalence.
- **If false.** Some simple stably finite ring kills MF approximations of its elementary groups by a mechanism
  other than one-sided compression. That would be a new non-MF mechanism.

## Attempts

- **Through exact matricial models (partial).** `exactly-matricial-rings-have-lef-general-linear-groups` proves
  the conclusion, with LEF, for exactly matricial rings. It does not reach every stably finite simple ring.
  `stably-finite-algebras-need-not-be-linear-sofic` (Greenfeld arXiv:2210.11650, imported by `un-prior-art`)
  gives finitely generated stably finite algebras that are not even linear sofic, though not simple. So stable
  finiteness alone does not supply ring models, and a proof must build MF models of `EL_N(R)` that are not
  induced by ring homomorphisms.
- **Evidence from Z-subshift rings (positive, non-simple class).** The peer root
  `subshift-elementary-mf-iff-word-edges-lie-on-cycles` states, for every subshift `X` and `n >= 4`:
  `EL_n(LC(X,F_q) ⋊ Z)` is MF ⟺ LEF ⟺ the ring is directly finite. In that class even direct finiteness
  suffices, which is the pattern this claim predicts.
- **Win-win test object: aperiodic Z^2 subshifts of finite type.** Let `Ω` be a free minimal Z^2 SFT with no
  periodic point and `R_Ω = LC(Ω,F_q) ⋊ Z^2`.
  - `R_Ω` is simple, finitely generated and stably finite: it embeds unitally in a rank ultraproduct via the
    Følner rank model of `free-minimal-subshift-elementary-groups-are-simple-kazhdan`, and rank ultraproducts
    are stably finite.
  - Its elementary groups are Kazhdan, simple mod centre and linear sofic.
  - The topological full group embeds in the units, `g ↦ Σ_i u^(γ_i) χ_(Y_i)`. So if `R_Ω` were exactly
    matricial, the full group would be LEF, which would bear on the open `labbe-shift-derived-full-group-is-lef`.
  - Permutation models are excluded by the aperiodic-SFT Theorem A of
    `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`. Linear (non-permutation) exact models are not
    excluded: integer-valued shift-invariant pattern dimensions exist, and only the exact commutation
    `U_1 U_2 = U_2 U_1` across block isomorphisms is unconstrained so far.
  - **If `R_Ω` is not exactly matricial**, then `EL_n(R_Ω)` decides between this claim and
    `stably-mf-elementary-groups-force-matricial-rings`: if it is MF it refutes that claim's strong form; if it
    is not MF it refutes this claim.
- **Through the C*-algebraic MF problem (no mechanism).** MIP* = RE yields a stably finite non-MF C*-algebra
  (`non_mf_groups_exist.tex` l.315–320). Transferring that to a simple ring `R` and to the non-unitary groups
  `EL_N(R)` needs a way to turn operator-norm models of `EL_N(R)` into models of `R`, and none is known.
- **Through the compression criterion (dies).** Every compressor built so far comes from a one-sided inverse in
  some `M_m(R)`. Compressors alone do not kill MF: `k[BS(1,2)]` is exactly matricial, yet `u k[y] u^-1 = k[y^2]`
  gives `u EL_3(k[y]) u^-1 < EL_3(k[y])`. What matters is a *full defect idempotent*, and in a stably finite
  simple ring every one-sided inverse is two-sided at every matrix size.
- **Correct reformulation, and a split into two halves (lane `un-m-converse`, unreviewed).** Artifact
  `research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md` §1 corrects the reading "this claim says a simple ring
  has an empty middle regime, that is `mf(R) = ∞` or `rig(R) < ∞`". "Empty middle regime", "`mf = ∞` or `rig < ∞`" and this
  claim are three inequivalent statements. The correct form is: this claim ⟺ every simple stably finite `R` has
  `mf(R) = ∞` ⟺ every simple stably finite `R` has `rig(R) = ∞` (**rigidity half**) and an empty middle regime
  (**lifting half**).
- **The lifting half is automatic on F_2 Steinberg algebras (unreviewed).**
  `simple-el-group-middle-regime-is-a-central-extension-effect` shows that if `EL_N(R)` is simple modulo a trivial centre,
  "MF" and "not MF-rigid" coincide at `N`. With `steinberg-elementary-groups-are-simple-mod-centre` this gives
  `f2-steinberg-elementary-groups-have-no-middle-mf-regime`: over `F_2`, for minimal effective `𝒢`, each `EL_N`,
  `N ≥ 3`, is MF or MF-rigid. On that class this claim reduces to its rigidity half.
  - The Labbé ring over `F_2` is in the class. If it is not exactly matricial, each `EL_N` over it (`N ≥ 4`) is non-LEF,
    and is either MF or MF-rigid. By monotonicity (`mf-rigidity-is-monotone-in-matrix-rank`), either all of them are MF (refuting the strong converse) or all large ones are MF-rigid (refuting this claim), with no third outcome (wording repair by un-verify, 2026-09-13).
  - Over `F_q`, `q` odd, a middle rank would force MF to fail to lift through a central subgroup of `F_q^× I_N`.
- **Firewalls for a proof (artifact §4, unreviewed).**
  - F1: in characteristic `p`, finite pieces are uniformly stable (Kazhdan ε-representations, recalled), so any
    obstruction or construction must handle infinite subgroups such as `⟨e_12(a), e_21(b)⟩`.
  - F2: the (L⇒) root-kernel extraction dies. A corona homomorphism of a simple-mod-centre `EL_N(R)` meets every root
    subgroup trivially, so no ideal appears.
  - F3: a compression without a torsion central defect gives nothing, as `k[BS(1,2)]` shows.
  - F4: the canonical trace is never amenable here, even when `EL_N` is LEF, so tex l.1349 cannot separate the cases.
  - F5: minimally almost periodic, so MF models must be genuinely asymptotic, and ring-induced models do not converge
    strongly.

**Review (un-verify, 2026-09-13) of the un-m-converse Attempts: PASS, one wording repair.** The correction is right: "empty middle regime", "`mf = ∞` or `rig < ∞`" and this claim are inequivalent, and this claim ⟺ `mf(R) = ∞` for every simple stably finite `R` ⟺ `rig = ∞` and an empty middle regime. The Labbé test-object dichotomy is now phrased at the level of the whole spectrum. See `research/artifacts/un-review-2026-09-13-part11.md` §3.
