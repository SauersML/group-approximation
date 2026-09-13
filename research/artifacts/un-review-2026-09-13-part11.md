# UN review, part 11: the MF spectrum of simple rings

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-m-converse`, landing `6afb261048`, artifact
`research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md`.

| item | node | verdict |
|---|---|---|
| (1) | `simple-el-group-middle-regime-is-a-central-extension-effect` (Theorem S) | PASS (folklore in substance, credited) |
| (2) | `f2-steinberg-elementary-groups-have-no-middle-mf-regime` (Corollary S2) | PASS, one scope repair |
| (3) | corrected wording on `stably-finite-simple-rings-have-mf-elementary-groups` and `toeplitz-ring-has-infinite-middle-mf-regime` | PASS, one wording repair |

## 1. Theorem S

- **(a)** A nontrivial `φ` has a proper normal kernel, hence a central one. `G/K ≅ φ(G)` is a subgroup of an MF group,
  and MF passes to subgroups (tex l.1080).
- **(b)** If `Z(G) = 1`, then `K = 1` and `G` is MF. Conversely an MF `G` has the identity as a nontrivial MF map, since
  `e_12(1) ≠ I`. So "MF" equals "not MF-rigid" at `N`, and `N` is not in the middle regime.
- **(c)** Immediate.
- **Credit.** This is folklore in substance: for groups whose normal subgroups are central or everything, a nontrivial
  MF quotient with trivial centre is faithful. The node says so.

## 2. Corollary S2

- **Hausdorff statement.**
  - The reviewed `steinberg-elementary-groups-are-simple-mod-centre` (part 1) gives central-or-everything normal
    subgroups for `N ≥ 3` and `Z(EL_N(R)) ⊆ k^× I_N`. Over `F_2` that is `{I_N}`.
  - Theorem S(b) then excludes every `N ≥ 3` from the middle regime.
- **Scope repair.** The node added that "the same conclusion holds for non-Hausdorff ample `𝒢` with a simple Steinberg
  algebra" through `ample-steinberg-el-simple-mod-centre-without-hausdorff`.
  - That node (part 7) proves simplicity modulo the centre but explicitly does not identify the centre. Trivial centre
    needs `Z(A_(F_2)(𝒢)) = F_2`, since `Z(EL_N) ⊆ Z(A)^× I_N`.
  - The remark now carries that proviso.
  - The artifact's model test "Grigorchuk algebra over `F_3`: centre `±1`" rests on the same unproved identification.
    It is lane prose and not load-bearing.

## 3. The corrected reformulation

- **Empty middle.** The middle regime is empty iff `rig = mf + 1` or `mf = ∞`. That differs from "`mf = ∞` or
  `rig < ∞`", which allows a band `mf < N < rig < ∞`.
- **The open converse.** It asks `EL_N(R)` MF for all `N ≥ 3`, and `EL_2 ≤ EL_3`. So it is equivalent to `mf = ∞` on
  simple stably finite rings.
  - By `mf < rig`, `mf = ∞` ⟺ (`rig = ∞` and empty middle): if the middle is empty and `rig = ∞`, then no `N > mf`
    exists, so `mf = ∞`.
- **Statements 2 and 3 of artifact §1** are correct: the converse says nothing about stably infinite rings, and "`mf = ∞`
  or `rig < ∞`" allows a stably finite simple ring that becomes rigid.
- **The Toeplitz node's relation paragraph** now states the correct form. `J` is non-simple with a proper non-central
  `EL_N(J, JeJ)`, consistent with Theorem S.
- **Wording repair.** The Attempts bullet on the Labbé ring said each `EL_N` is "either MF (refuting the strong converse)
  or MF-rigid (refuting this claim)". One MF rank does not refute the strong converse. By monotonicity, the no-third-outcome
  dichotomy is at the level of the spectrum: either every `EL_N`, `N ≥ 3`, is MF, or all large ones are MF-rigid. The
  bullet now says so.
- **Labbé ring hypotheses.** The groupoid `Z² ⋉ Ω_U` is Hausdorff, ample, minimal and free (hence effective), with
  compact infinite unit space, so S2 applies.
  - Non-LEF from non-matriciality goes through the reviewed (L⇒) nodes.
  - Stable finiteness goes through the Følner rank model.
