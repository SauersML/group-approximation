---
rg: 2
id: kazhdan-elementary-approximation-type-mirrors-ring-type
kind: claim
root: true
title: UN root — over a simple ring, the approximation type of the Kazhdan elementary groups mirrors the matricial type of the ring (LEF iff exactly matricial, linear sofic iff rank model, MF iff stably finite)
---

**OPEN (UN program root).** Let `R` be a countable simple unital ring. For finitely generated `R`, every
`EL_N(R)` with `N >= 3` is Kazhdan (`elementary-groups-over-fg-rings-have-property-t`). The claim is:

- **(L)** `EL_N(R)` is LEF for every `N` iff `R` embeds unitally in an algebraic ultraproduct
  `prod_omega M_(d_k)(F_k)` of matrix algebras over fields (*exactly matricial*).
- **(Σ)** Suppose `R` is an algebra over a finite field `k` with centre `k`. Then
  `S_N = EL_N(R)/(EL_N(R) ∩ k^x I)` is `k`-linear sofic for every `N >= 2` iff `R` has a unital rank model
  over `k`.
- **(M)** `EL_N(R)` is operator MF for every `N` iff `R` is stably finite, iff `[R]` is not paradoxical in
  `V(R)`.

**What it unifies.**
- The Pestov 9.1 answer (`infinite-simple-kazhdan-hyperlinear-group`) is (L⇐) at `LC(X,F_q) ⋊ Z`.
- The non-MF paper's Leavitt theorem (`non_mf_groups_exist.tex` Cor l.1016) is (M⇒) at `L_k(1,2)`.
- Both rings are Steinberg algebras of minimal effective ample groupoids:
  `leavitt-path-algebras-are-steinberg-algebras` and `crossed-products-are-transformation-steinberg-algebras`.
- Elementary groups over such algebras are uniformly simple modulo centre
  (`steinberg-elementary-groups-are-simple-mod-centre`). Only the type of the unit decides the approximation
  type.
- The sharpest mirror pair is `EL_3(LC(X,F_q) ⋊ Z)/Z` (LEF) against
  `boundary-action-elementary-simple-kazhdan-not-mf` (no MF quotient). Same construction; the dynamics is
  measure-carrying in one and paradoxical in the other.

**Established halves.**
- (L⇐): `exactly-matricial-rings-have-lef-general-linear-groups`.
- (Σ⇐): `rank-modelled-simple-rings-give-linear-sofic-projective-el`.
- (M⇒): `mf-elementary-groups-force-stably-finite-simple-rings` with
  `simple-ring-stably-finite-iff-unit-not-paradoxical`.

**Open converses** (route `kazhdan-approximation-ladder-from-three-converses`):
- (L⇒): `lef-el-groups-force-exactly-matricial-simple-ring`;
- (Σ⇒): `linear-sofic-el-groups-force-rank-model`;
- (M⇐): `stably-finite-simple-rings-have-mf-elementary-groups`.

A counterexample to a converse is itself a new object.

**The middle rung is realised (unreviewed).** `simple-kazhdan-linear-sofic-non-lef-group-exists` (un-sofic-not-lef,
9ef8948121): `EL_N(LC(X,F_q) ⋊ Γ_p)/Z`, over a free minimal subflow of the Abels–Prüfer group, is infinite, simple,
Kazhdan, `F_q`-linear sofic and not LEF.
- Its ring has rank models but is not exactly matricial: otherwise `GL_N` would be LEF, but it contains `Γ_p`.
- So it is consistent with (L) and (Σ), and it is a live test ring for (L⇒).
- Together with (M⇐), it would give an MF but non-LEF simple Kazhdan group.

**Paradox-side families (unreviewed).**
- `paradoxical-cantor-actions-give-simple-kazhdan-not-mf` (un-boundary-families, 0e439a2b56): a minimal topologically
  free Cantor action with a finite generating clopen family and `2[X] <= [X]` gives infinite simple Kazhdan groups
  with no MF quotient. Instances:
  - `free-product-finite-groups-boundary-simple-kazhdan-not-mf`;
  - `p-adic-projective-line-elementary-simple-kazhdan-not-mf`;
  - `boundary-action-elementary-simple-kazhdan-not-mf`. Correctness note: there `k` must be finite for finite
    generation and (T).
- Open: `hyperbolic-group-cantor-model-simple-kazhdan-not-mf`.

**Along the Pestov end, the approximation type is constant but the group is not** (un-open-5, unreviewed):
- `marked-subshift-elementary-group-determines-language` and `continuum-many-simple-kazhdan-lef-groups` (bec8c05389);
- `every-turing-degree-is-a-simple-kazhdan-lef-word-problem` (7e6f1c8002).

The dynamics lives in the isomorphism type and the word problem, not in the approximation rung. Open:
`subshift-elementary-group-isomorphism-forces-orbit-equivalence` and
`subshift-elementary-group-lef-growth-tracks-complexity`.

Blueprint: `research/artifacts/un-blueprint-2026-09-13-part1.md`.

## Attempts

- **F1. Simplicity is essential.** `Z[L^x]` is stably finite, yet its `EL_n` are not MF
  (`stably-finite-group-ring-with-non-mf-elementary-groups`). A finitely generated stably finite algebra need
  not be linear sofic (`stably-finite-algebras-need-not-be-linear-sofic`). So none of (L), (Σ), (M) extends to
  non-simple rings.
- **F2. Centre in (Σ).** The adjoint model kills exactly the scalars of the centre. With a larger centre `K`,
  soficity is over `K`.
- **F3. "Every N" in (M).** One-sided transport needs rank `>= 2p(R)`, where `p(R)` is the paradoxical level.
  Below that, MF quotients may survive (`el-n-mf-quotient-below-twice-paradoxical-level-exists`). A fixed-rank
  version needs new mechanisms.
- **F4. Measure side, (M⇐).** Proving that invariant measures make Cantor crossed-product algebras stably
  finite contains Kaplansky stable finiteness over the coefficient field
  (`measure-side-stable-finiteness-contains-char-p-kaplansky`). Any proof of (M⇐) for crossed products must
  pass through, or around, char-`p` Kaplansky.
  - **Groupoid Tarski** (un-tarski, 991380d00d, unreviewed): rank function ⇒ stably finite ⇒ not paradoxical ⟺
    invariant probability measure (`algebraic-tarski-for-steinberg-algebras`). Measure ⇒ rank function holds
    in characteristic 0 (`invariant-measure-gives-rank-function-in-char-zero`) and is open in general
    (`invariant-measure-gives-rank-function-any-field`).
  - **Almost unperforated `S(𝒢)`**: the paradox branch reaches rank 2
    (`unperforated-paradox-makes-steinberg-purely-infinite`).
  - The type semigroup does not mention `k`. So which branch a groupoid falls into is field-independent,
    while its ring consequences are not.
- **F5. Characteristic zero is not excluded.** The rational Weyl algebra is exactly matricial
  (`weyl-algebra-is-exactly-matricial`), but it is not finitely generated, so there is no (T) payoff there.
- **F6. Plain soficity is off the ladder.** d-ary Leavitt elementary groups over finite fields are nonsofic
  (`d-ary-leavitt-groups-nonsofic-over-finite-fields`), consistent with the failure end. Sofic versus linear
  sofic in the middle is `free-minimal-subshift-elementary-groups-are-sofic`.
- **F7. Calibration table** (un-calibration, 8d27ba78e6).
  - **The rungs stay distinct even with (T).** `group-ring-lef-iff-group-lef-iff-elementary-group-lef` gives,
    for `F_q[Γ]` with `Γ` amenable and not LEF, a stably finite ring with a faithful rank model whose Kazhdan
    `EL_n` is linear sofic and not LEF. It is not simple.
  - **Matriciality over the base field is the wrong notion.** `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q`:
    no characteristic-0 matrix model, yet a model over `F_p`. So (L) uses varying fields.
  - **Towers without expansiveness give LEF groups but no (T):** `odometer-crossed-product-elementary-groups-not-kazhdan`.
  - **Rank four, any ring** (reported by un-calibration, not re-read here): tex Prop l.1072 says that for every
    countable ring of characteristic `p`, `EL_4(R)` MF ⇒ `R` directly finite.
- **F8. Unit-group face** (un-k1-homology, 5c83d35b84, unreviewed). The same dichotomy appears one level up, at
  the maximal MF quotient of `GL_n(A_k(𝒢))`:
  - with (PI) local compressibility it is `K_1` and the radical is the commutator subgroup
    (`purely-infinite-steinberg-gl-max-mf-quotient-is-k1`);
  - when the algebra is exactly matricial the radical is trivial (`steinberg-gl-mf-radical-is-commutator-or-trivial`),
    and the two cases are mutually exclusive but not exhaustive;
  - for irreducible SFT Leavitt algebras there is an explicit formula
    (`irreducible-sft-leavitt-gl-max-mf-quotient-formula`), read homologically through Matui
    (`matui-sft-groupoid-homology-is-k-theory`);
  - the general low-degree homology form is open (`steinberg-gl-max-mf-quotient-is-low-degree-homology`).
- **F9. The coarse face** (un-open-7, 47fd74e1a7, unreviewed). Two facts about the ladder that use no
  operator algebra.
  - **RF-rigidity is free, on both sides.** `un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical`:
    `EL_n(R)` is perfect and has no nontrivial finite quotient, and every homomorphism from `EL_n(R)/Z`
    to a residually finite group is trivial, from simplicity of the central quotient alone. With
    `RF ⊆ LEF ⊆ MF`, the whole dichotomy sits in the gap `RF ⊊ MF`, which is why the non-MF paper states
    its theorems for MF targets and not for finite or residually finite ones.
  - **A quasi-isometry invariant separates the ends.** `lef-infinite-simple-groups-are-qi-rigid`: a
    finitely generated infinite simple LEF group is not finitely presented, hence is quasi-isometric to
    no finitely presented group. Every measure-side rung is such a group, while the non-MF paper supplies
    finitely presented Kazhdan examples with no MF quotient. Unlike (L), (Σ) and (M), this separation
    survives every quasi-isometry.
  - Open: whether a paradox-side rung is itself finitely presented
    (`paradox-side-elementary-group-is-finitely-presented`), which would move the separation inside the
    ladder; and whether LEF growth separates measure-side rungs from each other
    (`elementary-group-lef-growth-separates-subshifts`).
- **Flagship instance, ESTABLISHED.** `free-group-cantor-elementary-group-lef-iff-invariant-measure`, route
  `free-group-cantor-el-lef-iff-invariant-measure-proof`. Its inputs passed review; the assembly is unreviewed.
  - **Setting:** minimal topologically free free-group Cantor systems with finitely generated crossed product
    over `F_q`.
  - **Result:** (L) and (M) collapse to one dynamical dichotomy. `S_N` is LEF for all `N >= 3` iff an invariant
    measure exists; otherwise there is no MF quotient for `N >= 2n`.
  - **Open:** the band `3 <= N < 2n`.
