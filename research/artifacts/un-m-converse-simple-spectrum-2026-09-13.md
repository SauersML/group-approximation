# Rung (M⇐) for simple rings: the correct reformulation, the middle-regime collapse, and firewalls

Lane `un-m-converse`, 2026-09-13. Target: the open claim `stably-finite-simple-rings-have-mf-elementary-groups`
(rung (M), ring ⇒ group). Everything here is **unreviewed**. Not decided: whether stable finiteness of a simple ring
makes every `EL_N(R)` MF.

Notation as in `mf-rigidity-is-monotone-in-matrix-rank` (un-verify PASS · 7c7fdace42). `R` is a countable unital ring
with `1 ≠ 0`, `mf(R) = sup{N ≥ 2 : EL_N(R) MF}`, `rig(R) = min{N ≥ 2 : EL_N(R) MF-rigid}`, and the middle regime is
`{N : mf(R) < N < rig(R)}`. A group is MF if it embeds in the unitary group of a norm matrix corona, and MF passes to
subgroups (non-MF tex l.1080).

## 1. The reformulation in circulation is not correct

`un-open-2` §5, the node `toeplitz-ring-has-infinite-middle-mf-regime`, and synthesis part 2 §7.3 state that (M⇐)
"says exactly that a countable simple unital ring has an empty middle regime, that is `mf(R) = ∞` or `rig(R) < ∞`".
Three separate statements are being identified there, and none of the identifications holds.

1. **"Empty middle regime" is not "`mf = ∞` or `rig < ∞`".** The middle regime is empty iff `rig(R) = mf(R) + 1`, or
   `mf(R) = ∞`. The disjunction "`mf = ∞` or `rig < ∞`" also allows `rig < ∞` with a nonempty band `mf < N < rig`.
2. **(M⇐) does not give empty middle regimes.** (M⇐) is a statement about stably *finite* simple rings. It says
   nothing about stably infinite ones, where `rig(R) ≤ 2m` is known (item 1 of
   `mf-elementary-groups-force-stably-finite-simple-rings`) but the band below `rig` is open (`un-middle`,
   `el3-leavitt-3-4-has-full-mf-radical`).
3. **"`mf = ∞` or `rig < ∞` for every simple ring" does not give (M⇐).** It is satisfied by a stably finite simple ring
   with `rig(R) < ∞`, whose elementary groups become MF-rigid from some rank on. That is exactly the new non-MF
   mechanism (M⇐) rules out, and nothing on main excludes it.

**Proposition R (correct forms).** For countable simple unital `R`:
- (i) `R` not stably finite ⇒ `rig(R) < ∞` [established, `mf-elementary-groups-force-stably-finite-simple-rings`].
- (ii) (M⇐) ⟺ every countable simple stably finite `R` has `mf(R) = ∞`.
- (iii) (M⇐) ⟺ every countable simple stably finite `R` has `rig(R) = ∞` **and** an empty middle regime.

*Proof.* (ii): the open claim asks for `EL_N(R)` MF for all `N ≥ 3`; `EL_2(R) ≤ EL_3(R)` then gives `N = 2`. (iii): with
`mf < rig` (Corollary 1.1 of the MF spectrum), `mf = ∞` ⟺ `rig = ∞` and no middle. `[]`

So (M⇐) splits into a **rigidity half** (stable finiteness prevents rigidity) and a **lifting half** (no middle).
Section 2 shows the lifting half is automatic for a large class.

## 2. Theorem S: for simple groups there is no middle regime

**Theorem S.** Let `N ≥ 2` and `G = EL_N(R)`. Assume every normal subgroup of `G` is central or all of `G`.
- (a) If `φ: G → H` is a nontrivial homomorphism into an MF group, then `K = ker φ ≤ Z(G)` and `G/K` is MF.
- (b) If `Z(G) = 1`, then `G` is MF iff `G` admits a nontrivial homomorphism to an MF group. So `N` is not in the middle
  regime of `R`.
- (c) If `N` is in the middle regime, there is a subgroup `1 ≠ K ≤ Z(G)` with `G/K` MF and `G` not MF. That is, MF fails
  to lift through the central extension `1 → K → G → G/K → 1`.

*Proof.* (a) `ker φ` is normal and proper, hence central. `φ(G) ≅ G/K` is a subgroup of `H`, and MF passes to subgroups.
(b) If `Z(G) = 1`, then `K = 1` in (a), so `G ≅ φ(G)` is MF. Conversely, if `G` is MF, the identity is a nontrivial map
to an MF group, since `e_12(1) ≠ 1`. (c) Middle means not MF and not rigid. A nontrivial `φ` exists, and `K = 1` would
make `G` MF by (a), so `K ≠ 1`. `[]`

**Corollary S2 (F_2 Steinberg algebras).** Let `𝒢` be a Hausdorff ample groupoid that is minimal and effective, with
compact infinite unit space, and put `R = A_(F_2)(𝒢)`. Then for every `N ≥ 3`, `EL_N(R)` is either MF or MF-rigid.
Hence the middle regime of `R` is contained in `{2}`.

*Proof.* By `steinberg-elementary-groups-are-simple-mod-centre` (un-verify PASS · 171f0f7525), for `n ≥ 3` every normal
subgroup of `EL_n(R)` is central or everything, and `Z(EL_n(R)) ⊆ F_2^× I_n = {I_n}`. Apply Theorem S(b). `[]`

The same holds for non-Hausdorff ample `𝒢` with a simple Steinberg algebra, via
`ample-steinberg-el-simple-mod-centre-without-hausdorff` (PASS · e6fc337462). Over `F_q` with `q` odd, a middle rank
forces MF to fail to lift through some nontrivial `K ⊆ F_q^× I_N ∩ EL_N(R)`, a cyclic group of order dividing `q − 1`.

**Consequence for (M⇐).** On the class of Corollary S2, (M⇐) is equivalent to its rigidity half:
*stably finite ⇒ no `EL_N(R)`, `N ≥ 3`, is MF-rigid*, i.e. every `EL_N(R)` has a nontrivial homomorphism to an MF group.
The band question of `un-low-rank-band` also collapses there, to "MF or rigid". That band concerns `L_k(3,4)`, which is
not a Steinberg algebra, so this does not settle it.

**Model tests.**
- `L_(F_2)(1,2)`: the centre is trivial and `rig = 2`, so every `EL_N`, `N ≥ 2`, is rigid, consistent with tex l.918.
- Pestov's ring `LC(X,F_2) ⋊ Z`: `mf = rig = ∞`.
- Toeplitz–Jacobson `J`: `EL_N(J, JeJ)` is a proper non-central normal subgroup, so the hypothesis of Theorem S fails.
  Its infinite middle regime (`toeplitz-ring-has-infinite-middle-mf-regime`) is consistent.
- Grigorchuk algebra over `F_3`: centre `±1`, `EL_N/Z` simple, `EL_N` MF-rigid (PASS · e6fc337462), so no middle rank.

## 3. The decisive test object, sharpened

The Labbé ring `R_Ω = LC(Ω_U, F_2) ⋊ Z²` is minimal and free, hence effective, so Corollary S2 applies.
- It is simple and finitely generated. It is stably finite: the rank model through
  `subexponential-complexity-zd-subshift-rings-have-rank-models` plus `labbe-wang-shift-has-polynomial-pattern-complexity`
  is unreviewed, and the Følner rank model of the claim's Attempts also gives it.
- If `R_Ω` is not exactly matricial, then `EL_N(R_Ω)` is not LEF for `N ≥ 4`, by (L⇒) (PASS · 560decb046). This happens
  in particular if it is finitely presented (`lef-simple-rings-are-not-finitely-presented`).
- Then, by Corollary S2, **exactly one** of the following holds for each `N ≥ 3`:
  - `EL_N(R_Ω)` is MF. This refutes the strong converse `stably-mf-elementary-groups-force-matricial-rings`, and it would
    give an MF, non-LEF, infinite simple Kazhdan group.
  - `EL_N(R_Ω)` is MF-rigid. This refutes (M⇐), and it would give a stably finite simple ring whose Kazhdan elementary
    groups have no MF quotient by a mechanism other than one-sided compression.

So over `F_2` the decider has no third outcome.

## 4. Firewalls for a proof of (M⇐)

- **F1, finite pieces are uniformly stable.** In characteristic `p`, the unitriangular subgroups generated by elementary
  matrices with entries in a finite additive subgroup of `R` are finite groups. The restriction of an operator-norm
  asymptotic representation to a finite subgroup is close to genuine representations (Kazhdan's ε-representation theorem
  for amenable groups; recalled, not imported). So no obstruction lives on finite pieces. Any obstruction, or any construction, must
  handle infinite subgroups such as `⟨e_12(a), e_21(b)⟩`.
- **F2, root-kernel extraction dies.** The (L⇒) proof turns exact finite models into finite-index ideals through equal
  root kernels. A corona homomorphism of `EL_N(R)` with `R` simple (Theorem S hypothesis) is injective modulo the
  centre, so every root subgroup meets its kernel trivially and no ideal appears. MF models therefore yield no ring
  data by that mechanism.
- **F3, a compression alone gives nothing.** The compression criterion (tex Thm l.703) needs a strict compression of a
  Kazhdan subgroup together with a normal Kazhdan subgroup inside the defect. Every nontrivial defect built so far comes
  from a one-sided inverse, which a stably finite ring does not have. Conjugations that shrink a Kazhdan subgroup do exist
  without one-sided inverses (`k[BS(1,2)]`, claim Attempts), but there `EL_N` is LEF, so they carry no defect.
- **F4, no trace obstruction.** For these infinite simple Kazhdan groups the canonical trace is never amenable
  (`elementary-group-trace-amenable-iff-ring-residually-finite`, PASS · 10083fd646), even when the group is LEF
  (Pestov). So tex l.1349 cannot separate MF from non-MF in the middle.
- **F5, models must be genuinely asymptotic.** Simple infinite `EL_N(R)/Z` has no nontrivial finite-dimensional unitary
  representation (`minimally-almost-periodic-groups-are-not-pmf`). Any MF model is a non-exact asymptotic representation,
  and ring-induced models do not converge strongly (`ring-model-permutation-vectors-block-strong-convergence`).

## 5. Status and credits

- Proposition R, Theorem S and Corollary S2 are this lane's derivations, unreviewed. Theorem S is elementary and very
  likely folklore in substance (simple groups: "MF ⟺ nontrivial MF quotient"). Its content here is the collapse of the
  MF spectrum and the resulting split of (M⇐).
- Recalled, not imported: Kazhdan's theorem on ε-representations (F1).
- Sharpest next target: decide the rigidity half on the Labbé ring over `F_2`. Either build a nontrivial corona
  homomorphism of `EL_N(R_Ω)` from the rank model plus towers that are not ring-induced, or find a group-level compression
  with a torsion central defect inside `EL_N(R_Ω)`.
