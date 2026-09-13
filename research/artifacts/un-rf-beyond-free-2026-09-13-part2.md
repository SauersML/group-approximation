# Invariant measure versus finite models beyond free groups (part 2 of 2)

Lane `un-rf-beyond-free`, 2026-09-13. Written proofs, UNREVIEWED. Notation and Lemmas 1–3, Proposition S and
the class `𝔑` are in part 1.

## 6. Residually finite Toeplitz subshifts over every residually finite group

Theorem Z shows that for groups containing `Z^2` an invariant measure does not force finite models. The
LEF side of the UN program only needs *some* suitable action, though. This section builds, for every finitely
generated infinite residually finite `Γ`, a Toeplitz subshift that is RF, including for Kazhdan `Γ`.

**Theorem T.** Let `Γ` be a finitely generated infinite residually finite group. There is `x ∈ {0,1}^Γ`
whose orbit closure `X_Γ` is:
1. minimal, a Cantor space, and free as an action (every point of the orbit of `x` has trivial stabilizer),
   hence topologically free;
2. residually finite in the sense of Kerr–Nowak;
3. carries an invariant Borel probability measure.

**Construction.**
- Fix a chain of finite-index normal subgroups `Γ = Γ_0 >= Γ_1 >= …` with `∩ Γ_m = {e}`, finite
  symmetric `B_1 ⊆ B_2 ⊆ …` exhausting `Γ`, and an enumeration `Γ = {g_1, g_2, …}`.
- Passing to a subsequence of the chain (the intersection stays trivial), assume
  `d_m := [Γ_(m-1) : Γ_m] >= max(m + 2, 2|B_(m-1)| + 1)` for all `m >= 1` (`B_0 = {e}`).
- Level `m = 1, 2, …`. The unique *hole* of level `m-1` is a single `Γ_(m-1)`-coset `C_(m-1)` (`C_0 = Γ`). Split
  it into its `d_m` cosets of `Γ_m` and decide:
  - one subcoset is the new hole `C_m`, chosen to avoid the at most `m` subcosets containing `g_1, …, g_m`;
  - one other subcoset is valued `1`;
  - every remaining subcoset (at least one) is valued `0`.
- `x(h)` is the value of the subcoset containing `h` at the first level where `h` leaves the hole. Every
  `h = g_j` leaves by level `j`, so `x` is defined everywhere.

**Facts.**
- (F1) The skeleton `S_(<=m) = Γ \ C_m` is a union of `Γ_m`-cosets and `x` is constant on each.
  (Level-`m'` values are constant on `Γ_(m')`-cosets, which are unions of `Γ_m`-cosets for `m' <= m`.)
- (F2) `x` takes both values on `C_m`: at level `m+1` it contains a `1`-subcoset and a `0`-subcoset.

*Proof of 1 (minimal).* Given finite `W`, pick `M` with `W ⊆ S_(<=M)`. For `γ ∈ Γ_M` and `w ∈ W`,
`γw ∈ Γ_M w` by normality, so `(γ^(-1)·x)(w) = x(γw) = x(w)`. The return set of `x|_W` contains the
finite-index subgroup `Γ_M`, hence is syndetic. So `x` is almost periodic and `X_Γ` is minimal
(Gottschalk–Hedlund).

*Proof of 1 (free).* Suppose `g·x = x`, i.e. `x(g^(-1)h) = x(h)` for all `h`. Fix `m`. Left multiplication by
`g^(-1)` sends `Γ_m`-cosets to `Γ_m`-cosets and transports `x`. So it sends the non-constant coset `C_m` (F2) to a
non-constant coset, which must be `C_m` by (F1). Then `Γ_m g^(-1) c = Γ_m c` for `C_m = Γ_m c`, so `g ∈ Γ_m`.
This holds for every `m`, so `g = e`. The orbit of `x` is dense, so free points are dense and `Fix(g)` has empty
interior for `g ≠ e`. `X_Γ` is infinite and minimal, hence perfect: a Cantor space.

*Proof of 2 (RF).* Use Proposition S. Let `W` be finite, `L_W = L_W(X_Γ)`.
- Every `p ∈ L_W` occurs in `x` at some `g` with `gW ⊆ S_(<=m(g))`; there are finitely many. Pick `M` with
  `M >= m(g)` for all of them and `W ⊆ B_M`.
- Define the periodic configuration `p_M(h) = x(h)` on `S_(<=M)` and `p_M(h) = 0` on `C_M`. By (F1) it is
  `Γ_M`-invariant, so its orbit `O` is finite.
- **`O ⊆ (X_Γ)_W`.** Fix `g`. Among `w ∈ W`, the *hole positions* are those with `gw ∈ C_M`; there are at most
  `|W|`. For `γ ∈ Γ_M`:
  - skeleton positions: `γgw ∈ Γ_M gw`, so `x(γgw) = x(gw) = p_M(gw)`;
  - hole positions: `γ̄ ↦ Γ_(M+1)γgw` is a bijection from `Γ_M/Γ_(M+1)` onto the `d_(M+1)` subcosets of `C_M`.
    So exactly two classes `γ̄` put `γgw` in the `1`-subcoset or the new hole.
  - At most `2|W| <= 2|B_M| < d_(M+1)` classes are bad, so some `γ` puts every hole position in a
    `0`-subcoset. For it, `x(γgw) = p_M(gw)` for all `w ∈ W`.
  - So every `W`-pattern of `p_M` is a pattern of `x`, i.e. lies in `L_W`.
- **Coverage.** Each `p ∈ L_W` is the pattern of `x` at some `g` with `gW ⊆ S_(<=M)`, which is the pattern of
  `p_M` at `g`.
Proposition S gives RF. ∎

*Proof of 3.* Lemma 3 (part 1). The hole density `1/[Γ:Γ_m]` tends to `0`, so `x` is a regular Toeplitz array;
unique ergodicity then follows from Cecchi-Bernales–Cortez–Gómez (Prop `regular-measure`). It is not needed
here. ∎

**Remark (where genuine models come from).** The periodic models of `X_Γ` are exact finite `Γ`-sets
`Γ/Γ_M`. Relations cost nothing, because each model is a genuine quotient action, and the sparse hole
filling makes every window of the periodized skeleton occur in `x`. For `Z^2`-SFTs no periodic model exists at
all (Theorem Z). The difference is that here the *subshift* is designed around the chain.

## 7. New LEF Kazhdan simple families over every residually finite acting group

**Corollary T.** Let `Γ` be finitely generated, infinite and residually finite, `q` a prime power,
`R_Γ = LC(X_Γ, F_q) ⋊ Γ`, and `N >= 3`.
1. `R_Γ` is a finitely generated simple ring and embeds unitally and injectively in `∏_ω M_(N_n)(F_q)`.
2. `S_Γ,N = EL_N(R_Γ)/Z(EL_N(R_Γ))` is an infinite, finitely generated, simple group with property (T) that is
   LEF, hence sofic and hyperlinear.
3. In particular this holds for Kazhdan acting groups such as `SL_3(Z)` and `Sp_4(Z)`, and for surface groups.
   The case `Γ = Z` is the Pestov 9.1 mechanism.

*Proof.*
1. **Finite generation.** With `U = {x : x(e) = 1}`, the conjugates `u_g 1_U u_g^(-1) = 1_(gU)` are the indicators
   of all one-coordinate cylinders, and these generate `LC(X_Γ, F_q)` as an algebra. So `R_Γ` is generated by `u_s^(±1)` (`s` in a finite generating
   set) and `1_U`.
   **Embedding.** The action is minimal, topologically free and RF (Theorem T), so
   `residually-finite-actions-give-matricial-crossed-products` gives simplicity and the embedding.
2. **(T).** `elementary-groups-over-fg-rings-have-property-t`; finite generation by
   `elementary-group-fg-from-fg-coefficient-ring`.
   **Simple modulo centre.** The transformation groupoid is Hausdorff, ample, minimal, effective (topological
   freeness), with infinite compact unit space, so `steinberg-elementary-groups-are-simple-mod-centre` applies
   (reviewed PASS), and `Z <= F_q^x I` (`minimal-effective-steinberg-algebras-have-scalar-centre`).
   **LEF.** The embedding `ψ` is unital and `F_q`-linear, so `GL_N(R_Γ)` embeds in `∏_ω GL_(N N_n)(F_q)`
   (`exactly-matricial-rings-have-lef-general-linear-groups`). If `g ∈ EL_N(R_Γ)` maps to a scalar class,
   then since `F_q^x` is finite the scalar is constant `ω`-almost surely, and injectivity of `ψ` gives `g ∈ F_q^x I`.
   So `S_Γ,N` embeds in `∏_ω GL_(N N_n)(F_q)/F_q^x`, an ultraproduct of finite groups. It is finitely generated,
   hence LEF (`lef-implies-operator-mf` for the MF consequence).
3. `SL_3(Z)`, `Sp_4(Z)` and surface groups are finitely generated, infinite and residually finite. ∎

The Kazhdan property of `S_Γ,N` comes from EJZ and does not need `Γ` to have (T). What is new is the acting
group: the ring and group depend on `Γ` through a single RF Toeplitz subshift.

## 8. Credit, bounds, and what remains open

**Credit.**
- Lemma F is the full-support version of Kerr–Nowak Theorem 5.2 (minimal case), as quoted verbatim by Ma
  (`kerr-nowak-measure-free-group-actions-are-rf-citation`). The integer-flow proof here is elementary; no
  novelty is claimed for it.
- Proposition S, direction ⇒: the pseudo-orbit argument of `sfts-without-finite-orbits-are-not-residually-finite-actions`.
- RF passing to factors: `extensions-of-aperiodic-sfts-are-not-residually-finite-actions`.
- Toeplitz arrays over residually finite groups, and regular ones being uniquely ergodic, are due to Krieger,
  Cortez–Petite, and Cecchi-Bernales–Cortez–Gómez (arXiv:2305.09835, `theo:main0`, `theo:main1`, read from the
  TeX source; `ccg-uniquely-ergodic-toeplitz-subshifts-exist`). The contribution of §6 is the *sparse-filling*
  design making the subshift Kerr–Nowak RF, via Proposition S.
- Ma (arXiv:2209.00580, Remark after `thm: topo group of residually finite action`) lists minimal `Z`-systems and
  free-group systems with invariant measures as RF examples. Theorem V and Theorem T extend both lists.

**Bounds.** The Kerr–Nowak primary paper was not reachable during this lane (arXiv API redirects and
rate limits). A reviewer should confirm Theorem 5.2 from ETDS 32 (2012) and check whether their other examples
already cover virtually free groups or Toeplitz subshifts. No web search was run.

**Open, recorded in Cairn.**
- **The sharp class.** Conjecture: among finitely generated groups, `𝔑` is exactly the virtually free groups.
  Proved: virtually free ⊆ `𝔑`; groups containing `Z^2` ∉ `𝔑`.
  Unknown: one-ended groups without `Z^2`, e.g. surface groups, cocompact lattices in `Sp(n,1)`, `BS(1,n)`,
  infinite torsion groups.
  The obstruction needs a closed invariant subset of an SFT with no finite orbit carrying a full-support
  invariant measure. Every amenable group with such an SFT is outside `𝔑`.
- **Minimal free version for groups like `SL_3(Z)`.** Theorem Z.3 gives minimal free non-RF witnesses only
  for `Z^2 × Λ`. For `SL_3(Z)` the co-induced witness of Proposition R is not minimal, and a minimal subsystem
  need not carry an invariant measure.
- **Ring level.** Non-RF does not imply non-matricial: for `Z^2`-SFTs the ring may still have quantum models
  (`matricial-z2-sft-crossed-products-give-quantum-tilings`). So the ring-level flagship beyond virtually free
  groups is untouched by Theorem Z.
