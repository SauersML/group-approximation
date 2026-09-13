# Where a tracial rigid support can and cannot come from

Lane `un-tracial-support`, 2026-09-13. Unreviewed.

**Target.** A rigid support `S` inside tracial ultraproducts satisfying (S1)–(S3) of Lemma C
(`research/artifacts/un-open-8-target-agnostic-compression-2026-09-13.md` §1), so that hyperlinear images kill
`D_G(L)`. Equivalently: `NORM(hyperlinear)` of `rigid-compression-defect-normalization-dichotomy`, which is the
open win–win claim `hyperlinear-groups-kill-rigid-compression-defects`.

**Outcome.** No support found. This file records:
- a reformulation of normalization as the absence of a Wold shift (§0);
- a calibration of the extra hypothesis against the sofic group `W` (§1);
- five firewalls (§2), one with a new explicit example (TS2);
- the specification a support must meet (§3).

Nothing here asserts hyperlinearity or non-hyperlinearity of any group.

## 0. Reformulation

**Setting.**
- `σ: G -> U(M^ω)` is a homomorphism, `M^ω = prod_ω M_{d_n}` with trace `τ`.
- `Γ <= G` is Kazhdan, and `u ∈ G` satisfies `Γ_1 = uΓu^-1 ⊊ Γ`.

```text
A = σ(Γ)' ∩ M^ω,    B = σ(Γ_1)' ∩ M^ω = σ(u) A σ(u)*,    A ⊆ B.
```

Let `π(g)ξ = σ(g) ξ σ(g)*` on `L²(M^ω)`.
- The fixed space of `π(Γ)` is `L²(A)`: the automorphisms `Ad σ(γ)` preserve the trace, so the projection onto
  fixed vectors extends the conditional expectation onto the fixed-point algebra.
- So `V = π(u^-1)` maps `L²(A)` onto `L²(σ(u)*Aσ(u))`. That algebra is the commutant of `u^-1Γu ⊇ Γ`, so it lies
  inside `A`, and `V` is an isometry of `L²(A)` into itself.
- By the Wold decomposition:

```text
L²(A) = (⊕_{n>=0} V^n D) ⊕ ∩_n V^n L²(A),     D = L²(A) ⊖ V L²(A).
```

**Normalization at `(σ, u)` holds iff `D = 0`**, i.e. iff `V` has no shift part on `L²(A)`. A nonzero vector of
`D` is a `Γ`-central element orthogonal to the commutant of `u^-1Γu`.

## 1. Calibration: what separates W from the Leavitt pair

| | `W` (tex l.1840–1880) | Leavitt pair (tex l.918, Cor l.1016) |
|---|---|---|
| `Γ` | `Z^3 ⋊ SL_3(Z)`: (T), residually finite | `EL_3(L_{F_2}(1,2))`: (T), minimally almost periodic |
| compression | `α = Ad diag(2,2,2,1)`, index 8 | `e_ij(a) -> e_ij(sat)`, infinite index |
| compressor group | ascending HNN type, maps onto `Z`, not Kazhdan | `EL_4(L)`, Kazhdan |
| HS image of the defect | survives: `‖V_n(ε) - 1‖_2 -> sqrt 2` (tex l.1845) | unknown |

- **Why W escapes.** `W` is sofic, so it contains no rigid pair with nontrivial defect
  (`sofic-groups-kill-rigid-compression-defects`). Its configuration fails the rigid-pair hypothesis exactly
  because the compressor group is not Kazhdan (ladder §4, Theorem 4).
- **The extra hypothesis.** It is "`G` is Kazhdan", and the open claim already assumes it. So a tracial support
  must use (T) of `G` essentially, and TS1 shows spectral gap alone is not enough.
- **Infinite index is automatic for Leavitt-type pairs.** A group without nontrivial finite quotients has no
  proper finite-index subgroup, since it would act nontrivially on the cosets. So any support for them is an
  infinite-index object.

## 2. Firewalls for the candidate tools

**TS1. Spectral gap of `G` is powerless at the level of unitary representations.**
- Take a strict compression `uΓu^-1 ⊊ Γ <= G` with `Γ` and `G` Kazhdan, and the quasi-regular representation `λ`
  on `ℓ²(G/Γ)`.
- `δ_Γ` is `Γ`-fixed. `λ(u)δ_Γ = δ_{uΓ}` is `Γ`-fixed iff `u^-1γu ∈ Γ` for all `γ ∈ Γ`, i.e. iff
  `Γ ⊆ uΓu^-1`, which strictness forbids.
- So the Wold shift of §0 occurs in an honest unitary representation of a Kazhdan group. `NORM` cannot follow
  from (T) of `Γ` and `G` used only through unitary representations.
- A proof must use that `π` is a conjugation representation into a tracial algebra: fixed spaces are algebras,
  and `π(g) = λ(σ(g)) ρ(σ(g))*`.

**TS2. The Jones basic construction and the Pimsner–Popa index cannot force index 1.**
- **The tempting argument.** Work in `⟨M^ω, e_A⟩` with its canonical trace `Tr(x e_A y) = τ(xy)`, so
  `Tr(e_A) = 1`, and `e_A <= e_B`. If `e_B = v e_A v*` for a unitary `v` of `⟨M^ω, e_A⟩`, then
  `Tr(e_B) = Tr(e_A)`, and faithfulness would give `A = B`.
- **Why it fails.** The projection onto `L²(σ(u)Aσ(u)*)` is `π(u) e_A π(u)*` with `π(u) = σ(u)·Jσ(u)J`.
  - Left multiplication alone sends `L²(A)` to `L²(σ(u)A)`.
  - The right factor `Jσ(u)J` lies in `⟨M^ω, e_A⟩ = (JAJ)'` only when `σ(u)` commutes with `A`, which is the
    conclusion sought.
  - The trace sees one side of the bimodule; conjugation is two-sided.
- **Explicit strict unitary compression with finite index** (node `finite-index-unitary-compression-in-r-omega`).
  - Setup: `R = ⊗_{k∈Z} M_2` with the product trace, and `s` the shift `k -> k+1`.
  - Cyclic permutations of tensor factors on windows `[-m-1, m+1]` implement `s` on `[-m, m]`. So there is a
    unitary `v ∈ R^ω` with `Ad v = s` on the constant copy of `R`.
  - For `A = ⊗_{k>=0} M_2`: `v* A v = s^-1(A) = ⊗_{k>=-1} M_2 ⊋ A`, with Jones index 4.
  - So a unitary of the ultraproduct can strictly enlarge a von Neumann subalgebra with finite Jones index. No
    index, trace or dimension read off the position of `A` is a size, which sharpens `invariant-size-collapse`
    from infinite to finite index.
- **Group form: (T) of `Γ` is essential.**
  - Let `P_-` be the locally finite group generated by the Pauli matrices at coordinates `k < 0`, and `u = v*`.
    Then `uP_-u^-1 = s^-1(P_-) ⊆ P_-`.
  - `z = σ_x` at coordinate `0` commutes with `P_-`. But `uzu^-1` sits at coordinate `-1` and does not commute with
    `σ_z` there.
  - So `<P_-, u, z> <= U(R^ω)` is a countable hyperlinear group with a nontrivial compression defect for a
    non-Kazhdan subgroup, consistent with the ladder: without (T) there is no DD.

**TS3. Finite von Neumann algebra targets are not enough.**
- Normalization fails in finite von Neumann algebras for the configurations of interest:
  - `kun-thom-wreath-factor-is-exact-nonnormalized-commutant`: inside `L(W)` for the Kun–Thom wreath;
  - `fournier-facio-regular-models-carry-commutant-shift`: a proper shift on the `Γ`-commutant in every
    nontrivial tracial model.
- So a tracial support must use Connes-embeddability of the target, meaning finite matrix stages (ladder §11).
  Cited, not re-proved.

**TS4. No genuine skeletons on the Leavitt configuration.**
- `EL_3(L)` and `EL_4(L)` are minimally almost periodic (`binary-leavitt-unit-group-is-minimally-almost-periodic`,
  reviewed PASS).
- Take a trace-preserving `σ`. Every genuine finite-dimensional representation of `G` is trivial, while
  `τ(σ(g)) = 0` for `g ≠ 1` gives `‖σ(g) - 1‖_2 = sqrt 2`. So `σ|G` stays at normalized-HS distance `sqrt 2` from
  genuine representations, flexibly as well.
- So the sufficient route of ladder §11.4 (flexible actor exactification) cannot apply to the Leavitt pair, or to
  any infinite simple Kazhdan actor (`S_∂`, Pestov's `S`, `EL_N(A_k(𝒢))/Z`).
- The same fact is recorded for `Q` in `binary-leavitt-unit-group-hyperlinear`; here it is stated for the actor
  of the defect criterion.

**TS5. Relative (T) in the ultraproduct gives only rounding.**
- Connes–Jones rigidity gives `‖x - E_A(x)‖_2 <= κ^-1 max_{s∈S} ‖[σ(s), x]‖_2` for `x ∈ M^ω`, i.e. (A1), (A2)
  and (A4) of ladder §10.
- Rounding describes `A` and `B` separately. It says nothing comparing `A` with `σ(u)Aσ(u)*`, and (A3) is exactly
  that comparison.

## 3. The specification a tracial support must meet

For the Leavitt pair, a proof of `NORM(hyperlinear)` must:
- (a) use (T) of the compressor group `G`, not only of `Γ` (§1);
- (b) use more than the unitary representation theory of `G` (TS1);
- (c) see both sides of the conjugation bimodule, not a one-sided basic construction (TS2);
- (d) live at finite matrix stages, not in a finite von Neumann limit (TS3);
- (e) use no genuine finite-dimensional representation of `G` (TS4);
- (f) handle infinite index (§1).

**A candidate object meeting (c)–(f)** (a proposal only, not a claim):
- At stage `n`, take the HS range of the rounded Kazhdan projection of the conjugation action, restricted to
  operator-norm-bounded almost-commuting matrices.
- On bounded elements the containment `A ⊆ B` is exact. The Ad-Lipschitz failure (`un-hyperlinear-paradox` §3)
  lives on unbounded vectors.
- No faithful monotone size on that bounded part is known.

## 4. Status

- **Unreviewed.**
- **Recalled, not imported:** the Wold decomposition; fixed vectors of a trace-preserving action are `L²` of the
  fixed-point algebra; the Jones index of `A ⊆ M_2(A)` is 4; Connes–Jones rigidity for (T) groups.
- The TS2 example is self-contained (route `finite-index-unitary-compression-in-r-omega-proof`).
- Nothing here decides the famous claim.
