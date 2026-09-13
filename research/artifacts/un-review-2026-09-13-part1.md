# UN review, part 1: uniform simplicity of elementary groups over Steinberg algebras

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-simplicity`, landing `6c58d38ebb`, artifact
`research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md`. Tip at review: `45483f6995`.

Verdicts:

| item | node | verdict |
|---|---|---|
| (1) | `steinberg-algebras-have-local-annihilation` | PASS |
| (2) | `minimal-effective-steinberg-algebras-have-scalar-centre` | PASS (credit note) |
| (3) | `steinberg-algebra-simple-iff-minimal-effective` (+ `-citation`) | PASS |
| (4) | `steinberg-elementary-groups-are-simple-mod-centre` (+ `-proof`); `local-annihilation-makes-projective-el-simple` | PASS |

No false establishment. No FAIL, no GAP.

## 1. Local annihilation (S1)

**Lean predicate, as on main** (`GroupApproximation/Pestov91/SimpleModCentre.lean:43`):

```lean
def LocalAnnihilation (R : Type*) [Ring R] : Prop :=
  ∀ F : Finset R, NonUnitalSubring.closure
    {s : R | ∃ t : R, t ≠ 0 ∧ t * s = 0 ∧ ∀ f ∈ F, t * f * s = 0} = ⊤
```

The claim node's `S_F` and "generates `R` as a non-unital ring" match it word for word.

**Re-derivation (artifact §1).**
- Restriction identity. For `U, W ⊆ 𝒢⁽⁰⁾` compact open, `(χ_W * f)(g) = χ_W(r g) f(g)` and
  `(f * χ_U)(g) = f(g) χ_U(s g)`, since `χ_W` and `χ_U` are supported on units. Checked.
- `F` is supported in `K = ⋃_j B_j`, finitely many compact open bisections. By definition every element of `A_k(𝒢)` is
  a finite combination of `χ_B`, so this holds even for non-Hausdorff `𝒢`.
- The unit space of an ample groupoid is locally compact Hausdorff and totally disconnected. Here it is also compact, so
  it is zero-dimensional. `s(B_j)` is compact open in a Hausdorff space, hence clopen. The clopens `W ∋ y` missing the
  finite set `P_x`, and `V_x ∋ x` with the three listed properties, exist as stated.
- For clopen `V ⊆ V_x`, `s = χ_V a` and `t = χ_W`:
  - `t ≠ 0` needs `W ≠ ∅` and `k ≠ 0`, both assumed;
  - `ts = χ_(W∩V) a = 0`;
  - `tfs = (χ_W f χ_V) a`. An arrow `g ∈ supp f` with `s g ∈ V` lies in some `B_j` with `s g ∈ s(B_j) ∩ V_x`, which
    forces `x ∈ s(B_j)`, so `r g = α_j(s g) ∈ α_j(V_x)`, which misses `W`.
- The finite subcover refines to a clopen partition (successive differences), and `Σ χ_(V_i) = 1`, so the additive
  span of `S_F` is already `R`. Checked.

**Model tests.**
- A field `k`: `t ≠ 0` and `ts = 0` force `s = 0`, so `S_F = {0}` and the predicate FAILS, as it should.
- `LC(X, k)` for Cantor `X` (the trivial groupoid on `X`): the predicate holds by S1, but the ring is not simple (the
  functions vanishing at a point form a proper ideal). So the ring criterion S3 genuinely needs both hypotheses.
- Both calibrating rings satisfy S1: `L_k(1,2)`, whose unit space is Cantor, and `LC(X,F_q) ⋊ Z`, whose unit space is
  `X`. On main, the Pestov ring is also certified by `localAnnihilation_of_crossedProduct`
  (`SimpleModCentreCrossed.lean:67`).

## 2. Scalar centre (S2)

**Re-derivation (artifact §2 and the route).**
- `𝒢` is Hausdorff, so elements are locally constant with compact support.
- For clopen `U`, `χ_(𝒢⁽⁰⁾∖U) z χ_U` evaluated at `g` is `z(g)` when `r g ∉ U` and `s g ∈ U`, and `0` otherwise.
  Centrality makes it `0`. Clopens separate points, so `supp z ⊆ Iso(𝒢)`.
- `supp z` is open, so it lies in `Iso(𝒢)° = 𝒢⁽⁰⁾` by effectiveness.
- For a compact open bisection `B` and `g ∈ B`, `(χ_B z)(g) = z(s g)` and `(z χ_B)(g) = z(r g)`. Every arrow lies in
  such a `B`, so `z` is constant on orbits.
- `z` is continuous and every orbit is dense, so `z` is constant. Checked.

**Source.** Clark–Edie-Michell, arXiv:1403.4684. `main.tex` lines 578–584, fetched 2026-09-13, match the node's quote
verbatim:

> Let $G$ be a Hausdorff, ample groupoid, and $R$ a commutative ring with identity. (1) Suppose $G$ is effective and
> minimal, and $G^{(0)}$ is compact. Then $Z(A_R(G)) = R1_{G^{(0)}}$.

**Credit note (not a defect).** The same statement is already Steinberg, arXiv:1408.6014, **Proposition 3.7** (PDF
p. 10, read from the page image). For an effective Hausdorff ample groupoid and a commutative ring with unit, the centre
consists of the continuous compactly supported functions on `𝒢⁽⁰⁾` constant on orbits. In particular, if `𝒢⁽⁰⁾` has a
dense orbit, `Z(k𝒢) = k·χ_(𝒢⁽⁰⁾)` if `𝒢⁽⁰⁾` is compact, and `0` otherwise. Please add it as a co-credit.

**Opportunity, for the owner.** Via the graph-groupoid dictionary, S2 or CEM Theorem thm:center(1) should close the OPEN
claim `simple-leavitt-path-algebra-center-is-coefficient-field`. For a finite graph, a simple unital Leavitt path
algebra is a Steinberg algebra of a Hausdorff ample graph groupoid with compact unit space, and simplicity gives
effective and minimal by Steinberg Cor 3.6. The dictionary import is not checked here.

## 3. Steinberg simplicity import

- **TeX source** (arXiv:1408.6014, `main.tex` lines 317–330): `Thm simple` and `Cor simplehaus` match the citation
  node verbatim.
- **PDF p. 10:** Theorem 3.5 and **Corollary 3.6**, the same statements. The claim node's numbering "Corollary 3.6"
  is correct.
- **CEM "Corollary 4.6, a ring version":** checked against the PDF text of arXiv:1403.4684. Corollary 4.6: "Let G be a
  Hausdorff, ample groupoid and R a commutative ring with identity. Then A_R(G) is simple if and only if G is effective
  and minimal, and R is a field." Numbering and statement correct.
- The claim node states only the Hausdorff equivalence, so the non-Hausdorff half of Theorem 3.5 is not relied on.

## 4. Assembly

**Requires**, all present on main and established:
- `steinberg-algebra-simple-iff-minimal-effective` (import, §3);
- `steinberg-algebras-have-local-annihilation` (§1);
- `local-annihilation-makes-projective-el-simple` (Lean);
- `minimal-effective-steinberg-algebras-have-scalar-centre` (§2);
- `elementary-groups-over-fg-rings-have-property-t` (ESTABLISHED import of Ershov–Jaikin-Zapirain arXiv:0809.4095v2,
  Theorem `thm:main`).

**Lean hypotheses.** `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center` has exactly
`(hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R] (hloc : LocalAnnihilation R)`, with ambient `[Fintype ι] [DecidableEq ι]
[Ring R]` (`SimpleModCentre.lean:327`). Checks:
- no incomplete-proof placeholder and no axiom declaration in `SimpleModCentre.lean` or `SimpleModCentreCrossed.lean`;
- both modules are root-imported (`GroupApproximation.lean:4897–4898`);
- `IsSimpleRing` is Mathlib's two-sided-ideal simplicity. For a unital `k`-algebra, ring ideals are automatically
  `k`-subspaces, so algebra-simple in Steinberg's sense matches it.

**Paper steps re-derived (route §3).**
- With `h = e_ij(s)`, `t s = 0` and `t g_pk s = 0`, every entry of `ρ − 1 = g h g⁻¹ h⁻¹ − 1` is left-annihilated by `t`.
- `t ρ⁻¹ = t` as well, since `tρ = t`. So `ρ e_ml(ct) ρ⁻¹ e_ml(ct)⁻¹ = 1 + (ρ − 1)_(·m) c t` in column `l`, using
  `l ≠ m`. This is the displayed one-column matrix.
- `c` with `(ρ − 1)_(qm) c t ≠ 0` exists: otherwise `R (ρ−1)_(qm) R t = R t = 0`.
- Centre clause: commuting with every `e_ij(1)` forces `g = λI`, and commuting with `e_ij(a)` forces `λ ∈ Z(R)`. Checked.

**Remaining clauses.**
- **(T):** gated on finite `k` and finitely generated `R`, which is exactly EJZ's hypothesis. (T) passes to quotients,
  and (T) groups are finitely generated. Correct.
- **Infinite:** `e_12(a) e_12(b)⁻¹ = e_12(a − b)` is central only if `a = b`, since central elements are scalar. `R` is
  infinite because the unit space is infinite. Correct.

## 5. Subsumption scan (untruncated)

Scanned every `research/*.md` at `538afe1ed4` with two greps:
- local annihilation, simple modulo centre, scalar centre, `Z(A_k`, 1403.4684, 1408.6014, normal subgroups of EL,
  `EL_n(R)/Z`, sandwich: 301 hits;
- "Steinberg algebra": 19 hits.

Every established claim hit was read.
- **Special cases of the new claims, consistent with them and already named in `distinct_from` or artifact §5:**
  - `simple-kazhdan-lef-group-from-minimal-subshift` and `free-minimal-subshift-elementary-groups-are-simple-kazhdan`
    (simplicity halves);
  - `binary-leavitt-elementary-group-is-simple`;
  - `leavitt-center-is-coefficient-field` (S2 for `L_k(1,2)`);
  - `odd-leavitt-unit-groups-mod-scalars-are-fp-simple` and `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`
    (simplicity parts).
- **Consistent converse:** `projective-elementary-simplicity-forces-simple-ring`.
- No older established node proves S1, S2 or S4 at this generality, and none refutes them or an open neighbour.
- One OPEN neighbour becomes provable: `simple-leavitt-path-algebra-center-is-coefficient-field` (§2).

## 6. Display check

Recomputed every formula displayed in the ten node files:
- `S_F` and the partition clause (S1 claim);
- `tfs = (χ_W f χ_V) a = 0` (S1 route);
- `χ_(𝒢⁽⁰⁾∖U) z χ_U = χ_(𝒢⁽⁰⁾∖U) χ_U z = 0` and `z(r g) = z(s g)` (S2 route);
- `t(ρ − 1) = 0`, `(ρ − 1)_qm c t ≠ 0` and the one-column commutator (S3 route);
- `Z(EL_n(R)) ⊆ Z(R)^× I_n = k^× I_n` and `e_12(a) e_12(b)⁻¹ = e_12(a−b)` (S4 route).

All agree with the artifact and with the Lean statement.
