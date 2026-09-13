# UN review, part 6 (lane un-verify-3, 2026-09-13)

Scope:
- the part-5 notes, applied by this lane because the owners have finished;
- un-horofunction-families (703e356968);
- un-sigma-converse (3fa78684f7).

Method as in parts 1–5.

**Summary.** 4 PASS, 0 GAP, 0 FAIL. Three fixes applied.

| § | Node | Verdict |
|---|---|---|
| 1 | part-5 fixes (Toeplitz route requires, scope, transient noncentrality) | applied |
| 2 | `f2-groups-have-paradoxical-free-minimal-subshifts` | PASS |
| 3 | `f2-group-subshift-elementary-simple-kazhdan-not-mf` | PASS |
| 4 | `linear-sofic-projective-el-lifts-to-gl-rank-models` | PASS |
| 5 | route `non-linear-sofic-via-sigma-converse-at-leavitt` | PASS (wiring; cannot fire) |

## §1 Fixes applied

- `toeplitz-subshift-kazhdan-group-has-pestov-mf-quotient-proof` now also requires `elementary-group-fg-from-fg-coefficient-ring`
  and `lef-implies-operator-mf` (both established).
- `toeplitz-subshift-kazhdan-group-has-pestov-mf-quotient` gains a scope paragraph: items 3–4 are for `n ≥ 4`, the quotient
  is `EL_n` over the Pestov ring, and Pestov's `S` (rank 3) is not covered by the radical computation. The node id cannot
  change.
- `transient-crossed-products-have-nonsimple-mf-quotients-proof` now separates nontriviality
  (`[e_12(a), e_23(1)] = e_13(a)`) from noncentrality (`[e_13(a), e_32(1)] = e_12(a) ≠ 1`).

## §2 Paradoxical free minimal subshifts: PASS

- **Lemma 1.**
  - For `w = a^(-1)v` reduced, `aw = v` does not begin with `a`. Conversely, `v ∉ W(a)` gives a reduced `a^(-1)v`.
  - So `F = W(a) ⊔ aW(a^(-1))`, with `g_2 = a^(-1)` mapping the second piece to `W(a^(-1))`; the same for `b`.
  - The four translates start with four distinct letters.
  - Along `Γ = ⊔_t Ft`, left `F`-translation preserves each coset and acts as on `F`.
- **Lemma 2.**
  - `(γ·x)(g) = x(gγ)` is a left action, and `γ·{x(e)_k = 1} = {y(γ^(-1))_k = 1}`.
  - The partition conditions `y(e)_1 + y(e)_2 = 1` and `y(e)_3 + y(e)_4 = 1`, and the disjointness condition
    `y(g_1^(-1))_1 + y(g_2^(-1))_2 + y(h_1^(-1))_3 + y(h_2^(-1))_4 ≤ 1`, depend on finitely many coordinates, so they are
    closed.
  - On the orbit, `y(g_i^(-1))_i = χ_(g_iA_i)(δ)`.
- **Proposition 3.**
  - Freeness: `Stab(x,w) ⊆ Stab(w) = 1`.
  - `Z` is minimal by Zorn plus compactness.
  - Perfect: an isolated point makes its orbit open, hence all of `Z`, and a compact discrete space is finite, which a
    free infinite action rules out.
  - Cantor by Brouwer (recalled).
  - (H-gen): translates of `{x(e) = σ}` and `{w(e) = 1}` are all coordinate cylinders, which separate points. A different
    left-shift convention on `2^Γ` only permutes coordinates.
  - (H-par): preimages along the equivariant projection.
- **Hyperbolic consequence.** It appears only as recalled "Instances" in the claim bodies and as an Attempts bullet on
  `hyperbolic-group-cantor-model-simple-kazhdan-not-mf`, which stays OPEN with no incoming route. It is not a node.
- **Credit and novelty.** Rørdam–Sierakowski's paradoxical free minimal actions are recalled, not read. Novelty was not
  checked.

## §3 The F_2-group elementary groups: PASS

- The route feeds the reviewed paradoxical Cantor theorem exactly: finitely generated `Γ`, minimal, free hence
  topologically free, (H-gen), (H-par).
- The explicit defect matches that theorem's Lemma P.

## §4 Projective linear soficity lifts to exact GL rank models: PASS

- **Descends.** `Ad(λA) = Ad(A)`, and
  `Ad A − Ad(λB) = (A−λB)⊗A^(−T) + λB⊗(A^(−T) − (λB)^(−T))`. Each term has rank at most `n·rk(A−λB)`, so the map
  descends to `P → U`.
- **Injective on `P`.**
  - `ker(Ad A − 1)` is the commutant `C(A)`.
  - At an eigenvalue `μ` with Jordan partition `p` and conjugate partition `p'`, `dim C(A)` at `μ` is `Σ_j (p'_j)²`.
    This is at most `p'_1 Σ_j p'_j = k_μ d_μ`.
  - So `rk(Ad A − 1)/n² ≥ min_μ rk(A − μ)/n`.
  - For `μ ∈ k̄ \ k`, perfectness gives a conjugate `μ' ≠ μ` whose eigenspace has equal dimension and is independent, so
    `k_μ ≤ n/2`. At `μ = 0`, `rk(A) = n`.
  - Hence an `ω`-null `Ad`-image forces the `ω`-minimum to be attained on `k^×` and tend to `0`.
- **Kernel.** Exactly `Z_N`.
- **Novelty.** The reverse of the reviewed forward computation (part 1 §10).

## §5 Route into `non-linear-sofic-group`: PASS (wiring)

- The contrapositive of (Σ⇒) at `L_(F_2)(1,2)`: simple, centre `F_2`, no unital rank model. Some `S_N = EL_N` (since
  `F_2^× = 1`) is not `F_2`-linear sofic. The root asks for failure over some field.
- The route requires `linear-sofic-el-groups-force-rank-model`, which is OPEN with no incoming route, so it cannot fire.
