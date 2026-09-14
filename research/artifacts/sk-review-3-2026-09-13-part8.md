# SK review 3, part 8: subgroups of the Z-family G_X (sk-lef-embedding-d)

Lane `sk-verify-3`, 2026-09-13. Queue items 17–18. Main read at tip `3e5a0ff303`. Every step re-derived.
Artifacts: `research/artifacts/sk-lef-embedding-d-z-family-2026-09-13-part1.md` §1, `-part2.md` §§2–4.

## Verdicts

| claim | route | verdict |
|---|---|---|
| `z-family-lef-universality-reduces-to-gl-m-crossed-products` (Proposition A) | `-proof` | PASS |
| `fp-subgroups-of-subshift-gl-have-banded-representations` (Propositions B, C; Corollary B1) | `-proof` | PASS for the mathematics. GAP in the node's display of the obstruction test (quantifier), with a repair below. There is also a wiring note. |

Artifact §5 (the `SL_3(Z)` test object) is exploratory, not a claim, and was not reviewed.

## 1. Proposition A

- (i) ⇒ (ii): `G_Y ≤ GL_3(R_Y)`.
- (ii) ⇒ (i):
  - The overgroup `Γ ≤ [Δ,Δ]` with `Δ` f.g. LEF comes from `rf-groups-lie-in-derived-subgroups-of-rf-groups` (2), PASS in part 3 §A2.
  - `ρ: Δ ↪ S^×`, `S = M_m(R_X) ≅ R_(X^(m))` (tower claim, PASS in part 2 §5). So `EL_3(S) ≅ G_(X^(m))`.
  - Whitehead: `w(c)w(−1) = diag(c,c^(−1))`, and `diag(a,a^(−1),1)·diag(b,b^(−1),1)·diag((ba)^(−1),ba,1) = diag([a,b],1,1)`.
  - `c ↦ diag(c,1,1)` is injective and multiplicative, and it sends `[S^×,S^×]` into `EL_3(S)`.
  - Since `ρ(Γ) ⊆ ρ([Δ,Δ]) = [ρ(Δ),ρ(Δ)]`, `Γ` embeds.
- **Known subgroups list.**
  - `EL_n(F_2[u^(±1)]) ⊆ EL_(3n)(R_X) ≅ G_(X^(n))`, via block diagonal embedding.
  - `F_2[t^(±1)]` is Euclidean, so `SL_3 = E_3`.
  - The derived full group `[[σ]]′` maps into `[R^×,R^×]`.
  - Finite groups sit in tower corners.
- PASS.

## 2. Proposition B and Corollary B1

- `π(s) = Φ(ρ(s))` with `Φ(Σ f_j u^j) = Σ D_y(f_j)P^j` entrywise. List-preservation gives `π(v) = Φ(ρ(v))` along listed prefixes.
- Relators map to `Φ(I) = I`. `π(s)π(s^(−1)) = I`, so `π` is a homomorphism into `GL_(mN)(F_2)`.
- Injectivity on `B(r)`: `π(g) − π(h) = Φ(ρ(g) − ρ(h)) ≠ 0`.
- Banding: `D_y(f)P^j` maps block `n′` to block `n′+j`, and `|j| ≤ w` for generators.
- The window and period can be taken large. Item 1 of `subshift-lef-models-period-below-twice-recurrence` gives periodic `y_k` with `N_k ≥ 2k+2` for every `k`. Exponents in the list are `≤ (max length)·w`, so `N > 2·(max exponent)` separates them.
- B1 follows. It is also the special case "finitely presented LEF groups are RF".
- PASS.

**Wiring note.** The required node's item 2 is stated for balls of `EL_3(R)` with the elementary generating set. The route uses its proof for an arbitrary finite list in `M_m(R_X)`, with generator windows and exponents bounded by `w`. That proof is exactly what is used (the note's l.137–144 argument), so this is a display mismatch, not a gap. The owner could cite `minimal-subshift-algebra-is-simple-lef-ring` item 3, or state the general list form.

## 3. The obstruction test (display GAP)

**Node text:** "If a finitely presented `Γ` admits, for some `w`, no w-banded F_2-representations injective on balls of every radius, then `Γ` is a subgroup of no `G_X`."
- As worded, the hypothesis is `∃w ∃r` with no w-banded representation injective on `B(r)`.
- Proposition B only provides representations for the particular `w` bounding the exponents of a given embedding. Excluding one `w` excludes nothing.

**Repair** (the artifact's Corollary B2 already has the right order):
> "Suppose that for every `w` there is `r` such that no homomorphism `Γ → GL_N(F_2)`, for any `N`, with cyclically `w`-banded generators in blocks of size 3, is injective on `B_Γ(r)`. Then `Γ` is a subgroup of no `G_X`."

Block size 3 suffices for `G_X ≤ GL_3(R_X)`. For `GL_m(R_X)`, use blocks of size `m`.

## 4. Proposition C

- `R_X` is simple, so the orbit representation `π_x` on `⊕_Z F_2` has kernel a proper ideal, hence `0`. So `M_m(R_X)` acts faithfully on `⊕_Z F_2^m`.
- Generators move supports by `≤ w`, so `dim span(B(r)·v) ≤ m(L + 2wr)`. The bound passes to subquotients.
- PASS.

## 5. For the note

Proposition A is a clean reduction but proves no new embedding into the Z-family itself. The reviewed envelope theorem (part 6) uses the lamplighter crossed products, which are not Z-subshift groups. Whether every f.g. LEF group lies in some `G_X` stays open. Proposition B supplies necessary conditions.
