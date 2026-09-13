# UN review, part 3 (lane un-verify-3, 2026-09-13)

Scope:
- the UN flagship assembly (route `free-group-cantor-el-lef-iff-invariant-measure-proof`, un-architect), which now fires;
- un-lef-converse's closing of the ladder converse (L⇒) (de117129bd);
- un-sofic-not-lef's new object (9ef8948121).

Method as in parts 1–2.

**Summary.** 8 PASS, 0 FAIL, two wiring/display notes (§1, §2). No established node refutes or subsumes these claims.
The UN root stays OPEN, since the converses (Σ⇒) and (M⇐) are still open.

| § | Node | Verdict |
|---|---|---|
| 1 | flagship `free-group-cantor-elementary-group-lef-iff-invariant-measure` (assembly route) | PASS (requires note) |
| 2 | `lef-el-groups-force-exactly-matricial-simple-ring` via `lef-el-groups-matricial-via-lef-ring` | PASS (title display note) |
| 3 | `lef-elementary-groups-force-lef-rings` | PASS |
| 4 | `simple-lef-rings-are-exactly-matricial` | PASS |
| 5 | `simple-kazhdan-linear-sofic-non-lef-group-exists` | PASS |
| 6 | `amenable-minimal-crossed-products-have-faithful-rank-models` | PASS |
| 7 | `crossed-product-group-embeds-in-projective-elementary-group` | PASS |
| 8 | `finitely-presented-lef-groups-are-residually-finite` | PASS (standard) |

## §1 Flagship assembly: PASS

Every required node carries a PASS review line or is an older established import:
- `crossed-products-are-transformation-steinberg-algebras` (part 1);
- `steinberg-elementary-groups-are-simple-mod-centre` (un-verify);
- `free-group-crossed-product-matricial-iff-invariant-measure`, `kerr-nowak-measure-free-group-actions-are-rf`,
  `residually-finite-actions-give-matricial-crossed-products` (un-verify-measure);
- `no-invariant-measure-steinberg-elementary-no-mf-quotient`, `stably-infinite-ring-elementary-groups-have-no-mf-quotient`
  (un-verify);
- `elementary-groups-over-fg-rings-have-property-t` (EJZ import) and `lef-implies-operator-mf` (established).

Assembly re-derived:
- **Step 0.** The transformation groupoid of a minimal, topologically free `F_r`-action is Hausdorff, ample, minimal and
  effective, with compact infinite unit space. So `S_N` is infinite and simple with `Z ⊆ F_q^x I`. EJZ gives (T) for
  finitely generated `R`.
- **Step 1.** Measure ⟹ residually finite ⟹ an injective unital `F_q`-linear `Ψ : R → ∏_ω M_(N_n)(F_q)`. The map
  `∏_ω GL → ∏_ω (GL/ΛI)` has kernel `[ΛI]`: `Λ = F_q^x` is finite, so an ω-sequence of scalars is ω-constant. If
  `Ψ(g) ∈ [ΛI]` then `g = λI_N`, and `EL_N(R) ∩ ΛI = Z`. So `S_N` embeds in an ultraproduct of finite groups and is LEF.
- **Step 2.** No measure ⟹ trivial MF quotients from rank `2n`; `S_N` is nontrivial, hence not MF, hence not LEF.
- **Conclusion.** The iff follows, since in the second case `S_N` fails LEF at some rank.

**Requires note.** The route asserts that `S_N` is finitely generated, but does not require
`elementary-group-fg-from-fg-coefficient-ring` (established, kernel-checked), which the claim body cites. Add it to the
route's requires.

**Display.** The node's scope and claim match the route: finite `F_q`; finitely generated `R`; LEF for all `N ≥ 3` iff a
measure exists; otherwise trivial MF quotients for `N ≥ 2n`, with the band open.

## §2 (L⇒) closed: `lef-el-groups-matricial-via-lef-ring`: PASS

- **The route.** Suppose `EL_N(R)` is LEF for every `N ≥ 3`. `EL_4(R)` LEF gives a LEF ring (§3); a simple LEF ring is
  exactly matricial over finite fields (§4). So the target holds, with more: one rank `N ≥ 4` suffices.
- **Root wiring.** The ladder route into `kazhdan-elementary-approximation-type-mirrors-ring-type` still requires the open
  `linear-sofic-el-groups-force-rank-model` and `stably-finite-simple-rings-have-mf-elementary-groups`, so the root stays
  OPEN.
- **Display note.** The target's title is still phrased as a question ("If every elementary group over a countable simple
  ring is LEF, is the ring exactly matricial?"), while its body now reads ESTABLISHED. Restate the title as the theorem.

## §3 lef-elementary-groups-force-lef-rings: PASS

- **Import.** `steinberg-finite-presentation-and-kazhdan-theorem` states that `St_n(A)` is finitely presented for a
  finitely presented ring `A` and `n ≥ 4`. The free ring on a finite window qualifies, matching the rank-four hypothesis.
- **Extension.** Partial multiplicativity of `ψ` on all relator prefixes makes every relator evaluate to `ψ(1) = 1`, so
  `ρ` extends to `St_N(A)`.
- **Level ideal.**
  - `K_ij` are subgroups, since `x_ij(a+b) = x_ij(a) x_ij(b)`.
  - `[x_ij(a), x_jk(1)] = x_ik(a)` and `[x_ij(1), x_jk(a)] = x_ik(a)` give `K_ij, K_jk ⊆ K_ik`, so all are equal.
  - `[x_12(a), x_23(b)] = x_13(ab)` makes `K` a two-sided ideal.
  - `A/K ≅ ρ(x_13(A))` is finite.
- **Window.** For `c ∈ D = L − L`, `c ∈ K` iff `π(c) = 0`, by injectivity of `ψ` on the ball. So `W → A/K` is injective
  and preserves the sums and products inside `W`.
- **Model tests.** `L_k(1,2)` is not directly finite, hence not a LEF ring, so no `EL_N`, `N ≥ 4`, is LEF. This is
  consistent with `cohn-elementary-group-is-not-lef`.

## §4 simple-lef-rings-are-exactly-matricial: PASS

- Finite nonzero `Q_n` gives `Q_n/J(Q_n) = ∏ M_d(F_q)` (Artin–Wedderburn, Wedderburn's little theorem).
- Projecting onto one factor is unital and preserves the window operations.
- `Ψ = [ψ_n]_ω` is a unital ring homomorphism, since every sum and product lies in `W_n` eventually.
- `ker Ψ` is proper, so it is `0` by simplicity.
- Model test: `F_2 × F_2` shows simplicity is needed.

## §5 simple-kazhdan-linear-sofic-non-lef-group-exists: PASS

- **Γ_p.** Finitely presented and amenable, with central `c_p ≠ e` killed by every finite-dimensional unitary
  representation (`abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, established). The regular representation
  of any finite quotient is faithful on the quotient, so `c_p` dies in every finite quotient. Hence `Γ_p` is not residually
  finite, and by §8 not LEF.
- **The ring.** GJS (import, not re-read) gives a free minimal subflow `X ⊆ 2^(Γ_p)`, so the groupoid is principal,
  minimal and effective. `R` is generated by `1_([x_e=1])`, `F_q` and the `u_s`, since translates of the coordinate
  cylinder generate the clopen algebra.
- **(T) and simplicity.** EJZ gives (T); the reviewed simplicity and scalar-centre theorems give simplicity with
  `Z ⊆ F_q^x I`.
- **Linear sofic.** §6 with `k = F_q`, plus the reviewed adjoint theorem (`rank-modelled-simple-rings-give-linear-sofic-projective-el`,
  part 1 §10), gives `F_q`-linear soficity of `S_N`.
- **Not LEF.** §7 embeds `Γ_p` in `S_N`, and LEF passes to subgroups.
- **Novelty.** Only a bounded graph scan was run (distinct_from nodes read). Soficity, hyperlinearity and MF of `S_N`
  remain open, as the node says.

## §6 amenable-minimal-crossed-products-have-faithful-rank-models: PASS

- **Truncation.** `P_(F_n) ρ(·) P_(F_n)` of the orbit representation on `k^(Γ)` has multiplicativity defect of rank at
  most `Σ_g |gF_n Δ F_n| = o(|F_n|)`.
- **Faithfulness.** For `a = Σ_(g∈K) f_g u_g` with `f_(g_0) ≡ c ≠ 0` on `W'`:
  - column `h` has coefficient `c` at `δ_(g_0 h)` whenever `hx ∈ g_0^(-1)W'`;
  - minimality and compactness give syndetic visits;
  - a `K`-separated subset of such `h` has pairwise disjoint column supports, since the supports are `Kh`.
  - Hence `rank ≥ |F_n|/(|L||K^(-1)K|) − o(|F_n|)`. Freeness is indeed not used: distinct group elements `gh` index
    distinct basis vectors.

## §7 crossed-product-group-embeds-in-projective-elementary-group: PASS

- `x_12(v) x_21(−v^(-1)) x_12(v) = [[0,v],[−v^(-1),0]]`, and `w(v)w(−1) = diag(v, v^(-1)) ∈ E_2`.
- `diag(v, v^(-1), 1) e_13(1) diag(v^(-1), v, 1) = e_13(v)`, so a central image forces `v = 1`.

## §8 finitely-presented-lef-groups-are-residually-finite: PASS (standard)

- A partial embedding of a ball containing the relators and a word for `g` defines a homomorphism to a finite group that
  keeps `g ≠ e`.
- Standard (Gordon–Vershik; "LEF + finitely presented ⟹ RF").
