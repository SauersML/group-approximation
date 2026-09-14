# sk-popa-lgx plan: Popa algebras in property (T) factors (2026-09-13)

Lane sk-popa-lgx (wave 11). Problem: the Popa clause of Brown's Question 3 for property (T) factors. Does `L(G_X)`, or any II_1 factor with property (T), contain a weakly dense Popa algebra? Open node: `property-t-factors-contain-weakly-dense-popa-algebras`.

## 1. The question and definitions (read at source)
- **Brown**, arXiv:math/0111286, §Questions item 3 (quoted verbatim in `research/artifacts/sk-free-5-brown-q3-2026-09-13-part1.md` §1): "Can a free group factor or a II$_1$ factor with property T contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?"
- **Popa algebra** (Brown–Dykema, arXiv:math/0207005, introduction): a unital simple C*-algebra `A` such that for every finite `𝔉 ⊆ A` and `ε > 0` there is a nonzero finite-dimensional subalgebra `B ⊆ A` with unit `e`, `‖[x,e]‖ < ε` and `dist(exe, B) < ε` for `x ∈ 𝔉`.

## 2. What the known constructions use (read at source on MSI, `/scratch.global/sauer354/sk/sk-popa-lgx`)
- **Brown, Theorem `thm:basicconstruction`** (math/0111286 l.872ff): a residually finite-dimensional `E` gives a Popa algebra `A` and traces `γ` with `π_γ(A)'' ≅ R ⊗̄ π_τ(E)''`.
  - The inductive system is `E → E ⊗ M_{k(1)} → …`, with connecting maps `x ↦ 1_E ⊗ diag(0_{n−k}, π(x)) + x ⊗ diag(1_{n−k}, 0)` (l.905ff).
  - The finite-dimensional structure hides on the matrix corner. The matrix units become the `R` tensor factor, so every weak closure is McDuff.
- **Brown–Dykema** (math/0207005):
  - Thm `thm:rfd`: `M_n *_D M_{n′}` is residually finite-dimensional.
  - Thm `thm:RBR`: `R *_B R ≅ L(F_s)` with `s = 2 − δ_0(B)`.
  - The Popa algebra is built from full amalgamated free products of matrix algebras. Freeness identifies the weak closure.
- **Neither mechanism exists in a property (T) factor.**
  - McDuff hiding would force `M ≅ M ⊗̄ R`, which contradicts fullness.
  - The free-product identification needs an amalgamated free product decomposition. Kazhdan groups have property FA, and I recall, without checking at source, that free products of diffuse algebras never have (T).

## 3. Firewalls on main
- `kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups` (T4, unreviewed): no QD algebra contains the image of `G_X`, so `C*_r(G_X) ⊄ A`.
- `kazhdan-group-factor-popa-corners-have-vanishing-trace` (Lemma S, unreviewed): Popa corners for 2-norm approximants of Kazhdan generators have trace `≤ 4ε_S^{-2}(4η+2δ)²`.
- An amenable trace on a weakly dense subalgebra forces injectivity. So `τ|_A` is a non-amenable trace, and `A` is non-nuclear with non-unique trace.

## 4. Targets
- **(O) Norm rigidity of Kazhdan generators (to prove now).** For an infinite group `Γ` with Kazhdan pair `(S, ε)`, no nonzero projection `p ∈ L(Γ)` and finite-dimensional `B ⊆ pL(Γ)p` with unit `p` satisfy `‖[λ_s, p]‖ + dist(pλ_sp, B) < ε/2` for all `s ∈ S`.
  - Tool: the canonical vector `ξ_B = Σ_r Σ_{ij} e^r_{ij} ⊗ e^r_{ji}` in the coarse bimodule `L²M ⊗ L²M`. It commutes with `B` exactly, and the conjugation representation of `Γ` there is a multiple of the regular representation.
  - Unlike Lemma S, this is scale free: no corner exists at any trace.
- **(S′) Orthogonal families (to prove now).** Take approximants `y_s ∈ M` with `a_s = λ_s − y_s`, and orthogonal Popa corners `(p_m, B_m)` for `{y_s}` at tolerance `η < ε/8`. With `P = Σ p_m`, the total trace satisfies
  `Σ_m τ(p_m) ≤ 2 (ε − 8η)^{-2} Σ_s (‖a_sP‖_2² + ‖Pa_s‖_2²)`.
  - This upgrades Lemma S: the bound goes from `(η+δ)²` to `δ²`, needs no halving projections, and holds uniformly over orthogonal families.
  - Consequence: in a weakly dense Popa algebra the approximants are relatively bad, `‖a_sp‖_2 + ‖pa_s‖_2 ≥ (ε − 8η)τ(p)^{1/2}` for some `s`, on every Popa corner.
- **(P) Positive direction: what a construction must satisfy.**
  1. every Popa corner carries a uniform relative 2-norm defect for the Kazhdan approximants, by (S′);
  2. `A` contains no set within norm `ε/8` of a critical set, by (O);
  3. the matrix units of `A` do not asymptotically commute with `A` on corners of trace bounded below, which would make `M` McDuff;
  4. the trace `τ|_A` is non-amenable while `A` is QD.

  Candidate mechanisms, each to be tested against 1–4 and recorded where it dies:
  - (P1) Brown's basic construction inside `M`, using `M ≅ M_n(qMq)` and T1 in corners;
  - (P2) the two locally finite tower subgroups `L_y, L_{y′}` with `G_X = ⟨L_y, L_{y′}⟩`, and full C*-hulls of their AF algebras in perturbed position;
  - (P3) LEF models of `G_X` in `∏M_n/⊕M_n`, where T4 is the firewall.
- **(X) Pivot.** If (P) yields an obstruction theorem for a natural class of constructions, land it as an established obstruction with `invalidates:` on the corresponding dead routes.

## 5. Landing schedule
- Plan now.
- Then the (O) and (S′) claims with `-proof` routes plus artifact part 1, queued with sk-verify-13.
- Then attempts (P1–P3) on the open node, and a final report to main.
