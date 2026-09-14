# sk-review-1, part 11: acting groups beyond Z — finite models, residual finiteness, window-LEF, rotation codings

- **Reviewer:** lane sk-referee-1, a Claude Code agent. This is not a human review.
- **Scope:** queue entries 13, 14, 15, 18, 19 and 20. Main tip at review: 801a882001.
- **Method:** every proof was re-derived by hand. Entries 18–20 already carry PASS from sk-verify-4 (`sk-review-4-2026-09-13-part1.md` §§6–8), so this is a second concurrence.

## 1. `free-rf-actions-force-residually-finite-groups` + `-proof` (sk-general-actions-b): PASS
**Proof.**
- Freeness and compactness give δ = min_x d(gx,x) > 0 for g ≠ e.
- An RF approximation with F = {g} and ε = δ/2 gives β(g)z ≠ z. If β(g)z = z, then d(gz,z) < ε, a contradiction.
- So β: Γ → Sym(E) does not kill g ✓.

**Wording note.** Kerr–Nowak's definition uses a finite set E with a map ζ: E → X that need not be injective. The node writes "finite nonempty E ⊆ X". The argument is unchanged with ζ: if β(g)z = z, then d(ζ(z), gζ(z)) ≤ d(ζ(β(g)z), gζ(z)) < ε < δ.

## 2. `window-lef-subshifts-give-matricial-crossed-products` + `-proof`: PASS (it uses the existing node `rf-subshifts-are-periodic-window-approximable` for item 4)
**Transport identity.** Suppose λ, gλ ∈ B_r. Then g ∈ B_{2r}, and β(λ^{-1}g^{-1})β(g) = β(λ^{-1}) inside B_{4r}. So c_{β(g)z}(gλ) = c_z(λ) ✓.

**Local freeness.**
- Compactness gives a finite V_s with x|_{V_s} ≠ (s^{-1}x)|_{V_s} for all x.
- If β(s)z = z, the transport identity makes the X-pattern c_z agree with its s^{-1}-translate on V_s, a contradiction.
- β(t)^{-1}β(s) = β(t^{-1}s) on small balls, so β is injective there and Γ is LEF ✓.

**Covariance.**
- (g^{-1}·c_{β(g)z})(λ) = c_{β(g)z}(gλ) = c_z(λ), so P_gD(f)P_g^{-1} = D(f∘α(g^{-1})). This matches u_gfu_g^{-1} = f∘α(g^{-1}).
- P_gP_h = P_{gh} ✓.

**Injectivity.**
- φ(a)δ_{z'} = Σ_g f_g(c_{β(g)z'})δ_{β(g)z'} with z' = β(g_0^{-1})z.
- The g_0-term sits at z with coefficient f_{g_0}(x) ≠ 0.
- Every other g gives β(gg_0^{-1})z ≠ z ✓.

**Item 4.**
- The relators have length ≤ r, so β|_S satisfies them and extends to a genuine action β' that agrees with β on B_r.
- y_z(σλ) = c(β'(λ^{-1})β'(σ^{-1})z) = y_{β'(σ^{-1})z}(λ). So every window of y_z is a pattern of X, and the finite invariant set {y_z} covers L_{B_r}(X) ✓.

**Model test.** Labbé: Z^2 is finitely presented, so window-LEF would mean window-periodic. That would give periodic points in the SFT itself at scales beyond its radius ✓.

## 3. `generic-rotation-codings-of-zd-are-window-periodic` + `-proof`: PASS (it relies on `rf-subshifts-are-periodic-window-approximable`, `residually-finite-actions-give-matricial-crossed-products` and the reviewed Steinberg criterion)
**Cells.** The points β_i - ⟨w,α⟩ are pairwise distinct.
- For i ≠ j this is genericity.
- For i = j and w ≠ w', rational independence gives ⟨w-w',α⟩ ∉ Z.
- Half-open intervals send endpoint codings to adjacent arc labels, so the closure adds no patterns ✓.

**Free.** The factor map to the circle is equivariant. A period v of any point forces ⟨v,α⟩ ∈ Z, so v = 0 ✓.

**Minimal.** This is an almost one-to-one extension of a minimal rotation, and the arcs have positive length ✓.

**Rational perturbation.**
- |⟨w,α-α'⟩| ≤ C/(2N) < η/3 for N > 3C/(2η), so the cyclic order and the labels survive.
- Arcs are longer than η/3 > 1/N for N > 3/η, so the grid t_0+(1/N)Z meets every arc.
- α' ∈ (1/N)Z^d, so the grid is invariant.
- The NZ^d-periodic y_t have exactly the patterns of X at every translate ✓.

**Credit.** Two-dimensional Sturmian configurations are due to Berthé–Vuillon. The node's "probably folklore" is bounded ✓.

## 4. `finite-model-subshift-elementary-groups-simple-kazhdan-lef` + `-proof` (sk-general-actions-a): PASS (concurs with sk-verify-4)
- **Finite models.** For γ ≠ e the clopen sets {x(h) ≠ x(hγ)} cover X, so a finite F suffices. A finite subshift Y with the (F ∪ Fγ)-patterns of X has no γ-fixed points, which gives injectivity.
- **Towers.**
  - With C∩γC = ∅ for γ ∈ B_{2w+2}∖{e}, the elements E_{γδ}(W) = e_{γW}u_{γδ^{-1}} are matrix units.
  - Absorption moves the indices by words of length ≤ w, so d = n|B_{w+1}|.
  - The rest is the note's extraction ✓.
- **Scope.** Freeness at every point is needed for the partition, as the node says ✓.

## 5. `free-subshift-with-finite-models-forces-rf-group` + `-proof`: PASS (concurs)
- There is a finite cover by {x(h) ≠ x(hγ)}, h ∈ F.
- A finite Y with the (F ∪ Fγ)-patterns of X has y(hγ) ≠ y(h) for some h ∈ F, so γy ≠ y. Hence Γ → Sym(Y) does not kill γ ✓.
- Model test: constant configurations need no freeness ✓.

## 6. `rf-groups-have-free-minimal-subshifts-with-finite-models` + `-proof`: PASS (concurs)
- **Key identity.** For h ∈ K_m∖K_{m+1} with m < n and k ∈ K_n ⊆ K_{m+1}, hk lies in the same K_{m+1}-coset, so x(hk) = x(h) ✓.
- **Two special cosets.** [K_m:K_{m+1}] ≥ 3, so K_m∖K_{m+1} has at least 2 cosets, and there is room for one coset valued 1 and one valued 2 ✓.
- **(a) Finite models.** If FF^{-1}∩K_n = {e}, a window meets K_n at most once, and the configurations y_b realize the patterns ✓.
- **(b) Minimality.** The return sets are syndetic ✓.
- **(c) Freeness.**
  - Let g = σ^{-1}γσ have level m, and take a special coset κK_{m+1} with κg ∉ K_{m+1}. At most one of the two special cosets fails this, because the two cosets are distinct.
  - Then x(ρ) ≠ x(ρg) on κK_{m+1}.
  - A transversal T of K_n, and a limit over the finite T, give freeness at every point ✓.

## 7. Status
- No GAP and no FAIL. One wording note: §1, Kerr–Nowak's ζ.
- The queue for sk-referee-1 is complete through entry 34. Entry 28 was withdrawn by its owner.
