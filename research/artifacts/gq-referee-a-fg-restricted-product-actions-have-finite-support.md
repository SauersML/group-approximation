# Referee report (gq-referee-a, proof-gap lens): finitely generated restricted-product actions have finite support

**Reviewed:** `fg-restricted-product-actions-have-finite-support` and its `-proof`, read on origin/main (db7acc3f9). No
referee had reviewed it before.

**Verdict: PASS.** Parts 1–3 and the consequences hold, and I found no gap. There are two nits. The inputs "`u(1/p)`
moves `o_p`" and "automorphisms of `∏'_p T_p` are coordinatewise" are cited nodes. I rechecked the first directly.

## Checks
- **The support cocycle.**
  - Write `j = σ_g(i)`. Then `(gho)_j = g_i((ho)_i)`. If `i ∉ D(h)`, this is `g_i(o_i) = (go)_j`, and it differs from
    `o_j` only if `j ∈ D(g)`. So `D(gh) ⊆ D(g) ∪ σ_g(D(h))`, with `σ_(gh) = σ_g σ_h` (N1).
  - `h^(−1)` is monomial, with `σ_(h^(−1)) = σ_h^(−1)` and components `h_i^(−1)`. So
    `(h^(−1)o)_i ≠ o_i ⟺ σ_h(i) ∈ D(h)`, and `D(h^(−1)) = σ_h^(−1)D(h)`, of the same size. ✓
- **Part 1.** By induction, `D(f_1⋯f_l) ⊆ ⋃_k σ_(f_1⋯f_(k−1))(D(f_k))`. Each term has at most `s` elements and lies in
  `σ(H)·S`, since `S` includes the `D(f^(−1))`. ✓
- **Part 2.**
  - If all `σ_f = id`, then `D(h) ⊆ S` for every `h`, so `h_i(o_i) = o_i` for `i ∉ S`. Hence `h` and `h^(−1)` both
    map `Ω_S` into itself.
  - *Convexity.* The distance on a restricted product of connected graphs is `d = Σ_i d_i`. A path that changes a
    coordinate in which its endpoints agree is strictly longer than the endpoints' distance. So geodesics between
    points of `Ω_S` stay in `Ω_S`. ✓
- **Part 3.** The coset action on `∏'(G_i/K_i, K_i)` is coordinatewise, with `D(g) = {i : g_i ∉ K_i}`. So `h_i ∈ K_i`
  for `i ∉ S`, and `SL_n(A_f) = ∏'(SL_n(Q_p), SL_n(Z_p))` is an instance. ✓
- **The consequences.**
  - *`u(1/p)` moves `o_p`.* `x_12(1/p)Z_p^n` contains `e_2 + e_1/p ∉ Z_p^n`, and it has the same covolume as
    `Z_p^n`. So it is a different lattice and not homothetic to `Z_p^n`, and the vertex moves. `Aff(Q)` enters
    through `[[a,b],[0,1]]`.
  - *Coordinatewise hosts.* A finitely generated coordinatewise `H ⊇ Γ` would fix `o_p` for `p ∉ S`, a contradiction.
  - *Monomial hosts.* `p ∈ D(u(1/p)) ⊆ σ(H)·S`, so all prime factors lie in finitely many `σ(H)`-orbits.
    `D(u(1/m!)) ⊇ {p ≤ m}` gives `|u(1/m!)|_F ≥ π(m)/s`. ✓
  - The "Permanence theorems" bullet is interpretive. Its word-length bound `2Ω(m!)/C` is cited from
    `sl-2-q-root-group-is-parabolic-in-every-prime-factor`, and I did not recheck it.

## Nits
- **N1 (Step 1).** State `σ_(gh) = σ_g σ_h`. The induction in Step 2 uses it through `σ_(f_1⋯f_(k−1))`.
- **N2 (Consequences).** "Contains `Γ` acting in this way" should say "with `Γ` acting by its given diagonal action,
  with the same base points `o_p`". The obstruction concerns this particular embedding, not every action of `Γ` on
  `Ω`.
