# Adversarial check: `wreath-recursion-thompson-groups-inherit-fn` (bh-free-06, dying-kernel transfer) (bh-refute, 2026-09-18)

This item was assigned by the coordinator. I checked `wreath-recursion-thompson-groups-inherit-fn-proof`, §1–§7.
The standard inputs were not re-derived: Gabriel–Zisman fractions, Quillen's Theorem A, the collage lemma,
Thomason's theorem, and the Belk–Forrest grounding theorem as stated in Belk–Matucci Thm 6.2.

Verdict: **PASS**, with one clarification nit (N1).

## Checks

- **§1: the cloning category.**
  - `b·(x,c) = (π_b(x), b|_x c)` is an action because `ψ` is a homomorphism.
  - Composition is `(α^*F' ∘ F, α'α_*)`.
  - "Left cancellation" is the statement `f∘s = g∘s ⇒ f = g`. It holds because forest composition cancels
    and `s_*` is an isomorphism.
  - It is compatible with the failure of the other cancellation: `f∘a = f` for `a ∈ ∏ K_{T_i}`. That is exactly
    where a non-injective `ψ` enters.
- **§2, Lemma 1.** The Ore condition comes from common refinements. The cancellation axiom holds with `t = id`.
  The comma categories are filtered, so Quillen A gives `B𝒞 ≃ B𝒢`.
- **§2, Lemma 2.**
  - `L(f) = L(g)` iff `F = F'` and `α' = αk` with `k ∈ J^m`. This uses `∪_T K_T = J`.
  - `J` is `ψ`-saturated, and `ψ̄` is injective on `B/J`: an element fixing level 1 with sections in `J` lies in
    some `K_{j+1}`.
  - So `V(B,ψ) ≅ V(B/J,ψ̄)`, and this maps isomorphically onto `V(G)` iff `J = K`. **Correct.**
- **§3.**
  - `Γ_m` acts on `𝒞_{<m}↓m` by postcomposition. The action is free: `βα = α` forces `β = 1`.
  - `End(m) = Γ_m`, which is EI. So the collage pushout applies, and `(k−1)`-connected `L_m` gives a
    `k`-connected attaching map.
- **§4: Stein retraction.** `h_f : f → e(f)` is a natural transformation `id ⇒ ir`, and `ri = id`.
- **§5: polyhedral join.**
  - Automorphisms of an elementary arrow are `∏_{carets} K_1`, by the precomposition-stabilizer fact.
  - `Hom(f', f) ≠ ∅` iff `M(f) ⊆ M(f')` with matching decorations. It is an `Aut(f)`-torsor.
  - Thomason turns the Grothendieck construction over decorated matchings, with projection transitions, into
    `hocolim ∏ BK_1`.
  - A hocolim over a face poset of products with projections is the polyhedral join. The empty matching is
    excluded, because objects of `𝒞_{<m}↓m` have at least one caret. **Correct.**
- **§6, Lemma 5.** Re-derived.
  - The simplices through `v` contribute `Y_v * (∗_{lk v} Y'_u)`.
  - `W` is `(n−2)`-connected by induction, since the link is wCM of dimension `n−1` and nonempty.
  - `Y_v * W` is `(n−1)`-connected, and `CY_v * W` is contractible, so each cone-replacement is an iso on
    `π_{<=n−1}`.
  - At the end the space is `≃ L`. **Correct.**
- **§7, Lemma 7.**
  - The homotopy-quotient values are `(BK_1)_{h(B/K_1)} ≃ BB`, times factors `B^{unmerged}` and finite groups.
  - There are finitely many `Γ_m`-orbits of decorated matchings, because `Γ_I = B ≀ Sym(I)` is simply
    transitive on `Ω_I`. The infinitely many `ψ(B)`-classes collapse, which is what makes this work.
  - So the values have type `F_n`, and the hocolim has finite `n`-type. **Correct.**
- **§8.** The Nekrashevych inputs are quoted with line numbers: `pr:lengththree`, `pr:kernelcontracting`,
  `pr:expandingpi1`, and the Corollary at l.1729. The finite-presentation re-proof is the case `n = 2`.

## Nit

- **N1 (§4 functoriality).** For `g : f_1 → f_2`, transported bottom carets of `f_2` lie among those of `f_1`.
  `E_{F_1}` can be strictly larger: it also contains carets of `g`'s forest on strands that `F_2` leaves
  unsplit. The morphism `u` adds exactly those, and `e(f_2)∘u = e(f_1)` is still elementary. This is implicit in
  "the bottom carets of `f_2` are … bottom carets of `f_1`", but should be said.

## Lesson for general BH

Finiteness properties of Thompson-like hosts transfer through non-faithful presentations of the input. The
kernel of the recursion appears only as the automorphism group `K_1` of elementary arrows, and polyhedral joins
over weakly Cohen–Macaulay complexes are as connected as the base whatever the fibres. So a finiteness proof
for a BH host may use any `F_n` cover of the input with dying kernel, for example `π_1` of an expanding
dynamical system. This makes `F_∞` reachable for Röver–Nekrashevych hosts of expanding maps (`V_f` for
hyperbolic PCF rational maps). It bears directly on BBMZ's question whether full contracting RSGs are of
type `F_∞`.
