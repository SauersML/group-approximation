---
rg: 2
id: fw-inputs-admit-no-twisted-shell-normalization-proof
kind: route
title: Transfix the graph of the shift, then follow the unique infinite forward ray
target: fw-inputs-admit-no-twisted-shell-normalization
requires:
  - genuine-action-shell-envelopes-generalize-the-regular-shell
---

Notation as in the target. "Near equal" means equal off a finite set.

**Step 1: a commensurated graph.** Let `P` act on `N × N` by
`g·(x,y) = (ρ_(φ(g)) x, ρ_g y)`. This is an action, because `φ` is a homomorphism.
Let `Γ = {(x, x+1) : x ∈ N}` be the graph of `s`.
- `g·Γ` is the graph of `ρ_g s ρ_(φ(g))^-1`.
- The hypothesis `s^-1 ρ_g s = ρ_(φ(g))` near says that `ρ_g s ρ_(φ(g))^-1` and `s`
  are near equal. So `g·Γ Δ Γ` is finite, and `Γ` is commensurated.

**Step 2: transfixing.** By FW there is a `P`-invariant `Γ' ⊆ N × N` with `Γ' Δ Γ`
finite.
- Write `Γ'_x = {y : (x,y) ∈ Γ'}` and `Γ'^y = {x : (x,y) ∈ Γ'}`. Invariance gives
  `Γ'_(ρ_(φ(g)) x) = ρ_g(Γ'_x)` and `Γ'^(ρ_g y) = ρ_(φ(g))(Γ'^y)`.
- `D = {x : |Γ'_x| ≠ 1}` is finite and `ρ(φ(P))`-invariant.
  `E = {y : |Γ'^y| ≠ 1}` is finite and `ρ(P)`-invariant. It may contain `0`, whose
  cofibre is empty. That is harmless.
- Let `N_1` be the set of `x ∉ D` whose unique partner `s'(x)` lies outside `E`. It is
  cofinite and `ρ(φ(P))`-invariant, and `s' : N_1 -> N` satisfies
  `s'(ρ_(φ(g)) x) = ρ_g s'(x)` for `x ∈ N_1`, `g ∈ P`.
- `s'` is injective, because points outside `E` have one partner. It is near equal to
  `s`, since `Γ' Δ Γ` is finite.
- Its image `M_1 = s'(N_1)` is `ρ(P)`-invariant: `ρ_g s'(x) = s'(ρ_(φ(g)) x)`. So the
  finite set `K = N − M_1` is `ρ(P)`-invariant.

**Step 3: the orbit graph of `s'`.** Draw an edge `x -> s'(x)` for `x ∈ N_1`. Every
point has at most one incoming and at most one outgoing edge.
- Choose `n_0` above the finite set where `s'` differs from `s` or is undefined, and above
  `K`. Then every `n > n_0` has `s'(n) = n+1`, so all `n > n_0` lie on one forward-infinite
  path.
- Follow that path backwards from `n_0 + 1`. It stays in the finite set `[0, n_0]` and
  cannot repeat, since the forward orbit of `n_0 + 1` is infinite and `s'` is injective.
  So it stops at a point `k_0 ∈ K`.
- This gives the **main ray** `x_0 = k_0 -> x_1 -> x_2 -> …`, every `x_j ∈ N_1`,
  containing every `n > n_0`.
- Every other component lies in `[0, n_0]`.
  - A path starting at a point `k ∈ K − {k_0}` cannot reach the main ray: each `x_i`,
    `i >= 1`, already has its predecessor `x_(i-1)`, and `k_0` has none.
  - Nor can it enter a cycle, by injectivity.
  - So `s'^j(k)` is undefined for `j > n_0 + 1`.

**Step 4: the induction.** For `g ∈ P` and `j >= 0`,

    ρ_g(x_j) = s'^j(ρ_(φ^j(g)) k_0).

- For `j = 0` this is trivial.
- For `j >= 1`, `x_(j-1) ∈ N_1`, so `ρ_g(x_j) = ρ_g s'(x_(j-1)) = s'(ρ_(φ(g)) x_(j-1))`.
  Here `ρ_(φ(g)) x_(j-1) ∈ N_1` by `ρ(φ(P))`-invariance of `N_1`.
- The induction hypothesis for the element `φ(g)` gives
  `ρ_(φ(g)) x_(j-1) = s'^(j-1)(ρ_(φ^j(g)) k_0)`.

**Step 5: conclusion (item 1).**
- `k' = ρ_(φ^j(g)) k_0` lies in `K`, which is `ρ(P)`-invariant. By Step 4, `s'^j(k')` is
  defined.
- For `j > n_0 + 1`, Step 3 forces `k' = k_0`, and then `ρ_g(x_j) = s'^j(k_0) = x_j`.
- So `ρ_g` fixes every `x_j` with `j > n_0 + 1`, which is all but finitely many points of
  `N`. Thus `ρ_g` has finite support.

**Item 2.** If every `ρ_g`, `g ≠ 1`, has infinite support, then `ρ : P -> NearSym(N)` is
injective.
- (a) If `s^-1 ρ(P) s <= ρ(P)`, then `φ(g) = ρ^-1(s^-1 ρ_g s)` is an endomorphism of `P`
  satisfying item 1's hypothesis. So every `ρ_g` has finite support, which contradicts
  `P ≠ 1`.
- (b) If `s ρ(P) s^-1 = ρ(P)`, then conjugating by `s^-1` gives `ρ(P) = s^-1 ρ(P) s`,
  and (a) applies.

**Item 3.** Apply item 1 to `H`, with the restricted action and the restricted twist.
Item 1 never uses that `H` is infinite. A nontrivial element of `H` cannot have finite
support when all nonidentity elements of `P` have infinite support.

**Inputs.** FW is used only in Step 2. That (T) implies FW is standard: the cocycle
`g ↦ 1_(gA) − 1_A` of a commensurated subset is bounded under (T), and a commensurated
subset with bounded defect is transfixed (Brailovsky–Pasechnik–Praeger, Proc. AMS 123
(1995)). The same sentence is used in `almost-v-fw-subgroups-act-through-finitely-many-germs`.
The genuine-action shell framework is used only to name the gate in the consequences.
