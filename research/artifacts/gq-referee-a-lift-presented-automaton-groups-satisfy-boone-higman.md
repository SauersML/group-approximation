# Referee report (gq-referee-a, proof-gap lens): lift-presented automaton groups satisfy Boone–Higman

**Reviewed:** `lift-presented-automaton-groups-satisfy-boone-higman` and its `-proof` (lane bh-self-similar,
5ff53c09f), read on origin/main.

**Verdict: PASS.** §§1–3 hold, and I found no gap. There are two nits. Theorem A is a separate lane node. Items (S),
(FP3) and (R), Zaremsky's regrouping, and the Vorobets–Vorobets inputs are for the citation lens.

## §1: regrouping keeps the relator kernel and lift-closure (the author asked about this)
- *The recursion.* `ψ_Y` has `s(x,i) = (s(x), i)` and `s|_(x,i) = s|_x`.
  - By the cocycle rule, `(gh)|_(x,i) = g|_(h(x),i) h|_x = (gh)|_x`. So word-level `Y`-sections are exactly the
    `X`-sections, each repeated `m` times.
  - The root permutation on `Y` is `σ_w × id`, which is trivial exactly when `σ_w` is.
  - So the reachable sets coincide, and `S` stays closed under sections for `Y`. ✓
- *The relator kernel.* Consequence 4 of Theorem A gives `N_Y = N`, since the reachable words and their root
  permutations agree. It also follows directly: both actions are faithful actions of the same `G`, by (R), so both
  kernels equal `ker(F → G)` (N1). ✓
- *Lift-closure.* "`w` has trivial root permutation and all `w|_·` lie in `M`" reads identically for `ψ` and `ψ_Y`. So
  the lift ideals of `F` are the same, and `⟨⟨R⟩⟩_lift` is the same subgroup. Theorem A then gives that `V_(md)(G)` is
  finitely presented. ✓

## §2
- *Finite abelianization.* `A` has finitely many eigenvalues, so all but finitely many even `m` have `1/m` outside
  the spectrum, and (R) makes `V^ab` finite.
- *The host.* (S) makes `C = [V,V]` simple. `C` contains `[V_(md), V_(md)] ≠ 1`, so it is nontrivial. Finite index in
  the finitely presented `V` makes it finitely presented. ✓

## §3: all proper cones conjugate, and `δ_e` lands in `[V,V]` (the author asked about this)
- *The embedding.* `L_v` is injective, because the action is faithful. Copies on disjoint cones commute, so `δ_e` is
  an injective homomorphism: the first cone recovers `g`. ✓
- *Conjugacy of proper cones.*
  - Write `n = md`. The complement of a cone at depth `k` is a union of `(n−1)k` cones. Refining one cone raises the
    count by `n − 1`.
  - So two complements of proper cones can be refined to the same number of cones and matched by a
    prefix-replacement bijection. Together with `v ↦ v'` on the cones themselves, this gives `h ∈ V_n`.
  - The conjugation rule gives `hL_v(g)h^(−1) = L_(v')(g)`. So all `L_(v_i)(g)` have the same image `c(g)` in `V^ab`. ✓
- *Landing in `[V,V]`.* The image of `δ_e(g)` in `V^ab` is `e·c(g) = 0`, because `e` is the exponent. So `δ_e(g)` lies
  in `ker(V → V^ab) = [V,V]`.
  - For `e = 1`, `V` is perfect and no cone argument is needed (N2).
  - For `e ≥ 2`, the `e` disjoint cones are automatically proper. ✓

## Consequences
- **Item 1.** For finitely presented `G`, a finite `R` gives `N = ⟨⟨R⟩⟩ ⊆ ⟨⟨R⟩⟩_lift ⊆ N`. Contracting `G` is covered
  by consequence 1 of Theorem A. ✓
- **Item 3.** If `F → G` is injective, then `N = 1`, and `K_∞ ⊆ N` gives `K_∞ = 1 = N`. So `R = ∅` works, and
  `V_d(G)` is finitely presented by consequence 2. The states of Aleshin's automaton are closed under sections. The
  cited freeness results are for the citation lens. ✓
- **The Remark.** It is correct: §3 uses only that `V^ab` is finite, not that `G` is finitely presented.

## Nits
- **N1 (§1).** Note that `N_Y = N` also follows from faithfulness of both actions of `G`. Consequence 4 then serves
  as the effective check.
- **N2 (§3).** Add the cone count `(n−1)k` for the complement of a depth-`k` cone, which is what makes the
  prefix-replacement matching possible. Also note the trivial case `e = 1`.
