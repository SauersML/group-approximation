# EX review wave 2, part 8: the K1-kernel of AH component groups (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0.

**Why a separate part.** A reconciliation of census ids against verdict rows, run after part 7 landed, found one census
claim without a verdict:
- `ah-unitary-component-kernel-is-locally-finite`, of lane ex-unitary-higher-brackets, landing `4bddac93b`;
- priority (a), since it constrains every non-nilpotent AH component group.

Until this part landed, the index summary overstated the count by one. It is reviewed here.

**Prerequisites.**
- `block-component-group-class-at-most-excess-plus-two`: PASS in the first wave, part 1 Item 5.
- `toms-trapped-spin-bordism-class`: through its citation route. First-wave PASS on Toms Lemma 7.1, verbatim.

## 8.1 `ah-unitary-component-kernel-is-locally-finite`: PASS

- **(a) Finite kernel.**
  - S_k is the group of sections equal to 1 on X^{(k−1)}. By homotopy extension it maps onto F_k.
  - On each closed k-cell the class h_e(s) ∈ π_k U(r) does not depend on the trivialization, because conjugation by
    the connected group U(r) acts trivially on π_k.
  - Pointwise products give sums, so h is a homomorphism. If h(s) = 0, each cell is null rel boundary, so s ∈ F_{k+1}.
    Hence F_k/F_{k+1} is a quotient of a subgroup of ∏_e π_k U(r).
  - For k ≥ 2r, π_k U(r) is finite (rationally U(r) is a product of odd spheres up to S^{2r−1}). So F_{2r} is finite,
    with order dividing ∏ |π_k U(r)|^{c_k}.
  - N(E) ⊆ F_{2r}: restrict to X^{(2r−1)}, where Π ≅ K^1 in the stable range, and use naturality of κ.
  - Nilpotency comes from the excess bound, and finite direct sums split.
- **(b) Local finiteness.**
  - Onto: ‖φ_{i,∞}(a) − u‖ < 1/4 makes a invertible. Its polar part is within distance 2 of u, so it is in the same
    component.
  - Injective: Toms Lemma 7.1.
  - K_1 commutes with the limit, the maps preserve N(A_i), and filtered colimits of groups are exact. So
    ker κ = lim N(A_i) is locally finite and locally nilpotent, hence the direct sum of its Sylow subgroups.
  - K_1 is abelian, so the commutator subgroup lies in ker κ.
- **(c) Center-by-finite.** H_i′ ⊆ N(A_i) is finite, and H′ is its image. Conjugacy classes of the generators lie in the
  finite sets H′x_j, so the centralizers have finite index, and so does Z(H). A torsion-free group with finite H′ has
  H′ = 1.
- **(d) Amplification.** diag(x_j, 1_m) lives over E^{⊕(1+m)} of rank r(1+m). Once 2r(1+m) > d the stable range makes it
  trivial, since its K_1 class is κ(x_j) = 0.

**Assessment.** This is a sharp structural constraint: nonzero commutators in any unital AH component group have finite
order and die after finite amplification. The node correctly limits non-nilpotency to finite p-group pieces of unbounded
class. No owner message is needed.
