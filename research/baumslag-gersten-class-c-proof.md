---
rg: 2
id: baumslag-gersten-class-c-proof
kind: route
title: Classify the points of the line-sink seed by the tree, reduce rigidity to the signed lines by the derived-subshift theorem, and prove it there by up-monotone axis chains plus downward sign propagation
target: baumslag-gersten-groups-lie-in-class-c
requires:
  - quantum-rigidity-is-decided-on-the-derived-subshift
  - relative-seeds-glue-graphs-of-groups-into-class-c
  - locally-finite-splittings-preserve-rigid-sft-compactifications
---

Notation is that of the target. `P ≤ Q` means `PQ = QP = P`. As in the parents, this order is transitive, and a
pattern of diameter `≤ 2D` that never occurs has vanishing product (expand to a `D`-ball).

## 0. The tree

- **Up and down.** `h a^j b^(-1) = h b^(-1) a^(nj)`, so all `h a^j b^(-1)` lie in the one up coset `hb^(-1)⟨a⟩`.
  `h a^(nm+i) b = h a^i b a^m`, so the down cosets are `h a^i b⟨a⟩`, `i ∈ Z/n`. Every down neighbour has
  `h⟨a⟩` as its up neighbour.
- **Axis.** `b^k⟨a⟩` has up neighbour `b^(k−1)⟨a⟩` and down neighbour `b^(k+1)⟨a⟩` (`i = 0`), so it is a line.
- **Odometer.** The depth-`d` descendants of `⟨a⟩` are `a^m b^d⟨a⟩`, and `a^m b^d⟨a⟩ = a^(m')b^d⟨a⟩` iff
  `m ≡ m' mod n^d`. So the down-ends below `⟨a⟩` are `Z_n`, and `a` acts on them by `+1`.
- **Up-rays.** The up-ray from every vertex meets every line through `ω`.

## 1. (RS1) and local forcing

**The seed propagates along `b`.** Let `c(1) = *`.
- By (Ax), `b` is axis, and by (Sg), `c(b) = *`.
- By (LR), `b^(-1)` is axis, and (Sg) applied to `(b^(-1), 1)` gives `c(b^(-1)) = *`.
- Inductively, `*` sits at every `b^k`.

**The rest follows.**
- By (T) and (C), the coset `b^k⟨a⟩` carries `σ`.
- (LR) at `b^k` makes every down neighbour of `b^k⟨a⟩` other than `b^(k+1)⟨a⟩` non-axis.
- A vertex below a non-axis vertex is non-axis, by the up clause of (LR).
- Every vertex off the axis lies below such a neighbour, by §0 (up-rays). So it carries `↑`.

Each deduction reads one ball of radius `≤ n + 2` around sites already forced. So `y_b` is **locally forced**, and it
is the only point of `Y` with the seed at `1`.

**The formula is a point of `Y`.**
- (Sg) holds at `h = b^k a^(nj)`, since `hb = b^(k+1) a^j` and `σ(nj) = σ(j)`.
- For `j ≢ 0 mod n`, the element `b^k a^j b` lies in a non-axis coset.

**Stabilizer.** An element fixing `y_b` preserves its `*`-set `⟨b⟩`, so it lies in `⟨b⟩`, and `b` fixes the
formula. So `Stab(y_b) = ⟨b⟩`.

## 2. Classification of points, and (RS2)

Let `x ∈ Y` and let `A_x` be its set of axis vertices.
- **`A_x` is empty or one line through `ω`.**
  - By (LR), `A_x` is closed under going up, and each of its vertices has exactly one child in it.
  - Two distinct lines through `ω` merge going up, and at the merge vertex both children would be axis.
- **If `A_x` is a line `L` and some `*` occurs at `h`,** then (Ax) and (Sg) put `*` at `hb^k` for all `k`, as in §1.
  So `L = h.(axis of b)` and `x = h.y_b`, which is type (α).
- **If `A_x = L` and no `*` occurs,** then by (C) each axis coset is constant, `+` or `−`. By (Sg) adjacent axis
  cosets agree. This is type (β).
- **If `A_x = ∅`,** the point is type (γ).

All three types satisfy the rules, so they are exactly the points of `Y`.

**Limits.**
- **Signed lines.** Given `(L, ε)`, translate so that `⟨a⟩ ∈ L`, and let `ζ ∈ Z_n` be its down-end. Choose
  `m_k ≡ ζ mod n^k` with `ε m_k → +∞`. Then:
  - the axis `a^(m_k).(axis of b)` of `a^(m_k).y_b` agrees with `L` on larger and larger balls (§0, odometer);
  - its `*`-set `a^(m_k)⟨b⟩` leaves every finite ball, since the cosets `a^m⟨b⟩` are distinct and a ball meets
    finitely many of them;
  - on `⟨a⟩` the letter at `a^j` is `σ(j − m_k)`, which tends to `ε`.

  Every limit point is a point of `Y` with axis `L`, no `*`, and sign `ε` on `⟨a⟩`. By the classification, it is
  `(L, ε)`.
- **The constant point.** `↑^(V_n)` is the limit of translates of any signed line whose axis leaves every ball.

So `Y = cl(V_n.y_b)`, which is (RS2).

**Derived subshift.** The points of type (α) are isolated, because the seed pattern isolates them. Types (β) and
(γ) are limits of other points: vary the down-end, or push the line away. So `U = V_n.y_b` and
`Y' = (β) ∪ (γ)`.

## 3. `Y'` is quantum rigid

Let `(E)` be a `D`-family for `Y'` with `D ≥ 2`. Every window used below lies in `{h, ha, hb^(±1), h a^i b}`, which
has diameter `≤ n + 2`; take `2D ≥ n + 2`. Put `X(h) = E_(axis,+)(h) + E_(axis,−)(h)`. Then `E_(axis,*)(h) = 0`, since
`*` does not occur in `Y'`, and `E_↑(h) = 1 − X(h)`.

1. **Vertex idempotents.** Axis-ness and the sign are constant along `a` in `Y'`, and `h`, `ha` are adjacent. So
   `X(h) = X(ha)` and `E_+(h) = E_+(ha)`, where `E_± = E_(axis,±)`. Write `X_v`, `E_+^v` for the common values on the
   vertex `v`.
2. **Up-monotone chains.** For a child `c` of `v`, "`c` axis and `v` not" never occurs, so `X_c ≤ X_v`. By
   transitivity, `X_w ≤ X_v` whenever `w` lies below `v`.
3. **Incomparable vertices.** Two children `c ≠ c'` of `u` are never both axis, so `X_c X_(c') = X_(c') X_c = 0`. If
   `w` lies below `c` and `w'` below `c'`, then `X_w X_(w') = X_w X_c X_(c') X_(w') = 0`, and likewise in the other
   order.
   - Any two vertices are either comparable (step 2) or lie below distinct children of the vertex where their
     up-rays meet (this step). So all `X_v` commute.
4. **Downward sign propagation.** Let `c = h a^i b⟨a⟩` be a child of `v = h⟨a⟩`. Put `h' = h a^i`, so
   `h'b ∈ c` and `E_+(h') = E_+^v`. The patterns "`h'` and `h'b` axis with different signs" and "`h'b` axis,
   `h'` not" never occur. Hence:
   - `E_+^v X_c = E_+^v E_+^c`;
   - `X_v E_+^c = E_+^v E_+^c`;
   - `E_+^c = X_v E_+^c`.

   So `E_+^c = E_+^v X_c = X_c E_+^v`.
   - **Induction down a chain.** Suppose `v = c_0, c_1, …, c_m = w` and `E_+^(c_(m−1)) = E_+^v X_(c_(m−1))`. Then,
     using `X_(c_m) ≤ X_(c_(m−1))`, `E_+^v X_w = E_+^v X_(c_(m−1)) X_w = E_+^(c_(m−1)) X_w = E_+^w`. The same
     computation holds on the other side.
   - **So:** for every `w` below `v`, `E_+^w = E_+^v X_w = X_w E_+^v`.
5. **All letters commute.** Let `v`, `w` be vertices and `u` the vertex where their up-rays meet. Then
   `E_+^v = E_+^u X_v` and `E_+^w = E_+^u X_w`, and `E_+^u` commutes with `X_v` and `X_w` by step 4. So:
   - `E_+^v E_+^w = E_+^u X_v X_w = E_+^w E_+^v`;
   - `E_+^v X_w = E_+^u X_v X_w = X_w E_+^v`.

   With `E_− = X − E_+` and `E_↑ = 1 − X`, every pair of site idempotents commutes. `∎`

## 4. Conclusion

- **(RS3).** By §1, every isolated point of `Y` is a translate of the locally forced `y_b`. By §3, `Y'` is
  `D`-rigid for `2D ≥ n + 2`. `quantum-rigidity-is-decided-on-the-derived-subshift` (part 2) makes `Y` `D'`-rigid
  for all large `D'`, over every field.
- **(RS1)–(RS3).** With §1 and §2 these give `(V_n, ⟨b⟩) ∈ 𝓡`.
- **`BG_n`.** Its graph of groups has one vertex `V_n` and one loop edge `Z`, with images `⟨a⟩` and `⟨b⟩`.
  - `(V_n, ⟨a⟩) ∈ 𝓡` by the gluing theorem (statement 1, second bullet, for `V_n` over its vertex group `⟨a⟩`).
  - `V_n ∈ 𝒞` by `locally-finite-splittings-preserve-rigid-sft-compactifications`.

  Statement 1 of `relative-seeds-glue-graphs-of-groups-into-class-c`, with `C = 1`, gives `BG_n ∈ 𝒞`.
- **Graphs of groups.** Conjugates `g⟨b⟩g^(-1)` are handled by translating the seed. A ball around `1` containing
  the seed's new position isolates it. Finite-index subgroups of `⟨a⟩` are in `𝓡` by statement 1 of the gluing
  theorem applied to `(⟨a⟩, k⟨a⟩)`. `∎`
