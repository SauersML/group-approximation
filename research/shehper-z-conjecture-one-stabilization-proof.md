---
rg: 2
id: shehper-z-conjecture-one-stabilization-proof
kind: route
title: Proof of the equivalence between the presentations-of-Z conjecture and one-stabilization AC-triviality
target: shehper-z-conjecture-iff-one-stabilization-ac
requires:
  - z-presentations-with-a-trivializing-relator-are-ac-equivalent
---

Write F = F(x_1, …, x_n).

## Two AC composites

**(E1) Replacement.** If x_1 is one of the relators, any other relator r can be
replaced by any r' ≡ r mod ⟨⟨x_1⟩⟩. This is Step 1 of
`z-presentations-trivializing-relator-ac-equivalence-proof`, with x_1 in the role
of r_j. In particular all letters x_1^{±1} can be deleted from r.

**(E2) Swapping two relators.** Relators (a, b) can be swapped by AC moves:
- (a, b) → (ab, b) → (ab, b^{−1}) → (ab, b^{−1}ab);
- conjugate the second relator by b letter by letter, giving (ab, a);
- then (b^{−1}a^{−1}, a) → (b^{−1}, a) → (b, a).

So the order of relators is immaterial.

## (A_n) ⇒ (B_{n−1})

Let S = ⟨y_1, …, y_{n−1} | s_1, …, s_{n−1}⟩ present the trivial group. Let
r_i ∈ F be the free reduction of s_i(x_2 x_1^{−1}, …, x_n x_1^{−1}).

The map α: F(x_1, y_1, …, y_{n−1}) → F with x_1 ↦ x_1 and y_j ↦ x_{j+1} x_1^{−1} is
an isomorphism (its inverse sends x_{j+1} ↦ y_j x_1), and α(s_i) = r_i. Hence
F/⟨⟨r_1, …, r_{n−1}⟩⟩ ≅ ⟨x_1⟩ ∗ ⟨y | s⟩ = Z. In this group x_{j+1} = y_j x_1 = x_1, so
each x_i generates Z.

Take w = x_1, which trivializes the group. By (A_n),
P = ⟨x_1, …, x_n | r_1, …, r_{n−1}, x_1⟩ is AC-trivial. Killing x_1 sends r_i to
s_i(x_2, …, x_n). So by (E1), P is AC-equivalent to
⟨x_1, …, x_n | s_1(x_2, …, x_n), …, s_{n−1}(x_2, …, x_n), x_1⟩. By (E2) and the
relabelling y_j = x_{j+1}, this is the one-stabilization of S, which is therefore
AC-trivial.

## (B_{n−1}) ⇒ (A_n)

Let ⟨x_1, …, x_n | r_1, …, r_{n−1}⟩ present Z with each x_i generating Z, and let w
trivialize.
1. **Reduce w to x_1.** By `z-presentations-with-a-trivializing-relator-are-ac-equivalent`
   with x = x_1, P_w = (r_1, …, r_{n−1}, w) is AC-equivalent to (r_1, …, r_{n−1}, x_1).
2. **Delete x_1 from the other relators.** By (E1), replace each r_i by r_i', the
   word in x_2, …, x_n obtained by deleting its letters x_1^{±1}.
3. **The leftover presentation is trivial.** S' = ⟨x_2, …, x_n | r_1', …, r_{n−1}'⟩
   presents F/⟨⟨r, x_1⟩⟩ = Z/⟨⟨x_1⟩⟩ = 1, since x_1 generates Z. It is balanced in
   rank n−1.
4. **Apply (B_{n−1}).** ⟨x_1, x_2, …, x_n | x_1, r_1', …, r_{n−1}'⟩ is AC-trivial, and by
   (E2) so is P_w.

## Consequences

- **Stable triviality of AK(3).** For AK(3) take n = 3 in the first direction: (A_3)
  makes ⟨x, y_1, y_2 | x, x^3 = y^4, xyx = yxy⟩ AC-trivial (with y_1, y_2 in the roles
  of x, y), so AK(3) is stably AC-trivial after one (AC4) move.
- **Refutation.** Conversely, a proof that this rank-3 presentation is not
  AC-trivial would refute (A_3).

Elementary; no novelty is claimed.
