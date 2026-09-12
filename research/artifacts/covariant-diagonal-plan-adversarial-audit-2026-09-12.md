# Adversarial audit of the covariant-diagonal plan for the two-root gate

Lane `w4-r4-adversary`, 2026-09-12, at the request of `w3-strategist-neg`.
- **Target:** `leavitt-two-root-defect-piece-forces-covariant-diagonal`, with route
  `el3-rank-triviality-via-defect-piece-covariance`.
- **Plan:** artifact `research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md`, Section 3.

## 0. Verdict

* **The claim is not refuted.** Its route stays valid. But the claim is equivalent to the
  characteristic-two gate, because its conclusion holds in no rank ultraproduct and no nonzero corner of
  one (Section 2, Corollary 3).
* **The first lemma is automatic and carries no defect information.**
  - It is an instance of a general rigidity: every covariant, refinement-monotone family of principal
    right or left ideals indexed by proper cylinders is constant (Section 2, Theorem 2).
  - It holds in every rank model, whatever `N_23 N_12` is.
  - Every orthogonal cylinder family is itself monotone. So "orthogonality is the missing input" says
    only that the missing input is the contradiction.
* **Everything the root-span coincidence yields** (Section 3): the all-coefficient identity on a frame of
  shape `(a0, b, a1)` forces triviality. That is the known direction, nontrivial ⟹ violation. Its proof
  here is group-theoretic and uses no ring rank model.
* **Kill tests** (Section 4):
  - (a) fails, since countable joins exist;
  - (b) is consistent, since the Toeplitz algebra has no depth-changing units;
  - (c) is the gate itself.

## 1. Countable joins exist in rank ultraproducts

Let `M = prod_omega M_(n_i)(k) / d_omega`, with `omega` nonprincipal on `N` and `d_omega` the rank-null
ideal. `M` is von Neumann regular, and `rk` is faithful on principal right ideals: if `A ⊆ B` and
`rk A = rk B`, then `A = B`, because `B = A ⊕ C` with `rk C = 0`.

**Proposition 1.** For a countable family `(A_n)` of principal right ideals, there is a principal right
ideal `J` that contains every `A_n` and lies inside every right ideal containing them all. Moreover
`rk J = sup_n rk(A_1 + ... + A_n)`. Dually, countable meets exist.

*Proof.*
1. **Existence.** Put `J_n = A_1 + ... + A_n`, which is principal, say `f_n M`. Let `s = sup rk J_n`.
   The conditions `e^2 = e`, `e f_n = f_n` for all `n`, and `rk(e) <= s` are finitely satisfiable, by
   `e = f_N`. They are closed conditions in the rank metric. Metric ultraproducts along a nonprincipal
   ultrafilter on `N` are countably saturated, so some idempotent `e` satisfies all of them.
2. **Leastness.** If `K` contains every `A_n`, then `K ∩ eM` contains every `J_n`, so its rank is at
   least `s = rk(eM)`. By faithfulness, `eM ⊆ K`.
3. **Meets.** Same argument, with `f_n e = e` and `rk(e) >= s − 1/m` for every `m`.

QED

So the spans `V_(w,w')` of the plan are well defined, and kill test (a) does not kill.

## 2. Monotone rigidity

Let `X = {0,1}^N`, `V` Thompson's group acting by prefix replacement, and `C` the set of proper cylinders.
Let `sigma : V -> M^x` be a homomorphism. The same statement holds in a nonzero corner `qMq`, which is a
rank ultraproduct after renormalizing, with `ι_0(V)` acting on the subcylinders of `[0]`.

**Theorem 2.** Let `(A_w)_(w in C)` be principal right ideals with:
- **covariance:** `sigma(v) A_w = A_(vw)` whenever `v` carries `w` onto the cylinder `vw` by prefix
  replacement;
- **monotonicity:** `A_(w0) ⊆ A_w` and `A_(w1) ⊆ A_w`.

Then `A_w` is the same ideal for every `w in C`. For left ideals the same holds with
`A_w sigma(v)^-1 = A_(vw)`.

*Proof.*
1. **Common rank.** Any two proper cylinders `u, w` are leaves of complete prefix codes whose other
   leaves cover nonempty complements. So some `v` carries `w` onto `u`, and `rk A_w` is a constant `c`.
2. **Within a first letter.** `A_(w0) ⊆ A_w` with equal rank, so they are equal. Hence
   `A_(0x) = A_[0]` and `A_(1x) = A_[1]` for all words `x`.
3. **Across letters.** Take `v` with leaf map `(00, 01, 1) -> (00, 1, 01)`. It fixes `[00]` and carries
   `[01]` onto `[1]`. So `A_[0] = A_[00] = sigma(v) A_[00]`, and `sigma(v) A_[0] = sigma(v) A_[01] = A_[1]`.
   Therefore `A_[0] = sigma(v) A_[0] = A_[1]`.

QED

**Corollary 3.** Let `(e_w)` be idempotents with `e_(w0) + e_(w1) = e_w`, orthogonal summands, and
`sigma(v) e_w sigma(v)^-1 = e_(vw)`. Then `e_w = 0` for every proper `w`.

*Proof.* Orthogonality gives `e_w e_(wi) = e_(wi)`, so `A_w = e_w M` is covariant and monotone. By
Theorem 2, `e_(w0) M = e_(w1) M`. So `e_(w0) = e_(w1) m` for some `m`, and
`e_(w0) = e_(w0) e_(w0) = e_(w0) e_(w1) m = 0`. QED

This is the conclusion of `thompson-v-cantor-system-has-no-covariant-rank-model`, from monotonicity alone,
with no additivity of rank used. So the conclusion of the diagonal claim holds in no rank model and no
nonzero corner.

## 3. Root-group spans: what the coincidence carries

**Setting.**
- `R = L_(F_2)(1,2)`, and `sigma : R^x -> M^x` a characteristic-two rank model.
- For disjoint cylinders `w, w'` with `w ∪ w' != X`, put `N_(w,w')(y) = sigma(1 + s_w y t_(w')) - 1`.
- `V_(w,w')` is the join of `N_(w,w')(y) M` over `y in R`, and `L_(w,w')` is the join of `M N_(w,w')(y)`.

**Lemma 4 (coincidence).**
* **Covariance.** If `v` carries `w, w'` onto cylinders, then `sigma(v) V_(w,w') = V_(vw,vw')` and
  `L_(w,w') sigma(v)^-1 = L_(vw,vw')`. This is because `v s_w y t_(w') v^-1 = s_(vw) y t_(vw')`.
* **Monotonicity in both slots.** `s_(w0) y t_(w') = s_w (s_0 y) t_(w')` and
  `s_w y t_(w'0) = s_w (y t_0) t_(w')`. So the root group at a refined pair lies in the root group at
  the pair, and `V` and `L` grow when a slot grows.
* **Common rank.** `V` acts transitively on such pairs, so all the `V`'s share one rank, and so do the
  `L`'s.
* **Conclusion.** By faithfulness, `V_(w0,w') = V_(w,w') = V_(w,w'0)`, and the same for `L`. Both
  depend only on the branch component of the pair.

**Proposition 5.** Let `a, b` be disjoint cylinders with `a ∪ b != X`. If
`N_(b,a1)(y) N_(a0,b)(z) = 0` for all `y, z in R`, then `sigma` is trivial.

*Proof.*
1. **Reduce to the pair `(a,b)`.** The left annihilator of `V_(a0,b)` contains every
   `M N_(b,a1)(y)`, so it contains their join: `L_(b,a1) V_(a0,b) = 0`. By Lemma 4,
   `L_(b,a1) = L_(b,a)` and `V_(a0,b) = V_(a,b)`. So `N_(b,a)(y) N_(a,b)(z) = 0` for all `y, z`.
2. **Swap the roles.** Conjugating by the `v` in `V` that swaps `a` and `b` and fixes the complement
   gives `N_(a,b)(y) N_(b,a)(z) = 0` too.
3. **The Weyl element.** Put `X = N_(a,b)(1)` and `Y = N_(b,a)(1)`, so `XY = YX = 0`. Let `j` be the
   corner embedding `EL_2(R) -> R^x` on `{a,b}`. Then `w = j([[0,1],[1,0]])` has
   `sigma(w) = (1+X)(1+Y)(1+X) = 1 + X^2 + Y`, and `w j(x_12(1)) w^-1 = j(x_21(1))`, so
   `sigma(w) X = Y sigma(w)`.
   - The left side is `X + X^3`, and the right side is `Y + Y^2`.
   - Multiplying on the left by `X` gives `X^2 (1 + X^2) = 0`. Since `1 + X^2 = sigma(j(x_12(2)))` is a
     unit, `X^2 = 0`.
   - So `X = Y + Y^2`. Multiplying on the left by `Y` gives `0 = Y^2 (1 + Y)`, so `Y^2 = 0` and `X = Y`.
4. **Simplicity.** Now `sigma(j([[0,1],[1,1]])) = (1+X)(1+Y) = 1 + X + Y + XY = 1`. The element
   `j([[0,1],[1,1]])` is not `1`, and `R^x` is simple (`binary-leavitt-unit-group-is-simple`). So
   `sigma` is trivial.

QED

**What this shows.**
- **The known direction, and no more.** Every nontrivial model violates the all-coefficient identity on
  every frame `(a0, b, a1)`. That is the easy direction of corner locality, reproved here with no ring
  rank model: it uses `V`'s depth-changing units, faithfulness of rank and simplicity.
- **How the coincidence can be used.** Only through products of image and co-image data, as here. Any
  covariant family built from spans, co-images, their joins or their meets is monotone or antitone in
  the cylinder, so by Theorem 2 it is constant. It never produces orthogonal pieces.
- **Odd characteristic.** The same computation goes through with signs, using that `R^x` is perfect and
  simple modulo scalars.

## 4. The three kill tests

* **(a) The join issue.** Not a kill: Proposition 1 gives joins and meets.
* **(b) The Toeplitz Kazhdan group** `EL_3(C(X,F_2) ⋊ Z)`
  (`kazhdan-groups-without-fd-reps-violate-two-root-identity`).
  - The coefficient algebra has an invariant trace, so no unit carries an odometer idempotent of trace
    `2^-j` onto one of trace `2^-(j+1)`.
  - So step 1 of Theorem 2 fails at every depth. Monotone families refine strictly, and in the natural
    model the ranges of the phase idempotents form an honest diagonal, covariant under depth-preserving
    symmetries.
  - The mechanism does not transfer to this group, which is consistent. The Leavitt input it uses is the
    depth-changing transitivity, the same input that makes Corollary 3 hold.
* **(c) A violating model with no orthogonal `e_w`.** Corollary 3 says no rank model has one. So this test
  is the gate itself, and no test separates the claim from the gate.

## 5. What a proof of the diagonal claim must do

* **There is no intermediate target.** The claim's conclusion is contradictory (Corollary 3). A proof
  must derive a contradiction from `delta > 0` directly, and every covariant monotone object it builds
  on the way is constant (Theorem 2).
* **Families that are not covariant.** The plan's objects could still help if they were covariant only
  under depth-preserving symmetries, where honest diagonals can exist, as in Section 4(b). The
  contradiction then needs a rank comparison between depths `k` and `k+1`.
  - A depth-changing unit is what supplies that comparison.
  - By Lemma 4, such units act on image and co-image data only up to coincidence, so they give equality
    of spans, not halving of ranks.
  - What is missing is a rank inequality `rk(piece at depth k+1) <= rk(piece at depth k) / 2` for some
    non-span piece built from the defect.
* **Root spans alone yield only Proposition 5,** the known direction.
