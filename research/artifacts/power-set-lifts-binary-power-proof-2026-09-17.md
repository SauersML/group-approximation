# Select a point from each set for non-surjectivity, and collapse one site against the all-A background for non-injectivity

*Attempt artifact (2026-09-17), formerly route `power-set-lifts-binary-power-proof` into `power-set-lifts-never-give-binary-power-witnesses`, requires []. Demoted from the graph because referee lens 1 of two returned *refuted*: the numbered results hold, but the target's 'Families of sets' paragraph is asserted and proved nowhere ('translation-closed' is undefined), and the step-7 citation does not say what is used while `requires` is empty. Lens 2 returned *survives*. Restore it as a route once those are fixed and a full referee pass survives.*

This is a complete direct proof. The notation is that of the target.

1. **`|S| >= 2`.** If `S = {s}`, then `f(y) = pi(y_s)` for some `pi: A -> A`, and `tau(x)(g) = pi(x(gs))`.
   - Injectivity of `tau` forces `pi` injective: compare two constant configurations.
   - So `pi` is a bijection, and `tau` is surjective: given `y`, put `x(h) = pi^(-1)(y(h s^(-1)))`.

   This contradicts strictness. (If `S` is empty, `tau` is constant and not injective.)
2. **Non-surjectivity.** Pick `y in A^G` outside `tau(A^G)` and let `Y(g) = {y(g)}`. Suppose `Phi(X) = Y`.
   - If some `X(h)` were empty, then `Phi(X)(g) = ∅` for every `g` with `h in gS`. So every `X(h)` is nonempty.
   - Choose `x(h) in X(h)` for every `h`. Then `tau(x)(g) = f((x(gs))_s)` lies in `f(prod_s X(gs)) = {y(g)}`.
   - So `tau(x) = y`, a contradiction.

   The same argument applies to `Phi*`, which takes values in `P*(A)^G` because `f` of a product of nonempty
   sets is nonempty.
3. **`Phi` is not injective.** Let `X` be the all-`∅` configuration. Let `X'` be `∅` everywhere except
   `X'(1) = A`.
   - Every window `gS` has at least two elements by 1, so it contains a site other than `1`, where both
     configurations are `∅`.
   - So `Phi(X) = Phi(X')` is the all-`∅` configuration, while `X ≠ X'`.
4. **Readability.** Suppose `f` is not readable at `a`. Let `X` be the all-`A` configuration and `X'` agree with
   it except `X'(1) = A \ {a}`, which is nonempty.
   - For every `g`, `Phi*(X)(g) = I := f(A^S)`.
   - If `1 ∉ gS`, then `Phi*(X')(g) = I`.
   - If `1 in gS`, then `1 = gs` for exactly one `s`, and `Phi*(X')(g) = f({y : y_s ≠ a})`.

   This set is contained in `I`. It misses some `b in I` only if every preimage of `b` has `y_s = a`, which
   non-readability excludes. So `Phi*(X') = Phi*(X)`, and `Phi*` is not injective. No property of `G` is used.
5. **Balanced and readable implies one coordinate.** For every `a` choose `s_a`, `b_a` with
   `f^(-1)(b_a) ⊆ C(s_a, a) := {y : y_(s_a) = a}`.
   - Both sets have `k^(|S| - 1)` elements, so `f^(-1)(b_a) = C(s_a, a)`.
   - For `a ≠ a'` the preimages of `b_a` and `b_(a')` are either equal or disjoint. But `C(s_a, a) ≠ C(s_(a'), a')`,
     so they are disjoint.
   - Two cylinders on different coordinates always meet, so `s_a = s_(a')`. Hence all `s_a` equal one `s`.
   - The `k` cylinders `C(s, a)` then cover `A^S`, and `f(y) = b_(y_s)`: `f` depends on one coordinate.
6. **Linear rules.** Let `f` be linear on `(F_p^d)^S`, and readable at `a` through `s` and `b`.
   - `f^(-1)(b)` is a coset of `ker f` inside the cylinder `C(s, a)`, so `ker f ⊆ ker(proj_s)`.
   - Hence `proj_s = L o f` for a linear `L`. So `f` has rank at least `d`, which is its maximum.
   - So `dim ker f = d(|S| - 1) = dim ker(proj_s)`, and `ker f = ker proj_s`.
   - Then `f` factors through `proj_s` and depends on one coordinate, contradicting `|S| >= 2`.
7. **Arithmetic of the moves.**
   - If `n` is not a power of two, neither is `nm` (`m >= 1`), nor `n^m`.
   - For `n >= 2`, `2^n - 1` is odd and at least `3`, so it is not a power of two.
   - The size `2^n` arises only from `Phi`, which is never injective by 3, and so never carries a strict automaton
     by this construction.

   Every other size change used in the graph is a multiple, a subgroup or overgroup change, or a regrouping
   (`ec-groups-share-the-nonsurjunctive-alphabet-sizes`, the attempts on
   `some-nonsurjunctive-group-gives-a-binary-power-one`). So induction on the length of a sequence of moves
   proves the move statement.

**Computation (supporting, not used in the proof).** `experiments/hyperspace-lift-2026-09-17/check.py` decides
injectivity over `Z` with the pair graph: off-diagonal pair states on bi-infinite paths. It reproduces claims
3–6 on every injective ternary window-2 rule and every binary window-3 rule, and it verifies the `F_2^2`
collision.
