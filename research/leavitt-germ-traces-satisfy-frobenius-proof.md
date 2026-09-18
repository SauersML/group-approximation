---
rg: 2
id: leavitt-germ-traces-satisfy-frobenius-proof
kind: route
title: Pair the terms of the convolution square by swapping factors; over F_2 only the isotropy square roots survive
target: leavitt-germ-traces-satisfy-frobenius
requires: []
---

Notation as in `leavitt-germ-traces-satisfy-frobenius`. `G` is ample and Hausdorff, and `f*h(g) = Σ_(ab=g) f(a)h(b)`.

1. **Finiteness and classes.** A compact open bisection `Z(α,β)` with `|α| − |β| = k ≠ 0` contains at most one
   isotropy point, computed in the Setting: `αz = βz` forces comparability, and `α = βγ` gives `γz = z`, so
   `z = γ^∞`. An element of `R` is a finite sum of such indicators, so it meets each class in finitely many points.
   `(βγ^∞, |γ|, βγ^∞)` is conjugate to `(γ^∞, |γ|, γ^∞)` by `(βγ^∞, |β|, γ^∞)`, and `(γ^∞, |γ|, γ^∞)` is
   conjugate to the same element for any rotation of `γ`. Conversely the class fixes the orbit of the periodic
   point and the degree `k`, hence the necklace `[γ]` of length `|k|`.
2. **Trace.** `Φ_C(f*h) = Σ_((a,b) in S) f(a)h(b)` with `S = {(a,b) : ab defined, ab in C}`. If `ab in C`, then
   `r(a) = s(b)`, so `ba` is defined, and `ba = b(ab)b^(-1) in C`. So `(a,b) -> (b,a)` is a bijection of `S` onto
   the index set of `Φ_C(h*f)`, and the two sums agree.
3. **HH_0.** `[s_α t_β] = [t_β s_α]`, and `t_β s_α` is `s_γ`, `t_γ` or `0`. So `HH_0` is spanned by `[1]`,
   `[s_γ]` and `[t_γ]`. Also `[1] = [s_0 t_0] + [s_1 t_1] = [t_0 s_0] + [t_1 s_1] = 2[1] = 0`. Now `Φ_C(s_γ) = 1`
   exactly for `C = (+,[γ])` and `Φ_C(t_γ) = 1` exactly for `C = (−,[γ])`. So the `Φ_C` are dual to a spanning
   set, and `⋂ ker Φ_C = [R,R]`. This is part 1.
4. **Squares.** `Φ_(C')(f*f) = Σ_((a,b) in S') f(a)f(b)` with `S'` as in step 2 for `C'`. The involution
   `(a,b) -> (b,a)` preserves `S'`. A free orbit contributes `f(a)f(b) + f(b)f(a) = 0` in `F_2`. A fixed point
   is `(a,a)`: then `a` is composable with itself, so `a` is isotropy, and it contributes `f(a)^2 = f(a)`. Hence
   `Φ_(C')(f^2) = Σ_(a in Iso, a^2 in C') f(a)`.
5. **Square roots of a class.** Isotropy groups of `G` are `Z` or trivial. If `a^2, b^2 in C'`, then
   `a^2 = h b^2 h^(-1)`, so `(h^(-1) a h)^2 = b^2` in one isotropy group `≅ Z`, and `h^(-1) a h = b`. So
   `{a : a^2 in C'}` is empty or one class `C`, and then `C' = C^2`. In necklaces, `(±,[γ])^2 = (±,[γγ])`, and
   `C'` is a square class iff its necklace is `ν ν` for some `ν`. This is part 2.
6. **Part 3.** Iterating part 2 gives `Tr(y^(2^k)) = F^k(Tr y)`, and every class in the image of `F^k` has a
   `2^k`-th power necklace. `Tr(x)` involves finitely many classes of bounded length, so if this holds for
   infinitely many `k`, then `Tr(x) = 0`.
7. **Part 4.** The span `B` of `Γ` is the image of `F_2[Γ]`. The Frobenius `Σ a_g g -> Σ a_g g^2` of `F_2[Γ]` is
   surjective, because `g -> g^2` is onto `Γ` and the ring is commutative of characteristic two. So every element
   of `B` is a `2^k`-th power in `B` for every `k`, and part 3 gives `B ⊆ [R,R]`.
8. **Part 5.** `s_00 t_0` has `α = β·0`, so it contributes to `(+,[0])`. `s_1 t_11` contributes to `(−,[1])`, and
   `s_01 t_10` meets no isotropy. So `Φ_((+,[0]))(c) = 1`. The necklace `[0]` has length 1 and is not a square,
   so by part 2 `c ≠ y^2`. Traces are conjugation invariant. ∎
