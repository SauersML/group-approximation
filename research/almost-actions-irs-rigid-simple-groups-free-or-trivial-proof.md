---
rg: 2
id: almost-actions-irs-rigid-simple-groups-free-or-trivial-proof
kind: route
title: Pass to the invariant random subgroup limit of the stabilizers and apply rigidity on a clopen event
target: almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial
requires: []
---

Notation as in the claim. `Sub(F(A))` is the compact metrizable space of subgroups of
`F(A)` with the product topology on `{0,1}^(F(A))`. For `w in F(A)` the set
`C_w = {H : w in H}` is clopen.

**Step 1: exact invariant random subgroups of the free group.** Each `sigma_n` is a genuine
action of `F(A)` on `[d_n]`. For uniform `x in [d_n]` let `H_n(x)` be the stabilizer of `x`,
with law `mu_n`. Since `x -> sigma_n(s) x` preserves the uniform measure and
`H_n(sigma_n(s) x) = s H_n(x) s^(-1)`, `mu_n` is conjugation invariant. It is an invariant
random subgroup of `F(A)`, and

```text
mu_n(C_w) = |{x : sigma_n(w) x = x}| / d_n = 1 - d_H(sigma_n(w), 1).     (P1)
```

**Step 2: the limit lives on S.** Suppose `(AF2)` fails. Then there are `g notin N`,
`delta > 0` and a subsequence with `|{x : sigma_n(g)x = x} \ Fix_n| >= delta d_n`. By
compactness pass to a further subsequence with `mu_n -> mu` weak-*. Conjugation invariance
passes to the limit, so `mu` is an invariant random subgroup of `F(A)`. For `w in N`,
`(P1)` and `(AF1)` give `mu_n(C_w) -> 1`, and `C_w` is clopen, so `mu(C_w) = 1`. As `N` is
countable, `mu`-almost every `H` contains `N`. The map `H -> H/N` is a conjugation
equivariant homeomorphism from `{H : H >= N}` onto `Sub(S)`. So the push-forward of `mu`
is an invariant random subgroup of `S`.

**Step 3: rigidity.** By hypothesis that push-forward is `p delta_S + (1-p) delta_e` for
some `p in [0,1]`. Hence `mu = p delta_(F(A)) + (1-p) delta_N`.

**Step 4: the clopen event.** Let

```text
E = C_g ∩ ( union over a in A of the complement of C_a ).                (P2)
```

`E` is clopen because `A` is finite. A point `x` has `H_n(x) in E` exactly when
`sigma_n(g) x = x` and `x notin Fix_n`, so `mu_n(E) >= delta` along the subsequence.
On the other hand `F(A) notin E`, since it contains every `a`, and `N notin E`, since
`g notin N`. So `mu(E) = 0`. Weak-* convergence on a clopen set gives
`mu_n(E) -> mu(E) = 0`, a contradiction. This proves `(AF2)`.

**Consequence 1.** Each `sigma_n(a)` fixes `Fix_n` pointwise, so it maps the complement
`Y_n` of `Fix_n` onto itself. If `|Y_n| >= c d_n`, then for `w in N` the proportion of
`Y_n` moved by `sigma_n(w)` is at most `d_H(sigma_n(w),1)/c -> 0`. For `g notin N`, `(AF2)`
gives `|{x in Y_n : sigma_n(g)x = x}| / |Y_n| <= c^(-1) o(1) -> 0`. A map on words that is
asymptotically multiplicative on relators and asymptotically fixed-point free on every
nontrivial element is a sofic approximation; it is well defined on `S` up to `o(1)` because
two words with the same image differ by an element of `N`.

**Consequence 2.** If `S` is sofic, a sofic approximation composed with any lift
`F(A) -> S` satisfies `(AF1)` and has `|Fix_n|/d_n -> 0`. Conversely Consequence 1 applies.

**Consequence 3.** Let `L <= S` be finite, with lifts `w_l` of its elements. For
`l != 1`, `(AF2)` bounds the points of `Y_n` fixed by `sigma_n(w_l)` by `o(d_n)`, and
there are finitely many `l`. So all but `o(d_n)` points of `Y_n` have trivial stabilizer
in the approximate `L`-action. If each `sigma_n` restricted to the words `w_l` is replaced
by a nearby exact `L`-action (finite groups are permutation stable), the same holds for
the exact action.
