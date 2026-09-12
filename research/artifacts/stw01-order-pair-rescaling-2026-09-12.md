# STW Problem I: the order relation is a rescaling artifact (2026-09-12)

Lane `quasitrace-universal-order-pair`. Proof artifact for the claim
`stw01-order-pair-defects-rescale-generic-defects` and the route
`stw01-problem-i-via-universal-order-pair`. It also records the attempts on
`stw01-universal-order-pair-quasitrace-additivity`.

**Outcome.** Additivity on the universal order pair is **not decided**. Section 1 proves
that the relation `0 <= k_0 <= h_0 - h_0^2` restricts nothing: every non-additive positive
pair in every unital C*-algebra appears, after an affine rescaling, as an order pair
carrying a fixed multiple of its defect. So the universal order-pair test is exactly
generic additivity, and structure of `U` specific to the order relation cannot be the
lever. Sections 3-5 record the attacks on `U` and where each dies.

Notation. `U` is the universal unital C*-algebra of `h_0, k_0` with

```text
0 <= h_0 <= 1,        0 <= k_0 <= h_0 - h_0^2.                               (OP)
```

For a bounded 2-quasitrace `sigma` and `a, b >= 0`, `D(a, b) = sigma(a + b) - sigma(a) - sigma(b)`.
The axioms used are those listed in
`research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md` §0: positive
on `A_+`, `sigma(z^* z) = sigma(z z^*)`, linear on commutative C*-subalgebras,
`sigma(a + ib) = sigma(a) + i sigma(b)`, and extension to `M_2(A)`. Monotonicity on `A_+` is used
only in Section 5, as the standard axiom recorded in
`research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md`.

## 1. Lemma R: affine rescaling into order pairs

**Lemma R.** Let `A` be unital, `sigma` a bounded 2-quasitrace on `A`, and `x, y in A_+` with
`||x||, ||y|| <= 1`. Let `0 < eps <= 1/5` and `0 <= s <= 1/4 - eps - eps^2`. Put

```text
h = (1/2) 1 + eps x,        k = s 1 + eps y.
```

Then (i) `sp(h) ⊂ [1/2, 1/2 + eps]` and `0 <= k <= h - h^2`; (ii) `D(h, k) = eps D(x, y)`;
(iii) for `s = 1/4 - eps - eps^2`, also `(1 - 4 eps - 4 eps^2)(h - h^2) <= k`.

**Proof.**
- (i) `sp(x) ⊂ [0, 1]` gives `sp(h) ⊂ [1/2, 1/2 + eps] ⊂ [0, 1]`. Expanding,

  ```text
  h - h^2 = 1/2 + eps x - (1/4 + eps x + eps^2 x^2) = (1/4) 1 - eps^2 x^2,
  ```

  so `(1/4 - eps^2) 1 <= h - h^2 <= (1/4) 1`. Next, `s >= 0` is admissible because
  `eps + eps^2 <= 1/5 + 1/25 < 1/4`, and `k >= s 1 >= 0`. Also
  `k <= (s + eps) 1 <= (1/4 - eps^2) 1 <= h - h^2`.
- (iii) `h - h^2 <= (1/4) 1` gives `4s (h - h^2) <= s 1 <= k`.
- (ii) `sigma` is linear on the commutative C*-subalgebras `C*(1, x + y)`, `C*(1, x)` and
  `C*(1, y)`. So `sigma(h + k) = (1/2 + s) sigma(1) + eps sigma(x + y)`,
  `sigma(h) = (1/2) sigma(1) + eps sigma(x)` and `sigma(k) = s sigma(1) + eps sigma(y)`. Subtract. ∎

By (i) and the universal property there is a unital *-homomorphism `psi : U -> A` with
`psi(h_0) = h`, `psi(k_0) = k`, and `sigma o psi` has defect `eps D(x, y)` on `(h_0, k_0)`.

## 2. Corollary: a direct route from the order pair to Problem I

**Corollary.** If every bounded 2-quasitrace on `U` satisfies
`sigma(h_0 + k_0) = sigma(h_0) + sigma(k_0)`, then every bounded 2-quasitrace on every unital
C*-algebra is a trace.

**Proof.**
1. A bounded 2-quasitrace additive on `A_+` is a trace. For `a, b in A_sa`,
   `a_+ + b_+ + (a + b)_- = (a + b)_+ + a_- + b_-`. Apply `sigma`, use additivity on `A_+` on both
   sides, and use `sigma(c) = sigma(c_+) - sigma(c_-)` inside `C*(c)`. This gives additivity on `A_sa`.
   Real homogeneity holds inside each `C*(a)`, and `sigma(a + ib) = sigma(a) + i sigma(b)`. So `sigma`
   is linear, and it is tracial by `sigma(z^* z) = sigma(z z^*)`.
2. So a non-trace `sigma` has `x, y in A_+` with `D(x, y) != 0`. Put `t = 1/max(||x||, ||y||)`.
   Then `D(tx, ty) = t D(x, y)` by homogeneity inside commutative subalgebras.
3. Lemma R with `eps = 1/5`, `s = 0` gives `psi : U -> A`, and `sigma o psi` is a bounded
   2-quasitrace on `U` with defect `(1/5) t D(x, y) != 0`. ∎

**Comparison.** Theorem B of `research/artifacts/stw01-universal-order-pair-test-2026-09-12.md`
reached the same equivalence through the single-pair theorem: Steps 0-3 in a type `II_1`
AW*-factor, the affine rescaling with an intermediate-value choice of `eps` making the
second element a multiple `m q` of a projection, and the three-block dilation into
`C*(PSL_2(Z))`. For the order-pair claim none of that is needed. The tuning was needed
there because the target pair in `Q` is fixed; here the target is the universal pair, and
any small `eps` works.

## 3. What Lemma R rules out

Non-additive witnesses on `U` exist with every one of the following at once:
- `sp(h_0)` inside the window `[1/2, 1/2 + eps]`, for any `eps in (0, 1/5]`;
- `h_0 - h_0^2` within `eps^2` of the scalar `1/4`, so invertible and nearly central;
- `k_0` squeezed: `(1 - 4 eps - 4 eps^2)(h_0 - h_0^2) <= k_0 <= h_0 - h_0^2`;
- `k_0 - s 1` of norm at most `eps`, so `k_0` is within `eps` of a scalar.

So:
- **Spectral decomposition along `h_0`.** Dead. `h_0` is not central in `U`, and even a
  heuristic splitting along its spectrum meets witnesses concentrated in one window of
  width `eps`. The endpoints `0` and `1`, where `h_0 - h_0^2` degenerates, carry nothing.
- **The room `h_0 - h_0^2 - k_0`.** Dead as a lever. For the extreme `s` its norm is at most
  `eps + eps^2`, the same first order as the defect `eps D(x, y)`. So making the room small
  forces the defect small only in proportion, and rescaling produces no contradiction. The
  commuting sandwich (Lemma C of the order-pair artifact) stays consistent with every
  witness.
- **Perturbation of scalars.** Both elements are within `eps` of scalars, and the defect is
  exactly first order in `eps`. There is no second-order structure to exploit:
  `sigma(c 1 + eps z) = c sigma(1) + eps sigma(z)` for `z >= 0` is exact, not an expansion.

The universal order pair is therefore the generic positive pair after an affine change of
coordinates. A proof of `stw01-universal-order-pair-quasitrace-additivity` is a proof of
additivity for arbitrary positive pairs, i.e. of Problem I, with nothing extra available.

## 4. Two structural facts about `U`, and why they do not help

**4.1. A free-product model.** Let `V = C([0,1]) * C([0,1])` be the unital full free product,
generated by positive contractions `h, c`, and put `S = (h - h^2)^(1/2)`. Then
`0 <= S c S <= S^2 = h - h^2`, so there is a unital *-homomorphism `U -> V` with `h_0 -> h`,
`k_0 -> S c S`. It is isometric. Given a Hilbert-space order pair `(a, b)`, Douglas' lemma
gives a contraction `C` with `b^(1/2) = C (a - a^2)^(1/2)`, so `b = S_a C^* C S_a` with
`S_a = (a - a^2)^(1/2)`. The representation of `V` with `h -> a`, `c -> C^* C` sends `S c S` to `b`.
So `||P(a, b)|| <= ||P(h, S c S)||_V <= ||P(h_0, k_0)||_U`, and taking the supremum over `(a, b)`
gives equality. Hence `U ~= C*(1, h, S c S) ⊂ V`.

This does not help: a quasitrace on `U` need not extend to `V`, and linearity on `V` is
already equivalent to Problem I (`stw01-full-free-group-algebra-quasitraces-are-traces`,
item 2 of its equivalent forms).

**4.2. `U` is residually finite-dimensional, directly.** Let `(a, b)` be an order pair on `H`
and `P` a finite-rank projection. Then

```text
PaP - (PaP)^2 = P (a - a^2) P + P a (1 - P) a P >= P (a - a^2) P >= P b P,
```

so `(PaP, PbP)` is an order pair on `PH`. With `P ↑ 1` strongly, `P(PaP, PbP)` converges strongly
to `P(a, b)` for every *-polynomial, so `||P(a, b)|| <= sup ||P(PaP, PbP)||`. Finite-dimensional
representations therefore compute the universal norm. This gives an RFD proof independent
of Exel–Loring for `Q`.

This does not help, for the reason recorded on `stw01-modular-single-pair-quasitrace-additivity`:
pointwise limits of finite-dimensional traces are traces, and a quasitrace is not such a
limit unless it is already a trace.

## 5. Norm-local exact approximation inside `U` is impossible

**Lipschitz bound.** For a bounded 2-quasitrace and `a, b in A_+`, `a <= b + ||a - b|| 1`. So
monotonicity and additivity on the commuting pair `(b, ||a - b|| 1)` give
`|sigma(a) - sigma(b)| <= ||a - b|| sigma(1)`. Hence, if `(h_0, k_0)` could be approximated within
`delta` by positive elements generating an exact C*-subalgebra `E ⊂ U`, Haagerup's theorem
on `E` would give `|D(h_0, k_0)| <= 4 delta sigma(1)`.

**Obstruction.** No such approximation exists for arbitrarily small `delta`. Suppose
`h', k' in E` are within `delta` of `h_0, k_0`.
1. *Correct to an order pair inside `E`.* Put `h'' = g(Re h')` with `g` the clamp to
   `[0, 1]`, `k_1 = (Re k')_+` and `S'' = h'' - h''^2`. Continuity of the functional calculus on
   bounded sets gives `h'' -> h_0`, `S'' -> S_0 = h_0 - h_0^2` and `k_1 -> k_0` as `delta -> 0`. So
   `k_1 <= S'' + eta 1` once `delta` is small relative to `eta`. Put `T = (S'' + eta 1)^(-1/2)` and
   `k'' = S''^(1/2) T k_1 T S''^(1/2)`. Then `0 <= k'' <= S''`, and `k'' in E`.
2. *Closeness.* Write `k_0 = S_0^(1/2) c S_0^(1/2)` with `0 <= c <= 1` in `B(H)` (Douglas).
   With `f(t) = t (t + eta)^(-1/2)` and `sqrt t - f(t) <= sqrt(t + eta) - sqrt t <= sqrt eta`,
   the element `f(S_0) c f(S_0)` is within `sqrt eta` of `k_0`. And `k''` tends to it as `delta -> 0`
   with `eta` fixed. So `||k'' - k_0|| -> 0` as `eta -> 0` and then `delta -> 0`.
3. *Nuclearity.* The universal property gives `alpha : U -> E` with `alpha(h_0) = h''`,
   `alpha(k_0) = k''`. It is close to the identity on each *-polynomial of bounded degree, and
   hence, since `alpha` is contractive and polynomials are dense, on each finite subset of `U`.
   For a faithful representation `iota : U -> B(H)`, the map `iota o alpha = iota|_E o alpha` is
   nuclear, because `E` is exact. So `iota` is a point-norm limit of nuclear maps, hence
   nuclear, and `U` is exact.

`U` is not exact: it surjects onto `Q`
(`research/artifacts/stw01-universal-order-pair-test-2026-09-12.md` §1). So the approximation
fails, and this is a local form of the non-exactness already recorded for containing
subalgebras. `stw01-local-trace-rigid-models-force-linearity` still allows non-exact
quasitrace-rigid local models. None is known inside `U`.

## 6. The negative side

A non-additive lower semicontinuous dimension function on the Cuntz semigroup of `U`
(Blackadar–Handelman correspondence) would be a counterexample to Problem I. By
`stw01-quasitrace-crux-is-awstar-factor-w-star` it needs a type `II_1` AW*-factor with no
large W*-corner, and no construction of one is known. Not attempted here beyond recording
the equivalence. Lemma R shows the witness can be taken with `h_0` near `1/2`, and so gives
no additional handle on a construction either.

## 7. Status

Nodes this lane adds to the graph (see `git log` for when they land):
- claim `stw01-order-pair-defects-rescale-generic-defects`, proved by the route
  `stw01-order-pair-defects-rescale-generic-defects-proof`;
- route `stw01-problem-i-via-universal-order-pair` into the root, requiring the open claim.
  The root stays OPEN;
- `stw01-universal-order-pair-quasitrace-additivity` stays OPEN, with the attempts above added
  to its `## Attempts`.
