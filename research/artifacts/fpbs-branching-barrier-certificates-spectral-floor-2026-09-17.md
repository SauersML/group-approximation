# Branching barrier certificates have a spectral floor

Worker `swarm-0917-w12-w12-fp-break`. This note belongs to claim
`fpbs-branching-barrier-certificates-spectral-floor` and its route. It is
reproduced by `experiments/branching-barrier-2026-09-17/check.py`, with output
in `check.out`.

## 0. Why this class matters

Write `M = F(a,b) *_phi` with `phi(a) = a` and `phi(b) = b a b^{-2}`. So
`M = < a, b, t | t a t^{-1} = a, t b t^{-1} = b a b^{-2} >`. This is the
ascending HNN overgroup of `Gamma_mal = N = ker(M -> Z)`, the flagship test
group of the fixed-price lane (§4 recalls the facts used). Three facts hold:

- `C(M) = 1`.
- `M` has fixed price if and only if `C(s_M) = 1`.
- The Bernoulli shift of `M` restricts on `N` to the Bernoulli shift of `N`.

So universal fixed price predicts `C(s_M) = 1`.

The obvious way to prove `C(s_M) = 1` is to keep `t` and `a` at total cost
`1 + epsilon`, which is possible because `<a,t> = Z^2` is amenable. Then put
`b` on a sparse set `D` and recover every other `b`-edge from the relation
`b = t^{-1} (b a b^{-2}) t`. This relation writes one `b`-edge at `y` using
three `b`-edges at the points `c_1 y`, `c_2 y`, `c_3 y`, where

```text
c_1 = b^{-1} t,   c_2 = b^{-2} t,   c_3 = a b^{-2} t.
```

This is the same self-similar recursion that proves fixed price for
`BS(1,n)`-type chains. Here it dies: §1 is the general theorem and §2
specialises it to `M`.

## 1. The general floor theorem

**Setting.**
- `Gamma` is a countable group acting by `a : Gamma -> Aut(X, mu)`,
  p.m.p. on a standard probability space.
- `C = {c_1, ..., c_k}` is a finite subset of `Gamma`.
- For `y in X`, a *forward path* from `y` is a sequence
  `y_0 = y, y_{n+1} = c_{i_n} y_n` with `i_n` in `{1..k}`.
- A measurable `D ⊆ X` is a *barrier* for `C` if, for a.e. `y`, every
  infinite forward path from `y` meets `D`.

**Gap hypothesis (GH).** `P` is a nonempty set of unordered pairs
`{i, j}` with `i ≠ j`. Put `s_{ij} = c_i c_j^{-1}`. Assume there is
`kappa > 0` such that

```text
sum over {i,j} in P of || f - s_{ij} f ||_2^2  >=  kappa || f ||_2^2
for every real f in L^2_0(X, mu).                                    (GH)
```

Here `(g f)(x) = f(g^{-1} x)` is the Koopman representation. The inequality
does not depend on the orientation chosen for each pair, because
`|| f - s^{-1} f || = || s f - f ||`.

**Theorem A.** Assume (GH). Put `eta = kappa / (2|P|)`, and let
`delta_*(eta)` be the positive root of `eta d^2 + 4 d - eta = 0`, so that

```text
delta_*(eta) = ( sqrt(4 + eta^2) - 2 ) / eta,  and  eta/4 - eta^3/64 < delta_* < eta/4.
```

1. If `delta = mu(D) < delta_*`, then the points with an infinite forward
   path avoiding `D` have measure at least
   `r_+ = (1 + sqrt(1 - 4 delta / eta)) / 2 > 1/2`.
2. In particular every barrier has `mu(D) >= delta_*(eta)`.

No tree structure is used. The forward paths may merge, and they do merge in
the application to `M` (§2).

### Proof of Theorem A

**Step 1 (level sets).** Put `A_0 = X \ D` and, for `j >= 0`,

```text
A_{j+1} = (X \ D) ∩ ( c_1^{-1} A_j ∪ ... ∪ c_k^{-1} A_j ).
```

By induction, `y ∈ A_j` exactly when there is a forward path
`y_0, ..., y_j` from `y` lying entirely in `X \ D`. The sets are measurable
and decreasing. Their intersection `A_∞` is the set of points with an
infinite forward path avoiding `D`. For `⊆`: the paths from `y` form a
finitely branching tree of words over `k` letters, so König's lemma gives an
infinite branch when every length occurs. `⊇` is clear. So `D` is a barrier
iff `mu(A_∞) = 0`, iff `alpha_j = mu(A_j) -> 0`. Also `alpha_0 = 1 - delta`.

**Step 2 (one-step expansion).** Take measurable `A` and `{i,j} ∈ P`. The
sets `c_i^{-1} A` and `c_j^{-1} A` both have measure `mu(A)`, so

```text
mu(c_i^{-1}A ∪ c_j^{-1}A) = mu(A) + (1/2) mu(c_i^{-1}A △ c_j^{-1}A)
                          = mu(A) + (1/2) mu(A △ s_{ij} A),
```

where the second line applies `c_i`. Put `f = 1_A - mu(A)`. Then
`s f - f = 1_{sA} - 1_A`, so `|| f - s f ||^2 = mu(A △ s A)` and
`|| f ||^2 = mu(A)(1 - mu(A))`. The maximum over `P` is at least the
average, so (GH) gives

```text
mu( ∪_i c_i^{-1} A ) >= mu(A) + (1/(2|P|)) sum_P mu(A △ s_{ij} A)
                     >= mu(A) + eta mu(A)(1 - mu(A)).                (E)
```

**Step 3 (recursion).** By definition `∪_i c_i^{-1} A_j ⊆ A_{j+1} ∪ D`, so
(E) with `A = A_j` gives

```text
alpha_j + eta alpha_j (1 - alpha_j) <= alpha_{j+1} + delta.          (R)
```

Since `alpha_{j+1} <= alpha_j`, for every `j >= 0`:
- (R1) `eta alpha_j (1 - alpha_j) <= delta`;
- (R2) `alpha_j - alpha_{j+1} <= delta`.

**Step 4 (the step where a small barrier dies).** Let `delta < delta_*`.
- `delta_* < eta/4`, so `eta r(1-r) = delta` has real roots
  `r_- < 1/2 < r_+`.
- By (R1), every `alpha_j` lies in `[0, r_-] ∪ [r_+, 1]`.
- The forbidden window has width `r_+ - r_- = sqrt(1 - 4 delta/eta)`. This
  width exceeds `delta` exactly when `eta delta^2 + 4 delta - eta < 0`, which
  is `delta < delta_*`.
- By (R2) the sequence moves down in steps of at most `delta`, so it cannot
  jump over the window.
- The sequence starts above the window: `alpha_0 = 1 - delta > 1/2` and (R1)
  holds at `j = 0`, so `alpha_0 >= r_+`.

Hence `alpha_j >= r_+` for all `j`, and `mu(A_∞) = lim alpha_j >= r_+ > 1/2`.
This is item 1. Item 2 follows because a barrier has `mu(A_∞) = 0`. ∎

**The invariant, and where every member dies.** The invariant is the
Dirichlet form of the *child-difference group*
`L = < c_i c_j^{-1} : {i,j} ∈ P >`. It is evaluated on the level sets `A_j`
of the "longest `D`-free descent" function. A barrier must push the measure
of these level sets from `1 - delta` down to `0`, and so must pass the level
`1/2`. There, (E) creates new mass of about `eta/4` per step, while the
barrier can absorb only `delta` per step.

### When (GH) holds

**Lemma G.** Suppose the subgroup `L` generated by
`S_P = {s_{ij} : {i,j} ∈ P}` is nonamenable, and the Koopman representation
of `L` on `L^2_0(X)` is weakly contained in `lambda_L`. Then (GH) holds with

```text
kappa = |S| (1 - rho),   S = S_P ∪ S_P^{-1},   rho = rho(L, S) < 1.
```

This applies to every Bernoulli shift `s_Gamma`, and to every action weakly
contained in it, whenever `L` is nonamenable.

*Proof.* Let `T = (1/|S|) sum_{s ∈ S} s`, a self-adjoint operator on
`L^2_0`. For real `f`,

```text
sum_{s ∈ S} || f - s f ||^2 = 2|S| ||f||^2 - 2|S| <T f, f>
                            >= 2|S| (1 - ||T||) ||f||^2.
```

Each `s ∈ S` is `s_{ij}` or `s_{ij}^{-1}` for some pair in `P`, and
`|| f - s^{-1} f || = || f - s f ||`. So the left side is at most
`2 sum_P || f - s_{ij} f ||^2`. Two imports bound `||T||`.

- *Kesten.* `kesten-amenable-stabilizer-uniform-gap` quotes: "rho = rho(A,S)
  = || (1/|S|) sum over s in S of lambda_A(s) || < 1 ... which is < 1
  exactly when A is nonamenable."
- *Bernoulli Koopman.* `burton-kechris-tempered-actions-koopman-bernoulli`
  quotes Burton–Kechris: "In fact, κsΓ0 ∼= ∞ · λΓ". It also quotes that "the
  set of tempered actions if closed downwards under ≼".

Weak containment in `lambda_L` does not increase the norm of an element of
the group algebra, so `||T|| <= rho`. Restricted to `L`, `∞·lambda_Gamma` is
`∞·lambda_L`. Downward closure covers every action weakly contained in
`s_Gamma`. ∎

This clause is the one that matters. By Abért–Weiss and
`fpbs-finite-cost-transfers-up-weak-containment` (ESTABLISHED),
`C(s_Gamma)` is the largest cost among free actions. So the Bernoulli shift
is the one action a fixed-price proof has to handle.

## 2. The HNN overgroup M

**Lemma 2.1 (relation certificate).** Let `alpha` be a free p.m.p. action of
`M`, let `Phi` be a graphing generating `R_{<a,t>}`, and let `D` be
measurable. Put

```text
R' = < Phi, b|_D >,     G = { y : (y, b y) ∈ R' }.
```

Then `D ⊆ G`, and `c_1 y, c_2 y, c_3 y ∈ G` implies `y ∈ G`. If `D` is a
barrier for `{c_1, c_2, c_3}`, then `R' = R_M` up to a null set, and
`C(alpha) <= C(Phi) + mu(D)`.

*Proof.* The relation gives `b = t^{-1} b a b^{-2} t`. Follow the chain

```text
y  ->  z0 = t y  ->  z1 = b^{-1} z0 = c_1 y  ->  z2 = b^{-1} z1 = c_2 y
   ->  z3 = a z2 = c_3 y  ->  z4 = b z3  ->  t^{-1} z4 = b y.
```

- The `t`- and `a`-moves lie in `R_{<a,t>} ⊆ R'`.
- The move `z1 -> z0` is the pair `(c_1 y, b c_1 y)`, and `z2 -> z1` is
  `(c_2 y, b c_2 y)`.
- The move `z3 -> z4` is `(c_3 y, b c_3 y)`.

So `c_1 y, c_2 y, c_3 y ∈ G` implies `y ∈ G`, and `D ⊆ G` is immediate. Hence every
`y ∉ G` lies outside `D` and has a child outside `G`. Iterating, `y` has an
infinite forward path in `X \ D`, so for a barrier `mu(X \ G) = 0`. Then `R'`
contains `R_{<a,t>}` and the graph of `b` on an invariant conull set, and
`M = <a, b, t>`. ∎

Because `<a,t> = Z^2` is infinite amenable, `Phi` can be chosen with
`C(Phi) <= 1 + epsilon`. So every barrier `D` certifies
`C(alpha) <= 1 + mu(D)`. This is the class of **single-rule barrier
certificates** for `M`.

**Children and differences** (checked in `check.out`):

```text
c_1 c_2^{-1} = b,    c_2 c_3^{-1} = a^{-1},    c_1 c_3^{-1} = b a^{-1}.
```

**Corollary B.** Take `P = {{1,2},{2,3}}`, so `S_P^± = {a^±, b^±}` and
`L = <a,b> = F_2` with free basis `a, b`. Then:

- Kesten's value is `rho(F_2, {a^±, b^±}) = sqrt(3)/2`;
- Lemma G gives `kappa = 4 - 2 sqrt 3 ≈ 0.5359`;
- `eta = kappa/4 ≈ 0.1340`;
- `delta_* ≈ 0.03346`.

Consequences:

- For the Bernoulli shift `s_M`, and for every free `M`-action weakly
  contained in it, every barrier for `{c_1, c_2, c_3}` has
  `mu(D) >= 0.0334`.
- If `mu(D) < 0.0334`, more than half of the space has an infinite forward
  path avoiding `D`.
- So no single-rule barrier certificate proves `C(s_M) = 1`. The best such
  certificate gives `C(s_M) <= 1 + delta` with `delta` bounded away from 0.

The value `sqrt(3)/2` is classical (Kesten 1959) but is not quoted
verbatim in the graph. The statement proper needs only `rho < 1`, which is
quoted, and then gives an explicit floor `delta_*(eta) > 0` with
`eta = 1 - rho`.

**Upper side of the window.** Let `D_p = {x : x(e) < p}` in `s_M` with
uniform base. Along any forward path the group elements
`e, c_{i_1}, c_{i_2} c_{i_1}, ...` have `t`-exponent sums `0, 1, 2, ...`, so
they are distinct. Their coordinates are therefore independent. The expected
number of `D_p`-free forward paths of length `n` is `3^n (1-p)^{n+1}`, which
tends to 0 for `p > 2/3`. So `D_p` is a barrier for every `p > 2/3`.

The optimal single-rule barrier measure for `s_M` therefore lies in
`[0.0334, 2/3]`. For comparison, `C(s_M) <= 2` holds trivially because
`M = <b, t>`.

**Not a tree.** `b^{-1}` and `a b^{-2}` lie in the same left
`phi(H)`-coset, because `b^2 a^{-1} b^{-1} = (b a b^{-2})^{-1}`. So
`c_3 = c_1 b` in `M`, and `c_3 c_2 = c_1 c_1`. The forward graph merges.
Theorem A needs no tree structure, so this changes nothing. It does correct
an earlier heuristic in this lane that the `c`-graph is a genuine ternary
tree.

## 3. Scope: what escapes, and the precise dying step

**Amenable child differences escape.** If every pair's difference generates
an amenable group, (GH) fails in Bernoulli shifts, and small barriers are not
excluded. This is exactly the chain situation.

- `BS(1,n)`: `b = t^{-1} b^n t`. All differences are powers of `b`.
- The T5 group of `research/artifacts/fpbs/docs/fixed-price-countable-passage.md`,
  with `phi(b) = b^2`: the `b`-recursion also has differences in `<b>`.

For these the recursion is the one that succeeds. Theorem A therefore draws
the line: single-rule recursion certificates for a generator `g` over a
cost-one subgroup can only reach cost `C(Gamma_0) + 0` when the
child-difference group is amenable, or the action has no spectral gap there.
For ascending HNN extensions `F_n *_phi`, the children of `b` are indexed by
the `b`-letters of `phi(b)`. Their differences are the subwords between
consecutive `b`-letters, conjugated. So the obstruction applies as soon as
`phi(b)` has two `b`-letters whose pairwise differences generate a
nonamenable subgroup. Here those differences are `b`, `a` and `b a^{-1}`.

**Several rules (AND–OR certificates) escape the argument.** Suppose the
`b`-edge at `y` may be derived by any one of several relation readings
`r = 1..m`, each with its own children `c_{r,i}`. Then the level recursion
becomes

```text
A_{j+1} = (X \ D) ∩ ⋂_r ∪_i c_{r,i}^{-1} A_j .
```

(E) bounds each union from below, but an intersection of `m >= 2` large sets
has only the union bound. That bound gives
`1 - alpha_{j+1} <= delta + m (1 - alpha_j)(1 - eta alpha_j)`, which is
useless unless `m (1 - eta) < 1`, i.e. `m = 1`. **This is the exact step
where the kill stops.** The general statement "`Phi ∪ b|_D` generates `R_M`"
is the AND–OR closure over the countably many relation readings. So Theorem A
kills every single-rule certificate and leaves the multi-rule ones open. A
proof of `C(s_M) = 1` must use at least two genuinely different derivations
of `b`-edges on a positive-measure set, for example the relation read at `y`
and at `b y`, or relations of `M` other than the defining one.

## 4. Context facts about M (recorded for the lane)

1. **`C(M) = 1`.** By `fpbs-finite-cost-normal-subgroup-infimal-cost-one-citation`,
   Donoso-Echenique–Silva Theorem 2.2 reads: "Let G be a countable group and
   let N◁G be an infinite normal subgroup such that N has infinite index in G
   and cost(N)<∞. Then cost(G) = 1."
   - `N = Gamma_mal` is normal in `M` with `M/N = Z`.
   - `cost(N) <= 2` by `fpbs-mal-odometer-product-actions-have-cost-two`.
2. **`M` has fixed price iff `C(s_M) = 1`.** Every free `alpha` satisfies
   `1 = C(M) <= C(alpha) <= C(s_M)`. The upper bound uses Abért–Weiss and
   `fpbs-finite-cost-transfers-up-weak-containment`.
3. **`s_M|_N ≅ s_N`.**
   - `M` is the disjoint union of the countably many cosets `N m`. So
     `[0,1]^M = prod_m [0,1]^{N m}`, and `N` acts diagonally by left shifts.
   - This is the Bernoulli shift of `N` with base `[0,1]^{N\M} ≅ [0,1]`.

   So in `fpbs-extension-routes-to-finite-cost-are-circular` item 4, the
   second descent ("from a product of twists of b to b, which is (U)
   itself") is vacuous for the Bernoulli shift. By
   `fpbs-mal-fixed-price-iff-bernoulli-finite-cost`, the Bernoulli shift is
   the only action that matters. The coinduction route for `Gamma_mal` is
   therefore exactly one statement: finite `M`-cost of `s_M`, which always
   holds (`<= 2`), descends to finite `N`-cost of `s_M|_N = s_N`. That is,
   `relC(R_N ⊂ R_M)`-type descent along the `Z`-quotient. It fails for
   general extensions (`F_∞ x Z`), so it needs `M`-specific input. This
   sharpens the recorded item. It does not refute it: the route is still
   not a proof.

## 5. Reproduction

`python3 experiments/branching-barrier-2026-09-17/check.py` performs these
checks:

- Stallings folding of `phi(H)`, which has 3 vertices;
- the coset tests, including `c_3 = c_1 b`;
- the child differences;
- the constants `kappa`, `eta`, `delta_*`;
- a brute-force bisection of recursion (R), with greedy descent, giving
  least `delta ≈ 0.03349 >= delta_* ≈ 0.03346`.
