---
rg: 2
id: dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures-proof
kind: route
title: Derive the conditional edge law (L′ uniform off H′, new direction uniform off L′ + H_U), show the rank-split mixture is class invariant because the kernel kills H_U, count injective images to get b and c exactly, bound every wrong reference by the 2^(1-l) lift lemma, and sum over clean surjective tuples
target: dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures
requires: [dkkms-2to1-instances-satisfy-selector-decoding-hypotheses]
artifacts:
  - experiments/ugc-seed-mixture-2026-09-17/check_seed_mixture.py
---

The notation is that of the target claim and of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. That node quotes
verbatim the vertices, the edge process, the constraint, the folding classes
(Lemma 4.1 of DKKMS) and the unfolding (Definition 4.2) of Dinur, Khot,
Kindler, Minzer and Safra, ECCC TR16-198. Its item 3 is used: given
`((V,L′), U)`, the new direction is uniform on `X_U \ (L′ + H_U)`. So is its
item 4: the `U`-marginal of `G_multi` is uniform. The unfolding uniqueness
statement used below is also quoted there, and in
`dkkms-near-perfect-labellings-are-outer-honest-proof` (Q4):

> "if L∩H = φ then any linear function f : L → F2 has a unique (H,h)-extension,
> ˜f : L + H → F2, where ˜f(z) = f(x) + h(y) and where z = x + y is the unique
> way to write z as a sum of x∈L and y∈H."

Throughout, `U` is a tuple, `V` its smoothed tuple, and `H′ := H_U ∩ X_V`.
This is spanned by the `x_e` of the kept equations, because a dropped equation
contributes only one coordinate vector to `X_V`. Put `Q := X_V/H′` and
`d′ := dim Q = 2·#kept + #dropped >= k`. A tuple is **clean** for `x` if `x`
satisfies every equation of `U`.

## Step 1: the conditional edge law

**Lemma 1.** Under `G_multi`, conditioned on `V`:
* `L′` is uniform on the `(l-1)`-subspaces of `X_V` with `L′ ∩ H′ = 0`;
* given `(V, L′)`, `L = L′ + <w>` with `w` uniform on `X_U \ (L′ + H_U)`.

The `V`-marginal is the smoothing law reweighted by
`p(V) := Pr[L′ ∩ H′ = 0 | V] >= 1 - 2^(l-1-d′)`.

*Proof.* The process draws `L′` uniformly from `Gr(X_V, l-1)`, then `L`
uniformly among `l`-spaces of `X_U` containing `L′`, and keeps the output iff
`L ∩ H_U = 0`.

Since `L′ <= X_V`, we have `L′ ∩ H_U = L′ ∩ H′`. If this is nonzero, no `L` is
kept. Otherwise `L = L′ + <w>` is kept iff `w ∉ L′ + H_U`, a space of
dimension `l-1+k`. Each `L` arises from exactly `2^(l-1)` vectors `w ∈ L \ L′`.

So the keep probability is
`(2^(3k) - 2^(l-1+k)) / (2^(3k) - 2^(l-1))`. This does not depend on `L′` or
`V`, which gives both displayed statements. The second is also item 3 of the
decoding-hypotheses node.

For the marginal, a fixed nonzero vector of `H′` lies in a uniform
`(l-1)`-space with probability `(2^(l-1)-1)/(2^(dim X_V)-1)`. A union bound
over the `2^(dim H′)` vectors of `H′` gives `1 - p(V) <= 2^(l-1-d′)`. ∎

**Lemma 2 (quotient image and lifts).** Let `L′` be uniform on the
`(l-1)`-spaces of `X_V` avoiding `H′`.
(a) Its image `M̄` in `Q` is uniform on `Gr(Q, l-1)`.
(b) For every nonzero linear `w : X_V -> F_2`, `Pr[w|_(L′) = 0] <= 2^(1-l)`.

*Proof.* Fix a linear section `s : Q -> X_V`. The spaces avoiding `H′` with
image `M̄` are exactly the graphs
`{ s(q) + T(q) : q ∈ M̄ }` for linear `T : M̄ -> H′`. The number of these,
`2^((l-1) dim H′)`, is the same for every `M̄`, which gives (a). The map `T` is
uniform given `M̄`.

For (b), write `w(s(q) + T(q)) = w̄(q) + (w|_(H′) ∘ T)(q)`, where
`w̄ := w ∘ s`. There are two cases.
* If `w|_(H′) != 0`, then `w|_(H′) ∘ T` is a uniform linear functional on
  `M̄`, independently of `M̄`. So `w|_(L′) = 0` with probability exactly
  `2^(1-l)`.
* If `w|_(H′) = 0`, then `w` descends to a nonzero functional on `Q`, and
  `w̄` is it. A uniform `(l-1)`-space of `Q` lies in its kernel with probability
  `(2^(d′-l+1) - 1)/(2^(d′) - 1) <= 2^(1-l)`. ∎

## Step 2: the labelling is well defined and unfolds honestly

Let `Φ = (φ, z)` vanish on every equation vector `x_e`. Then:
* `Φ(H_U) = 0` for every tuple;
* `y := x + z` has `y(x_e) = x(x_e)` for every `e`, so `y` satisfies exactly
  the equations that `x` satisfies.

**Lemma 3.** Let `C` be a class with representative `R := R_C`.
(a) For every member `(U,L)` of `C`, `φ(L) = φ(R)`. So `φ` is injective on
    `L` iff it is injective on `R`, since `dim L = dim R = l`.
(b) Suppose `(U,L)` is a member whose `U` is clean for `x`. Then the
    unfolding of the class label `x|_R` at `(U,L)` is `x|_L`, and that of
    `y|_R` is `y|_L`.
(c) Suppose every tuple is clean. Then within a folded constraint between
    `C` and `(V,L′)`, every multi-edge has the same outcome under `h`. So
    `val_(G_folded)(h) = val_(G_multi)(h)`.

*Proof.* (a) Membership means `L + H_U = R + H_U`. Since `φ` kills `H_U`,
`φ(L) = φ(L + H_U) = φ(R + H_U) = φ(R)`.

(b) `x|_(R+H_U)` is linear. It restricts to `x|_R` on `R`, and on `H_U` it
takes the values `x(x_e) = b_e = h_U(x_e)`. By the quoted uniqueness it is the
`(H_U,h_U)`-extension of `x|_R`. Restricting to `L <= R + H_U` gives `x|_L`.
The same argument applies to `y`.

(c) By (a) and (b), every member `(U,L)` of `C` unfolds to `a|_L`, where `a`
is `x` or `y` according to the branch of `C`. Its constraint with `(V,L′)`
tests `a|_(L′) = h_(V,L′)`, and this does not depend on the member. The folded
constraint is the conjunction of these tests, and its weight is the sum of
their weights. ∎

## Step 3: exact branch probabilities on one tuple

Fix a clean `V` on which `Φ` is surjective onto `F_2^(l+1)` (take `m = l`).
Then `φ` and `z` are surjective on `X_V`, hence on `X_U`. Since they vanish
on `H′`, they induce `φ̄ : Q -> F_2^l` (surjective) and `z̄ : Q -> F_2`
(nonzero). In particular `z|_(X_V) != 0`, so `x|_(X_V) != y|_(X_V)`.

**Lemma 4.** Conditioned on `V`:
(a) `b := Pr[φ injective on L′] = Π_(i=0)^(l-2) (1-2^(i-l))/(1-2^(i-d′))`.
(b) Given any `L′` on which `φ` is injective,
    `Pr[φ not injective on L | L′] = c := (2^(3k-1) - 2^(l-1+k))/(2^(3k) - 2^(l-1+k))`.

*Proof.* (a) `φ` kills `H′`, so `φ` is injective on `L′` iff `φ̄` is injective
on the image `M̄`, which is uniform by Lemma 2(a). Count ordered bases
`(q_1, ..., q_(l-1))` of `M̄`. Given `q_1..q_i`, the vector `q_(i+1)` must
avoid `φ̄^(-1)(span φ̄(q_1..q_i))`. This is a subspace of `Q` of dimension
`d′ - l + i`. It is taken out of the `2^(d′) - 2^i` vectors outside
`span(q_1..q_i)`. The ratio of good bases to all bases is
`Π_i (2^(d′) - 2^(d′-l+i)) / (2^(d′) - 2^i)`, which is the displayed product.

(b) By Lemma 1, `L = L′ + <w>` with `w` uniform on `X_U \ (L′ + H_U)`, which has
`2^(3k) - 2^(l-1+k)` elements. Since `φ|_(L′)` is injective, `φ` fails to be
injective on `L` iff `φ(w) ∈ φ(L′)`. That is, `w` lies in `φ^(-1)(φ(L′))`, a
subspace of `X_U` of dimension `3k - l + (l-1) = 3k-1`, because `φ` is
surjective on `X_U`. This subspace contains `L′ + H_U`. So there are
`2^(3k-1) - 2^(l-1+k)` bad `w`. ∎

The general-`m` versions replace `l` by `m` in the numerators:
`(1-2^(i-m))` in (a), and `2^(l-1+3k-m)` in (b). The artifact checks these
exactly (Part B).

## Step 4: value and seed dishonesty on one tuple

Keep `V` clean and surjective. By Lemma 3(b), the A-side label seen by the
edge is `x|_L` if `φ` is injective on `L` and `y|_L` otherwise. The B-label
is `x|_(L′)` or `y|_(L′)` by the same rule on `L′`. Injectivity on `L`
implies injectivity on `L′`. So only three events occur:

| event | probability given `V` | A / B branch | accepted iff |
|---|---|---|---|
| `E_x`: `φ` injective on `L` | `b(1-c)` | x / x | always |
| `E_xy`: injective on `L′`, not on `L` | `bc` | y / x | `z|_(L′) = 0` |
| `E_y`: not injective on `L′` | `1-b` | y / y | always |

Let `p_x` be the satisfied mass with B-branch `x`, and `p_y` that with
B-branch `y`. Then `p_y = 1-b`, and
`p_x = b(1-c) + Pr[E_xy, z|_(L′) = 0]`.

Now `Pr[z|_(L′) = 0] <= 2^(1-l)`, by Lemma 2(b) with `w = z|_(X_V) != 0`.
Therefore:

```text
1 - bc  <=  val_V(h) = p_x + p_y  <=  1 - bc + 2^(1-l).        (4.1)
```

**Lemma 5.** For every linear `λ_V : X_V -> F_2`,
`D_V(h, λ) >= min(p_x, p_y) - 2^(1-l) >= min(b(1-c), 1-b) - 2^(1-l)`.

*Proof.* Since `x|_(X_V) != y|_(X_V)`, `λ_V` differs from at least one of
them. Say `λ_V != x|_(X_V)`; the case of `y` is symmetric. The satisfied
x-branch edges whose B-label `x|_(L′)` equals `λ_V|_(L′)` have
`(λ_V - x)|_(L′) = 0`. By Lemma 2(b) this has probability at most `2^(1-l)`.

So the satisfied mass agreeing with `λ_V` is at most `p_y + 2^(1-l)`, and
`D_V >= p_x - 2^(1-l)`. In the symmetric case `D_V >= p_y - 2^(1-l)`. Take the
minimum. ∎

This is where every single-reference statement dies. `λ` is a per-`V` object,
but the branch is decided by `rank φ|_(L′)`, which varies with `L′` inside
each `V`, with constant mass `b` on one side and `1-b` on the other.

## Step 5: summing over tuples, and the numbers

Let `Bad` be the set of `V` that are unclean or non-surjective, and let `β_bad`
be its `G_multi` mass. By Lemma 1 and item 4 of the decoding-hypotheses node,
`β_bad <= (Pr_smooth[Bad] + 2^(l-1-k)) / (1 - 2^(l-1-k))`. Unclean mass is at
most `ε_out(x)`, and it is `0` when `x` satisfies everything.

For fixed `l`, the quantities `b` and `c` depend on `V` only through `d′ >= k`,
and:
* `b_l <= b <= b_l Π_(i<l-1) (1-2^(i-d′))^(-1) <= b_l (1 + 2^(l-k))`, where
  `b_l := Π_(i=0)^(l-2)(1-2^(i-l)) = Π_(j=2)^l (1-2^(-j))`;
* `|c - 1/2| <= 2^(l-2k)`.

Averaging (4.1) and Lemma 5 over good `V`, and charging `β_bad` fully, gives,
with `o_k(1) := O(2^(l-k) + β_bad)`:

```text
val(h)   in  [ 1 - b_l/2 - o_k(1),  1 - b_l/2 + 2^(1-l) + o_k(1) ]
D(h, λ)  >=  min(b_l/2, 1 - b_l) - 2^(1-l) - o_k(1)   for every λ.
```

We have `b_l > P_1 = 0.5776` and `b_l <= b_2 = 3/4`. So `b_l/2 < 1 - b_l` iff
`b_l < 2/3`, which holds for `l >= 3` (`b_3 = 21/32 = 0.656`). With
`γ := val(h) - 1/2`:

```text
D - γ    >=  b_l - 1/2 - 2·2^(1-l) - o_k(1)
D - γ/2  >=  3b_l/4 - 1/4 - (3/2)·2^(1-l) - o_k(1).
```

The artifact's Part A table charges `3·2^(1-l)` against `γ`, which is weaker.
It gives `D - γ > 0` from `l = 7` on (`+0.035`) and `D - γ/2 > 0` from `l = 5`
on. As `l -> infinity` the margins tend to `P_1 - 1/2 = 0.077576` and
`3P_1/4 - 1/4 = 0.183`. Here `P_1 = Π_(j>=2)(1-2^(-j))`, the `q = 1/2`
Euler-function product divided by `1/2`, which the artifact computes to 200
terms.

**Corollary M.** Assume `(Seed)` held with parameter
`γ <= γ_0(l) := 1/2 - b_l/2 - 2^(-l)`. The labelling `h` has value
`>= 1/2 + γ_0(l) >= 1/2 + γ` once `o_k(1) < 2^(-l)`. So `(Seed)` would give an
outer labelling `λ` with `D(h, λ) <= γ/2 <= γ_actual/2`. This contradicts
`D - γ_actual/2 > 0` for `l >= 5`. On the J-instances `x = 0` satisfies
everything, so by Lemma 3(c) the folded and multi-edge values agree. ∎

## Step 6: the J-instances have a generic kernel of rank m+1

Take `N` disjoint copies of `F_2^(m+1) \ {0}` as variables. For each copy and
each 2-dimensional subspace `{0, u, u′, u+u′}`, take the equation
`x_u + x_(u′) + x_(u+u′) = 0`.

**Regularity.** Each point lies on `(2^(m+1) - 2)/2 = 2^m - 1` lines of its
copy.

**Homogeneity.** For `Φ(e_u) := u`, extended linearly and summed over copies,
`Φ(x_e) = u + u′ + (u+u′) = 0`. Every coordinate of `Φ` is therefore a
homogeneous solution, and `x = 0` satisfies every equation.

**Surjectivity.** `Φ(X_V)` is the span of the labels of the variables of `V`.
It is proper iff all these labels lie in some hyperplane `ker ψ`, where `ψ`
ranges over the `2^(m+1) - 1` nonzero functionals.

Each of the `k` blocks of `U` contributes either a whole line (kept) or a
point of it (dropped). Compare a uniform tuple of disjoint lines with `k`
independent uniform lines. The two laws are within total variation `O(k^2/N)`
of each other. A fixed line meets at most `3·2^m` of the
`N(2^(m+1)-1)(2^m-1)/3` lines, which is a fraction `O(1/(N 2^m))`, and a union
bound over the `k^2` pairs of blocks gives the total.

For one independent uniform line, and its independently chosen point:
* the probability that the point lies in `ker ψ` is
  `(2^m - 1)/(2^(m+1) - 1) < 1/2`;
* the probability that the line lies in `ker ψ` is smaller.

So

```text
Pr[Φ not surjective on X_V]  <=  2^(m+1) 2^(-k) + O(k^2/N).
```

The artifact's Part D takes `m = 3`, 60 copies, `k = 8`, `β = 0.3` and 4000
tuples. It finds 15 variables and 35 equations per copy, degree 7, `Φ`
vanishing on every equation vector, and a failure frequency of `0.0005`
against the bound `0.0625`.

This proves Theorem M and Corollary M on the J-instances with
`N >> k^2 2^(2l)` and `k -> infinity`.

## Step 7: the padded family (Remark P), conditional part

Let `I` be regular of degree `D_I`. Repeat every equation of `I` `r_I` times
and every line of `J` `r_J` times, with `r_I D_I = r_J (2^l - 1)`. Take
`N` copies of `J` to set the J-weight `ω`. Extend `φ, z` by `0` on the
variables of `I`; they still vanish on every equation vector.

A uniform tuple has `t ~ Bin(k, ω)` J-blocks, up to `O(k^2/|X|)`. Only the
J-blocks can contribute labels, so by Step 6 applied to them,

`Pr[not surjective] <= 2^(l+1) E[2^(-t)] + O(k^2/N) = 2^(l+1)(1-ω/2)^k + O(k^2/N)`.

Let `x` be an assignment of `I` violating an `ε_3` fraction, extended by `0`
on `J`. Unclean mass is then `ε_out(x) <= kε_3/(1-O(k^2/|X|))`, which is
item 5 of the decoding-hypotheses node.

So Steps 1-5 hold verbatim on the multi-edge game, with
`β_bad = O(kε_3 + 2^(l+1) e^(-ωk/2) + k^2/N + 2^(l-k))`.

The map `I -> I ⊔ J` is polynomial. It sends YES instances of
`Gap3Lin(1-ε_3, s*)` to YES instances of `Gap3Lin(1-ε_3, ·)`, and NO instances
to instances of value at most `s′ = (1-ω)s* + ω`. The Corollary of the
decoding-hypotheses node, and Theorem C, invoke Lemma 5.4 of DKKMS on their
inputs. As quoted there, Lemma 5.4 is stated for regular 3LIN inputs of value
at most `s*`.

**The transfer is therefore conditional on Lemma 5.4 holding at soundness
`s′`,** with `q` replaced by some `q(s′)`. This is not claimed here.
Theorem M and Corollary M do not depend on it: they refute `(Seed)` as a
universal statement about DKKMS games.

## Step 8: why this kills the single-reference class

Let `S` be any statement that concludes, from `val(h) >= 1/2 + γ`, that for
one outer labelling `λ` (or any per-`V` functional family), the satisfied
B-labels agree with `hon(λ)` outside mass `f(γ)`, where `f(γ) <= γ`.
Steps 4 and 5 give `D(h,λ) - γ >= b_l - 1/2 - 2^(2-l) - o_k(1) > 0` for all
`λ` once `l >= 6`, so `S` fails on `h`.

The only property of the input used is a homogeneous kernel of rank `l+1`
that is surjective on almost every `X_V`. Consequently, a proof of any such
`S` must use an input property that excludes it. Examples are "the
homogeneous system has no rank-`(l+1)` solution space generic on tuples", or
a list of references in place of one.

Lemma 5 shows the obstacle is exactly two good references, `x` and `y`, split
along `L′`. So the list version with two references is not refuted by `h`.
Part C of the artifact searches all rank-threshold labellings with up to 3
branches in the limit model. If every branch mass is at most `0.25`, the best
value is `0.134`, below `1/2`. This is evidence, not proof, for the list
version in this family.
