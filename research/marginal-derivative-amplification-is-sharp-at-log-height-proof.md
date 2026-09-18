---
rg: 2
id: marginal-derivative-amplification-is-sharp-at-log-height-proof
kind: route
title: Proof that marginal-derivative amplification is sharp at logarithmic height
target: marginal-derivative-amplification-is-sharp-at-log-height
requires: []
---

Notation is as in the target. Partial actions follow Moore's Def. 3.1, quoted verbatim from the
TeX source of arXiv:0905.1118v7:

> A *partial action* of G on a set S is a partial function ·: S × G → S such that:
> x · e = x for all x ∈ S; x · g = y if and only if x = y · g^{-1} for all g ∈ G and
> x,y ∈ S; x · (gh) = (x · g) · h for all g,h ∈ G and all x ∈ S for which all computations
> involving · are defined.

**Consequence used throughout.** For fixed `γ`, the map `s ↦ s·γ` is injective on its domain,
because `s·γ = y` forces `s = y·γ^{-1}`. Write `bd_γ(μ) = Σ_s |μ(s·γ) − μ(s)|`, so that
`bd = Σ_γ bd_γ`.

## Step 1: restriction costs at most `2|Γ|μ(B)`

Let `μ ≥ 0` be finitely supported and `ν = μ·1_A`. Then `μ − ν = μ·1_B ≥ 0`, and pointwise
`|ν(sγ) − ν(s)| ≤ |μ(sγ) − μ(s)| + (μ−ν)(sγ) + (μ−ν)(s)`.

Sum over `s`:
- `Σ_s (μ−ν)(s) = μ(B)`;
- `Σ_s (μ−ν)(s·γ) ≤ μ(B)`, by injectivity of `s ↦ s·γ`.

Hence `bd(ν) ≤ bd(μ) + 2|Γ|μ(B)`. This is the mechanism of Moore's Lemma 3.11, written additively.

## Step 2: pushforward along `∂` does not increase `bd` on measures carried by `A`

Let `ν ≥ 0` be finitely supported with `ν(B) = 0`, and let `ν' = ∂_*ν`, so
`ν'(t) = Σ_{∂s = t} ν(s)`. Fix `γ ∈ Γ` and `t ∈ S`. Every sum below runs over `s ∈ S` with
`∂s = t`.

*Case `t·γ` defined.* We claim `ν'(t·γ) = Σ ν(s·γ)`, where terms with `s·γ` undefined vanish.
- Let `s' ∈ A` with `∂s' = t·γ`. Since `(t·γ)·γ^{-1} = t` is defined and `γ^{-1} ∈ Γ`,
  (E′) at `s'` shows that `s := s'·γ^{-1}` is defined with `∂s = ∂(s')·γ^{-1} = t`. By Def. 3.1,
  `s·γ = s'`.
- Conversely, let `∂s = t` with `s·γ =: s' ∈ A`. Then `s'·γ^{-1} = s`, and (E′) at `s'` gives
  `t = ∂(s')·γ^{-1}`, hence `∂s' = t·γ`.
- So `s ↦ s·γ` is a bijection from `{s : ∂s = t, s·γ ∈ A}` onto `{s' ∈ A : ∂s' = t·γ}`.
  Since `ν` vanishes off `A`, the claim follows.

Therefore `ν'(t·γ) − ν'(t) = Σ [ν(s·γ) − ν(s)]`, and
`|ν'(t·γ) − ν'(t)| ≤ Σ |ν(s·γ) − ν(s)|`.

*Case `t·γ` undefined.* Then `ν'(t·γ) = 0` by convention. For `s ∈ A` with `∂s = t`, (E′) makes
`s·γ` undefined, so `ν(s) = |ν(s·γ) − ν(s)|`. Terms with `s ∉ A` contribute `0` to `ν'(t)`.
Hence again `|ν'(t·γ) − ν'(t)| ≤ Σ |ν(s·γ) − ν(s)|`.

The fibres `∂^{-1}(t)` partition `S`, so summing over `t` gives `bd_γ(ν') ≤ bd_γ(ν)`, and
therefore `bd(ν') ≤ bd(ν)`. This is Moore's Lemma 3.4 applied to `ν = μ↾𝒜`, with its hypothesis
supplied by (E′). His statement, verbatim:

> Suppose G acts partially on sets S and T and that μ is a weighted ε-Følner set with respect to
> the action on S. If h:S → T satisfies that h(s · γ) = h(s) · γ (with both quantities defined)
> whenever μ(s)+μ(s · γ)>0 and γ ∈ Γ, then ν(t) = Σ_{h(s)=t} μ(s) defines a weighted ε-Følner
> set.

## Step 3: the recursion and Theorem A

Put `μ_0 = μ` and `μ_{i+1} = ∂_*(μ_i·1_A)`, and write `m_i = μ_i(S)` and `b_i = bd(μ_i)`.

*Identification.* By induction, `μ_i = ∂^i_*(μ·1_{h≥i})`. For `i = 0` this is trivial. For the
step, `μ_i(t)` for `t ∈ A` collects the `s` with `h(s) ≥ i` and `∂^i s = t ∈ A`, which are exactly
the `s` with `h(s) ≥ i+1`; pushing forward by `∂` gives `μ_{i+1}`. In particular
`m_n = μ({h ≥ n})`.

*Mass.* `m_{i+1} = μ_i(A) = m_i − μ_i(B) ≥ m_i − c·b_i`, by `c`-thinness.

*Boundary.* By Steps 1 and 2 and thinness,
`b_{i+1} ≤ bd(μ_i·1_A) ≤ b_i + 2|Γ|μ_i(B) ≤ (1 + 2c|Γ|)b_i = q·b_i`, so `b_i ≤ qⁱ b_0`.

Summing the mass inequality:
`m_n ≥ m_0 − c·b_0·(1 + q + … + q^{n−1}) = m_0 − b_0(qⁿ − 1)/(2|Γ|)`, since `q − 1 = 2c|Γ|`.
This is item 1.

*Item 2.* Let `μ` be weighted `ε`-Følner, so `b_0 < ε m_0` and `m_0 > 0`, and let
`n = ⌊log_q(1 + 2|Γ|/ε)⌋`, so that `ε(qⁿ − 1) ≤ 2|Γ|`. If `n = 0` there is nothing to prove.
Otherwise
`m_n > m_0 − ε m_0 (qⁿ−1)/(2|Γ|) ≥ 0`,
so `{h ≥ n}` meets the support of `μ`.

*Item 3.* If `h(s) ≥ n`, then `s, ∂s, …, ∂^{n−1}s ∈ A`. Hence
`|s| ≥ φ(|∂s|) ≥ φ(φ(|∂²s|)) ≥ … ≥ φ^{(n)}(|∂ⁿ s|) ≥ φ^{(n)}(m_*)`. This uses that `φ` is
nondecreasing and that `|∂ⁿ s| = |∂(∂^{n−1}s)| ≥ m_*`, because `∂^{n−1}s ∈ A`.

*Marginal implies thin.* Moore's Lemma 3.10, verbatim:

> If E ⊆ S is marginal, then there is a constant C such that if ε > 0 and μ is a weighted
> ε-Følner set, then μ(E) < C ε μ(S).

Given a nonzero finitely supported `μ ≥ 0` and `δ > 0`, the function `μ` is weighted
`(bd(μ)/μ(S) + δ)`-Følner. So `μ(E) < C·bd(μ) + Cδμ(S)`, and letting `δ → 0` gives
`μ(E) ≤ C·bd(μ)`. For `μ = 0` this is trivial.

## Step 4: composition

**Claim.** For `r ≥ 1`, `(∂^r, A_r = {h ≥ r})` is a derivative datum with bad set `c_r`-thin,
where `c_r = (qʳ−1)/(2|Γ|)`.

*(E′).* Let `s ∈ A_r`, so `s, ∂s, …, ∂^{r−1}s ∈ A`. Applying (E′) at each of these in turn gives
`s·γ` defined ⟺ `∂s·γ` defined ⟺ … ⟺ `∂^r s·γ` defined, and then `∂^r(s·γ) = ∂^r(s)·γ`.

*Thinness.* Item 1 gives `μ({h < r}) ≤ bd(μ)(qʳ − 1)/(2|Γ|)`.

*Rate.* Hence `q_r = 1 + 2|Γ|c_r = qʳ`. The height for `∂^r` is `⌊h/r⌋`, so Theorem A for `∂^r`
certifies `⌊log_{qʳ}(1 + 2|Γ|/ε)⌋` steps of `∂^r`, that is, `r` times as many `∂`-steps. This is
the same as Theorem A for `∂`, up to rounding. Bundling steps gives nothing.

## Step 5: Moore's instance

Moore's definitions and lemmas below are quoted verbatim from the TeX source of arXiv:0905.1118v7,
with TeX macros expanded.

**Definitions.**

> If U and V are in 𝒯, then we will say that U is *dominated by* V if every element of U has a
> extension in V.

> If T is in 𝒯 and f is in F with f defined on all of T, then T · f is the pointwise image of T
> under f. It is easily checked that this results in an element of 𝒯 and hence this defines a
> partial right action of F on 𝒯. If T is in 𝒯 and f is in F, then f *acts properly* on T if it
> acts properly on the elements of T.

> In particular, if f acts properly on t, it acts properly on any extension of t.

**Lemma 5.4.**

> If ∂T has n elements, then T has more than 2^{n−2} elements.

**Lemma 5.5.**

> If g is in F, T is in 𝒯, and g acts properly on ∂T, then ∂(T · g) = (∂T) · g.

**Lemma 5.12.**

> The set {T ∈ 𝒯 : Γ does not act properly on ∂T} is marginal.

Here `Γ = {x0, x1, x0^{-1}, x1^{-1}}`, and `∂` is Moore's Definition 5.1.

**Verification.** Let `A = {T : Γ acts properly on ∂T}`.

*Every leaf of `T` extends a leaf of `∂T`.* Both `T` and `∂T` are complete prefix codes, and
`∂T` is dominated by `T`. Given `v ∈ T`, some `u ∈ ∂T` is comparable with `v`. Suppose `v` were a
proper initial part of `u`. Then the extension of `u` in `T` would properly extend `v ∈ T`,
contradicting prefix-freeness. So `u ⊆ v`.

*(E′) holds, in the strong form.* Let `T ∈ A` and `γ ∈ Γ`. Then `γ` acts properly on every leaf of
`∂T`, hence on every leaf of `T`. So `T·γ` and `(∂T)·γ` are both defined, and
`∂(T·γ) = (∂T)·γ` by Lemma 5.5.

*`B` is thin.* `B = S ∖ A` is marginal by Lemma 5.12, hence thin by Step 3.

*Size contraction.* Put `|T| = #T`.
- Lemma 5.4 says the integer `|T|` strictly exceeds `2^{|∂T|−2}`. So
  `|T| ≥ ⌊2^{|∂T|−2}⌋ + 1 =: φ(|∂T|)`, and `φ` is nondecreasing.
- `m_* ≥ 4`. For `T ∈ A`, the generator `x0` acts properly on `∂T`, but it is undefined on the
  empty sequence, so `∂T` is non-trivial. By defining condition 1 of Moore's Definition 5.1,
  `∂T` then has leaves extending each of `00`, `01`, `10`, `11`. This is the `k_0 ≥ 4` of his
  Claim 5.14.
- The iterates are `φ(4) = 5`, `φ(5) = 9`, `φ(9) = 129`, and `φ^{(n)}(4) ≥ exp_n(0)`.

So Theorem A turns a weighted `ε`-Følner set of trees into a tree with at least `φ^{(n)}(4)`
leaves, where `n = ⌊log_q(1 + 8/ε)⌋`. That is a tower of height `≍ log(1/ε)`.

Moore's own bookkeeping (Lemma 5.13 and Claim 5.14) is the special case in which each
restriction-and-push multiplies `ε` by a constant `K`. Theorem A makes that constant explicit as
`q = 1 + 2c|Γ|`.

## Step 6: Theorem B, the sharpness datum

Fix an integer `K ≥ 2` and put `L_j = 3K^j`.

**The partial action.**
- `S = ⊔_{j≥0} P_j`, where `P_j = {j} × {0, …, L_j − 1}`.
- `ℤ` acts partially by `(j,x)·t^k = (j, x+k)` when `0 ≤ x+k < L_j`, and is undefined otherwise.
  This is a partial action, being the restriction of translation on `ℤ` to a subset, taken on
  each copy.
- `F` acts through the homomorphism `π : F → ℤ` with `π(x0) = t` and `π(x1) = e`, by
  `s·g := s·π(g)`. The three axioms of Def. 3.1 transfer through `π`.
- With Moore's `Γ = {x0^±1, x1^±1}`, the elements `x1^±1` act as the identity and contribute `0`
  to `bd`. So `bd` is the same as for `ℤ` with `{t^±1}`.

**The derivative datum.**
- For `j ≥ 1`, `∂(j,x) = (j−1, x mod L_{j−1})`. On `P_0`, `∂` is the identity.
- `A = {(j,x) : j ≥ 1, x mod L_{j−1} ∉ {0, L_{j−1}−1}}`.
- So `B ∩ P_0 = P_0` has `3` points, and for `j ≥ 1`, `B ∩ P_j` has exactly `2K` points: the two
  ends of each of the `K` blocks of length `L_{j−1}`.

**(E), both sides always defined.** Let `s = (j,x) ∈ A` and `r = x mod L_{j−1}`, so
`1 ≤ r ≤ L_{j−1} − 2`.
- Since `L_{j−1}` divides `L_j`, `r ≤ L_{j−1} − 2` forces `x ≤ L_j − 2`, and `r ≥ 1` forces
  `x ≥ 1`. So `s·t^{±1}` is defined.
- `∂(s)·t^{±1} = (j−1, r±1)` is defined, and `(x±1) mod L_{j−1} = r ± 1`.
- Hence `∂(s·t^{±1}) = ∂(s)·t^{±1}`. For `x1^{±1}` both sides are trivially equal.

**`B` is 1-marginal in Moore's sense.** Recall his definitions, verbatim:

> If g ∈ G, I ⊆ S, and E ⊆ S, then *g marginalizes E off I* if for every x ∈ E if x · g^k ∈ E
> and k > 0, then there is an i < k such that x · g^i is in I or is undefined. If I is the
> emptyset, then I will write g *marginalizes* E.

> The emptyset is 0-marginal. If there is a decomposition E = ⋃_{i<l} E_i ⊆ S and for each
> i < l, there is a g_i ∈ G and a k-marginal set I_i such that g_i marginalizes E_i off I_i,
> then E is (k+1)-marginal.

Enumerate `B ∩ P_j` increasingly as `β_j(0) < β_j(1) < …`; there are at most `2K` terms, since
`3 ≤ 2K`. Put `E_i = {β_j(i) : j ≥ 0}` for `i < 2K`, so that `B = ⋃_{i<2K} E_i`.
- Each `E_i` meets each `x0`-orbit `P_j` in at most one point.
- `x·x0^k ≠ x` for `k > 0` whenever it is defined.
- So the hypothesis `x·x0^k ∈ E_i` never occurs, and `x0` marginalizes `E_i` off `∅`, vacuously.

Hence `B` is 1-marginal.

**`B` is `K`-thin (direct proof, with the constant).**

*Layer cake.* For finitely supported `μ ≥ 0`, put `U_λ = {μ > λ}`. For `a, b ≥ 0`,
`|a − b| = ∫_0^∞ |1_{a>λ} − 1_{b>λ}| dλ`. Hence `bd(μ) = ∫_0^∞ bd(1_{U_λ}) dλ` and
`μ(B) = ∫_0^∞ |B ∩ U_λ| dλ`. So it suffices to show `|B ∩ U| ≤ K·bd(1_U)` for every finite `U`.

*Runs.* Decompose `U` into maximal runs, that is, maximal intervals of consecutive points inside
one `P_j`.
- Take a run `[a,b]` in `P_j`. The generator `x0` sees its right end: either `b+1` lies outside
  `U` or `b·x0` is undefined. Either way this contributes `1` to `bd_{x0}`.
- Likewise `x0^{-1}` sees its left end and contributes `1` to `bd_{x0^{-1}}`.
- Distinct runs give distinct contributing points, so `bd(1_U) ≥ 2·#runs`.

*Counting.* A run inside `P_j` contains at most `|B ∩ P_j| ≤ 2K` bad points. Hence
`|B ∩ U| ≤ 2K·#runs ≤ K·bd(1_U)`.

**Følner sets of bounded height.**
- `U = P_j` is a single run with both ends at the boundary of the orbit. So
  `bd(1_{P_j}) = 1 + 1 = 2` and `|P_j| = 3K^j`, and `P_j` is `ε`-Følner for every
  `ε > 2/(3K^j)`.
- For `s ∈ P_j` we have `∂^j s ∈ P_0 ⊆ B`, so `h(s) ≤ j`.
- Given `ε ∈ (2/(3K^j), 2/(3K^{j−1})]`, the set `P_j` is `ε`-Følner and all its heights are
  `≤ j < log_K(2/(3ε)) + 1`.

**Sizes.** Put `|(j,x)| = φ^{(j)}(1)` for any nondecreasing `φ`. On `A` this gives
`|s| = φ(|∂s|)`, and the largest size in the support of `P_j` is `φ^{(j)}(1)`.

**Comparison.** Theorem A, with `c = K` and `|Γ| = 4`, guarantees height
`⌊log_{8K+1}(1 + 8/ε)⌋`. The datum shows height `≤ log_K(2/(3ε)) + 1`. The two agree up to the
base of the logarithm.

**The loss is realized.** `μ_0 = 1_{P_j}` has ratio `2/(3K^j)`. After `i` restriction-and-push
steps, with `1 ≤ i ≤ j−1`, we have `μ_i = K^i·1_{{j−i}×[1, L_{j−i}−2]}`.
- Induction: restricting `μ_{i−1}` to `A` removes the block ends of `P_{j−i+1}`.
- Then each of its `K` blocks pushes its interior onto `{j−i} × [1, L_{j−i}−2]` with weight
  `K^{i−1}`.

So `bd(μ_i) = 4K^i` and `μ_i(S) = K^i(3K^{j−i} − 2)`. The ratio is `4/(3K^{j−i} − 2)`, so each
step multiplies the Følner ratio by `≍ K`, exactly the loss Theorem A allows up to the constant.

## Step 7: why this kills the class

**What the class is.** An argument in the class sees only:
- the partial action;
- the pair `(∂, A)` with (E′);
- the thinness or marginality constant of `B`;
- the contraction `|s| ≥ φ(|∂s|)`.

**Why no argument in the class does better.** Suppose such an argument concluded
"ε-Følner ⇒ some support point has height `≥ H(ε)`" uniformly over data with a given constant
`c`. Step 6, with `K = ⌈c⌉ ≥ 2`, forces `H(ε) ≤ log_K(2/(3ε)) + 1`. This holds even on a partial
`F`-set with Moore's generators and a 1-marginal `B`.

**Consequences.**
- With `φ` exponential, the certified size is at most a tower of height `O(log 1/ε)`, which is
  Moore's bound.
- Iterating finitely many derivatives, or bundling them (Step 4), does not change the rate.
- To exceed every tower in `log(1/ε)` one needs a faster `φ`, that is, a new derivative on `𝒯`.
  This is the prerequisite `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`.
