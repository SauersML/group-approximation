---
rg: 2
id: dkkms-list-seed-needs-lists-exponential-in-l-proof
kind: route
title: Derive the conditional edge law, show the defect-line labelling is class invariant because the kernel kills H_U, bound growth of the defect line by 2^(-1-N), compute the nullity law, bound what one reference covers on the defect branches by GL-invariance and orbit counting, and sum over tuples of a J-instance with a rank-2l kernel
target: dkkms-list-seed-needs-lists-exponential-in-l
requires:
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - dkkms-near-perfect-labellings-are-outer-honest
artifacts:
  - experiments/ugc-list-seed-2026-09-17/check_defect_split_mixture.py
---

Notation is that of the target and of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` (below: the
decoding node). That node quotes verbatim the vertices, the edge process, the
constraint, the folding classes (DKKMS Lemma 4.1) and the unfolding
(Definition 4.2) of ECCC TR16-198. Two of its items are used:
* item 3: given `((V,L′), U)`, the new direction is uniform on
  `X_U \ (L′ + H_U)`;
* item 4: the `U`-marginal of `G_multi` is uniform.

The unfolding uniqueness is quoted verbatim as (Q4) in
`dkkms-near-perfect-labellings-are-outer-honest-proof`:

> "if L∩H = φ then any linear function f : L → F2 has a unique (H,h)-extension,
> ˜f : L + H → F2, where ˜f(z) = f(x) + h(y) and where z = x + y is the unique
> way to write z as a sum of x∈L and y∈H."

Steps 1 and 2 re-derive, self-contained, the lemmas that the rank-split
mixture node of wave 12 uses (that node is not on main). Everything else is new.

Throughout: `U` is a tuple, `V` its smoothed tuple, `H′ := H_U ∩ X_V`,
`Q := X_V / H′`, `d′ := dim Q`. `H′` is spanned by the `x_e` of the kept
equations, since a dropped equation contributes one coordinate vector to `X_V`,
so `d′ = 2·#kept + #dropped >= k`. `n := l + s`, `Φ = (φ, ζ) : F_2^X -> F_2^l x F_2^s`,
`K = 0 x F_2^s`, `π : F_2^n -> F_2^l` the first projection, so `φ = π ∘ Φ`.

## Step 1: the conditional edge law

**Lemma 1.** Under `G_multi`, conditioned on `V`:
* `L′` is uniform on the `(l-1)`-subspaces of `X_V` with `L′ ∩ H′ = 0`;
* given `(V, L′)`, `L = L′ + <w>` with `w` uniform on `X_U \ (L′ + H_U)`.

The `V`-marginal is the smoothing law reweighted by
`p(V) := Pr[L′ ∩ H′ = 0 | V] >= 1 - 2^(l-1-d′)`.

*Proof.* The process draws `L′` uniformly from `Gr(X_V, l-1)` and `L`
uniformly among the `l`-spaces of `X_U` containing `L′`, and keeps the output
iff `L ∩ H_U = 0`. Since `L′ <= X_V`, `L′ ∩ H_U = L′ ∩ H′`; if it is nonzero
nothing is kept. Otherwise `L = L′ + <w>` is kept iff `w ∉ L′ + H_U`, a space of
dimension `l-1+k`, and each `L` arises from exactly `2^(l-1)` vectors
`w ∈ L \ L′`. The keep probability `(2^(3k) - 2^(l-1+k))/(2^(3k) - 2^(l-1))`
does not depend on `L′` or `V`. This gives both bullets; the second is also
item 3 of the decoding node. A fixed nonzero vector of `H′` lies in a uniform
`(l-1)`-space of `X_V` with probability `(2^(l-1)-1)/(2^(dim X_V)-1)`; a union
bound over `H′` gives `1 - p(V) <= 2^(l-1-d′)`. ∎

**Lemma 2 (graphs).** Let `L′` be uniform on the `(l-1)`-spaces of `X_V`
avoiding `H′`, and fix a linear section `σ : Q -> X_V`.
(a) The image `M̄` of `L′` in `Q` is uniform on `Gr(Q, l-1)`, and given `M̄`,
    `L′ = { σ(q) + T(q) : q ∈ M̄ }` with `T : M̄ -> H′` uniform.
(b) If a functional `μ : X_V -> F_2` has `μ|_(H′) != 0`, then for every event
    `E` determined by `M̄`, `Pr[μ|_(L′) = 0, E] = 2^(1-l) Pr[E]`.

*Proof.* (a) The spaces avoiding `H′` with image `M̄` are exactly these graphs,
one for each linear `T`, so there are `2^((l-1) dim H′)` of them for every
`M̄`. (b) `μ(σ(q) + T(q)) = μ(σ(q)) + (μ|_(H′) ∘ T)(q)`, and `μ|_(H′) ∘ T` is a
uniform functional on `M̄` given `M̄`. So `μ|_(L′) = 0` has conditional
probability exactly `2^(1-l)`. ∎

Since `Φ` kills every `x_e`, it kills `H′` and `H_U`, and induces
`Φ̄ : Q -> F_2^n` with `Φ(L′) = Φ̄(M̄) =: P`. In particular `c(L′) = P ∩ K`
is a function of `M̄`. Put `N0 := ker Φ̄`.

## Step 2: class invariance and honest unfolding (item 1)

Each `y_d = x + <d, ζ(·)>` is linear on `F_2^X` with `y_d(x_e) = x(x_e)` for
every equation, because `ζ(x_e) = 0`. So `y_d` satisfies exactly the equations
`x` satisfies.

**Lemma 3.** Let `C` be a class with representative `R := R_C` and let
`(U,L) ∈ C`. Then (a) `Φ(L) = Φ(R)`, hence `c(L) = c(R)`; (b) if `x` satisfies
every equation of `U`, the unfolding of `a|_R` at `(U,L)` is `a|_L`, for
`a ∈ {x} ∪ {y_d}`.

*Proof.* (a) Membership means `L + H_U = R + H_U`, and `Φ(H_U) = 0`, so
`Φ(L) = Φ(L + H_U) = Φ(R + H_U) = Φ(R)`. (b) `a|_(R + H_U)` is linear, equals
`a|_R` on `R`, and equals `a(x_e) = x(x_e) = b_e = h_U(x_e)` on `H_U`. By (Q4)
it is the `(H_U, h_U)`-extension of `a|_R`; restrict to `L <= R + H_U`. ∎

So when `x` satisfies every equation (Step 7), every member `(U,L)` of `C`
unfolds `h_C` to `a_C|_L`, where `a_C` is the branch assignment fixed by
`c(R_C) = c(L)`. The test of a multi-edge `((U,L),(V,L′))` is
`a_C|_(L′) = h_(V,L′)`, which does not depend on the member. A folded
constraint is the conjunction of its multi-edges with summed weight. So the
folded value of `h` equals its `G_multi` value, and the same holds for the
satisfied mass on any set of B-vertices. This is item 1.

## Step 3: growth of the defect line (item 2)

Fix `V` with `Φ` surjective on `X_V`. Then `φ` is surjective on `X_V`, hence
on `X_U`. Let `r′ := rank φ|_(L′) = (l-1) - N`.

**Lemma 4.** Given `L′`, `Pr[c(L) != c(L′) | L′] <= 2^(-1-N)`.

*Proof.* `Φ(L) = P + <Φ(w)>`. If `Φ(w) ∈ P` then `c(L) = c(L′)`. Otherwise
`c(L) = (P + <Φ(w)>) ∩ K` is larger than `P ∩ K` iff some `p ∈ P` has
`p + Φ(w) ∈ K`, that is iff `φ(w) = π(Φ(w)) ∈ π(P) = φ(L′)`. So the bad `w`
lie in `φ^(-1)(φ(L′))`, a subspace of `X_U` of dimension `3k - l + r′` that
contains `L′ + H_U` (because `φ(H_U) = 0`). By Lemma 1 the probability is at
most `(2^(3k-l+r′) - 2^(l-1+k))/(2^(3k) - 2^(l-1+k)) <= 2^(r′-l) = 2^(-1-N)`. ∎

If `c(L) = c(L′)`, the A-branch and the B-branch are the same assignment `a`,
and by Step 2 the edge tests `a|_(L′) = a|_(L′)`, so it is accepted. Hence
`val_V(h) >= 1 - E[2^(-1-N) | V]`. This is item 2.

## Step 4: the nullity law and the defect mass

Since `L′ ∩ H′ = 0`, `L′ ≅ M̄` and `φ|_(L′)` corresponds to
`φ̄ := π ∘ Φ̄` on `M̄`. Its kernel is `(Φ̄|_(M̄))^(-1)(P ∩ K)`, so

```text
N  =  dim(M̄ ∩ N0) + dim c(L′).                                   (4.1)
```

**Lemma 5 (law of N).** Build `M̄` from a uniform ordered basis
`q_1, ..., q_(l-1)`. Given `q_1..q_i` with image rank `r`, the next vector keeps
the rank iff it lies in `φ̄^(-1)(span φ̄(q_1..q_i)) \ span(q_1..q_i)`, which has
probability `(2^(d′-l+r) - 2^i)/(2^(d′) - 2^i)`. This Markov chain is exactly
`nullity_law(l, d′)` in the artifact. Its per-step stay probability is within
`2^i/(2^(d′) - 2^i) <= 2^(i+1-d′)` of the limit value `2^(r-l)`, so the law of
`N` is within total variation `2^(l-d′) <= 2^(l-k)` of the limit law
`nullity_law(l)`. In the limit `P(N=0) = Π_(j=2)^l (1 - 2^(-j)) = b_l`
(checked).

**Lemma 6 (the chain in l).** Let `N_l` have the limit law. Index the steps
from the end, `j = l-2-i`; with `r = i - (nullity so far)`, the stay
probability is `2^(-2-j-(nullity so far))`. So the chain for `l+1` is the chain
for `l` preceded by one step (`j = l-1`, from nullity 0) that stays with
probability `2^(-1-l)`; if it does not stay, the rest is the chain for `l`.
Hence `TV(N_(l+1), N_l) <= 2^(-1-l)` and `TV(N_l, N_oo) <= 2^(-l)`. The
artifact evaluates the law exactly for `8 <= l <= 64`; beyond that every
quantity below moves by less than `2^(-60)` from its value at `l = 64`.

**Lemma 7 (small events).** (a) `Pr[M̄ ∩ N0 != 0 | V] <= 2^(-s-1)`.
(b) The law of `P` is invariant under `GL(F_2^n)`, so for every nonzero
`p ∈ F_2^n`, `Pr[p ∈ P | V] <= (2^(l-1) - 1)/(2^n - 1) < 2^(-s-1)`.

*Proof.* (a) `N0` has codimension `n` in `Q` (`Φ̄` is onto). A fixed nonzero
vector lies in `M̄` with probability `(2^(l-1)-1)/(2^(d′)-1)`; union bound over
`N0`: `2^(d′-n) · 2^(l-1-d′) = 2^(-s-1)`. (b) Write `Q = N0 ⊕ S` with
`Φ̄|_S` an isomorphism. Every `g ∈ GL(F_2^n)` lifts to `g̃ ∈ GL(Q)` (identity on
`N0`, `(Φ̄|_S)^(-1) g Φ̄|_S` on `S`) with `Φ̄ g̃ = g Φ̄`. `M̄` is uniform, so
`g̃ M̄` has its law, and `gP = Φ̄(g̃ M̄)` has the law of `P`. So
`Pr[p ∈ P]` is the same for all `p != 0`, and equals
`E[|P| - 1]/(2^n - 1) <= (2^(l-1) - 1)/(2^n - 1)`. ∎

**Defect mass.** By (4.1), `N = 1` and `M̄ ∩ N0 = 0` give `dim c(L′) = 1`.
Given `dim c(L′) = 1`, (4.1) gives `N >= 1`, so by Lemma 4 the edge is
accepted with probability `>= 3/4`. Hence the satisfied mass on B-vertices with
one-dimensional `c(L′)` is at least
`(3/4)(Pr[N = 1 | V] - 2^(-s-1)) >= (3/4) Pr[N = 1 | V] - 3 · 2^(-s-1)`,
the second (weaker) form being the one stated in item 3 and used by the
artifact.

## Step 5: one reference covers little of the defect branches (item 3)

Fix a surjective `V`, `s >= 2`, `l >= 3`, and a functional `λ_V : X_V -> F_2`.
Let `E_d := {c(L′) = <(0,d)>}` for nonzero `d ∈ F_2^s`; these events are
disjoint. On `E_d` the B-label is `y_d|_(L′)`, so the covered mass is at most
`Σ_d Pr[E_d, μ_d|_(L′) = 0]` with `μ_d := (λ_V - y_d)|_(X_V)`.

Since `μ_d - μ_(d′) = <d + d′, ζ>|_(X_V)` and `ζ` is onto on `X_V`, at most one
`d`, call it `d_0`, has `μ_(d_0) = 0`. Let `G := {M̄ ∩ N0 = 0}`, so that
`dim P = l-1` on `G`. Then

```text
covered <= Pr[(0,d_0) ∈ P] + Pr[not G] + Σ_(d != d_0) Pr[E_d, G, μ_d|_(L′) = 0].
```

The first two terms are each `< 2^(-s-1)` by Lemma 7. We show that each
remaining summand is at most `2^(3-l) Pr[E_d]`. Summing, that part is at most
`2^(3-l)`, and `covered <= 2^(-s) + 2^(3-l)`. Fix `d != d_0` and
`μ := μ_d != 0`. The events `E_d` and `G` are determined by `M̄`.

**Case (i): `μ|_(H′) != 0`.** By Lemma 2(b), the summand is
`2^(1-l) Pr[E_d, G]`.

**Case (ii): `μ|_(H′) = 0`.** Then `μ` descends to `μ̄ != 0` on `Q`, and
`μ|_(L′) = 0` iff `M̄ <= ker μ̄`.

*(ii-a) `μ̄|_(N0) != 0`.* Fix a section `τ : F_2^n -> Q` of `Φ̄`. The spaces
`M̄` of dimension `l-1` with `M̄ ∩ N0 = 0` and `Φ̄(M̄) = P` are exactly the
graphs `{τ(p) + T(p) : p ∈ P}`, one for each linear `T : P -> N0`, and their
number does not depend on `P`. So given `G` and `P`, `T` is uniform. Now
`μ̄(τ(p) + T(p)) = μ̄τ(p) + (μ̄|_(N0) ∘ T)(p)`, and `μ̄|_(N0) ∘ T` is a uniform
functional on `P`. Since `E_d` is determined by `P`, the summand is
`2^(1-l) Pr[E_d, G]`.

*(ii-b) `μ̄ = ω ∘ Φ̄` for some nonzero `ω ∈ (F_2^n)^*`.* Then
`μ|_(L′) = 0` iff `ω|_P = 0`. On `E_d` we have `(0,d) ∈ P`, so the summand is
`0` unless `ω(0,d) = 0`; assume this. Let `G_d` be the group of
`g ∈ GL(F_2^n)` with `gK = K` and `g(0,d) = (0,d)`. It preserves `E_d` and
`G ∩ E_d` (because `c(gP) = g(P ∩ K)` and `dim gP = dim P`), so by Lemma 7(b)
the law of `P` given `E_d ∩ G` is `G_d`-invariant. For the orbit
`O := {ω ∘ g : g ∈ G_d}`, averaging over `g` uniform in `G_d` gives

```text
Pr[ω|_P = 0 | E_d, G]  =  E[ #{ω′ ∈ O : ω′|_P = 0} | E_d, G ] / |O|.
```

In coordinates `(u, v) ∈ F_2^l x F_2^s`, `G_d` contains every
`g(u,v) = (Au, Bu + Cv)` with `A ∈ GL_l`, `B` arbitrary, `C ∈ GL_s` and
`Cd = d`. Write `ω = (α, κ)`.
* If `κ = 0`, then `α != 0`, and `O` contains all `2^l - 1` functionals
  `(α′, 0)` with `α′ != 0`. Those killing `P` are the nonzero `α′` killing
  `π(P)`, which has dimension `(l-1) - 1 = l-2` on `E_d ∩ G`. So at most `3`
  of them, and the ratio is `<= 3/(2^l - 1) <= 2^(3-l)`.
* If `κ != 0`, then `κ(d) = 0`. `ω ∘ g = (αA + κB, κC)`. As `B` varies,
  `κB` runs over all of `(F_2^l)^*`; as `C` varies over the stabilizer of `d`,
  `κC` runs over all `2^(s-1) - 1` nonzero functionals vanishing at `d`
  (the stabilizer maps onto `GL(F_2^s/<d>)`). So `|O| >= 2^l (2^(s-1) - 1)`.
  The functionals killing `P` form a space of dimension `n - (l-1) = s+1`, so at
  most `2^(s+1) - 1` of them lie in `O`. The ratio is at most
  `(2^(s+1) - 1)/((2^(s-1) - 1) 2^l) <= 7 · 2^(-l) < 2^(3-l)` for `s >= 2`.

In every case the summand is at most `2^(3-l) Pr[E_d]`. This proves item 3. ∎

**This is where every list of `l`-free size dies.** A reference is one
functional per tuple. Up to `2^(3-l)` it matches the label `y_d` of at most one
defect line `d_0`, and every defect line has mass `< 2^(-s-1)`.

## Step 6: summing over tuples, the numbers, and Corollary LS

Assume every tuple is clean for `x` (Step 7). Let `β_bad` be the `G_multi`
mass of tuples on which `Φ` is not onto `X_V`. By Lemma 1 and item 4 of the
decoding node, `β_bad <= δ_sur/(1 - 2^(l-1-k))`. By Lemma 5, replacing the law
of `N` on each good `V` by its limit law costs at most `2^(l-k)`. Put
`o_k := 2^(l-k) + β_bad`. For a list `Λ` of `t` references, the uncovered
satisfied mass is at least the satisfied defect mass minus what each member
covers. By Steps 2 to 5:

```text
val(h)    >=  v(l) - o_k,               v(l) := 1 - E[2^(-1-N_l)],
D(h, Λ)   >=  Ddef(l, s) - t (2^(-s) + 2^(3-l)) - o_k,
Ddef(l,s) :=  (3/4) P(N_l = 1) - 3 · 2^(-s-1).
```

The artifact (Part A) computes these exactly as rationals, which gives the table of
item 4.

**Corollary LS.** Take `s = l >= 8`. For `8 <= l <= 64` the artifact checks
exactly that `v(l) >= 0.6096` and `Ddef(l,l) >= 0.28`. For `l > 64`,
Lemma 6 moves both by less than `2^(-60)` from their values at `l = 64` (`0.6103`, `0.2888`). Take
`k` so large that `o_k < 0.0006`, which is possible because `δ_sur < 2^(2l-k)`
(Step 7). Then, for every `γ <= 0.109`:
* `val(h) >= 0.609 >= 1/2 + γ`;
* for every list with `t < 2^(l-6)`, `t (2^(-l) + 2^(3-l)) < 9/64 < 0.141`, so
  `D(h, Λ) > 0.28 - 0.141 - 0.0006 > 0.0545 >= γ/2`.

The references are arbitrary per-tuple functionals, so in particular this
covers honest encodings of good outer labellings. So (List-Seed) fails for
every list size `t < 2^(l-6)`, and since `l` is free, it fails for every list
size depending only on `γ`. The sharper threshold is
`t_min = (Ddef - γ/2)/(9 · 2^(-l))`, which is about `0.026 · 2^l` as `l -> oo`. ∎

## Step 7: J-instances carry a generic kernel of every rank

Fix `n` and take `N >= k` disjoint copies of `F_2^n \ {0}` as variables. For
each copy and each 2-dimensional subspace `{0, u, u′, u+u′}`, take the
equation `x_u + x_(u′) + x_(u+u′) = 0`. Put `Φ(e_u) := u`, extended linearly and
summed over copies.
* **Regular.** Each point lies on `(2^n - 2)/2 = 2^(n-1) - 1` lines of its copy.
* **Homogeneous.** `Φ(x_e) = u + u′ + (u+u′) = 0`, and `x = 0` satisfies every
  equation, so every tuple is clean.
* **Surjective.** Any two points of one copy lie on a common line. So
  legitimacy (b) forces the `k` blocks of `U` into `k` distinct copies, and a
  uniform legitimate tuple has independent uniform lines in distinct copies.
  Their label lines are therefore i.i.d. uniform lines of `F_2^n`. Smoothing
  keeps a line or picks a uniform point of it, independently. `Φ(X_V)` is the
  span of the labels of the variables of `V`, and it is proper iff all of them
  lie in `ker ψ` for some nonzero `ψ`. For one block, a uniform point of a uniform
  line is uniform on `F_2^n \ {0}`, so it lies in `ker ψ` with probability
  `(2^(n-1) - 1)/(2^n - 1) < 1/2`, and a whole kept line lies in `ker ψ` with
  smaller probability. Hence `δ_sur < (2^n - 1) 2^(-k) < 2^(n-k)`.

With `n = l + s = 2l` this is `δ_sur < 2^(2l-k)`, which needs `2l << k`.
(This is sharper than the `O(k^2/N)` form recorded on the wave-12 branch,
because legitimacy already separates the copies.) ∎

## What the artifact checks

`check_defect_split_mixture.py` runs in well under two minutes and exits 0 iff all
checks pass.
* **Part A.** Lemma 5 exactly, for finite `d′` and in the limit, including
  `P(N=0) = b_l` and the total-variation bound. It also checks `v(l)`,
  `Ddef(l,l)` and `t_min >= 2^(l-6)` exactly for the table rows and for every
  `8 <= l <= 64`, and Lemma 6 at `l = 5, 8, 12`.
* **Part B.** Exact enumeration of the image model on `F_2^(l+s)` for
  `(l,s) = (3,1), (3,2), (4,1), (3,3)`. It checks the growth bound
  `Pr[c(W~) = c(W)] >= 1 - E[2^(-1-N)]` (Lemma 4) and
  `max_d Pr[(0,d) ∈ W] <= 2^(-s)` (Lemma 7(b)).
