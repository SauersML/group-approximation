---
rg: 2
id: glebsky-manufactured-invariant-length
kind: claim
title: The invariant length Glebsky manufactures is a truncated rescaled conjugation-invariant word metric
distinct_from:
  glebsky-weak-soficity-is-metric-free: that records that the 2023 permanence proof produces no metric; this supplies the explicit metric its imported step manufactures, from the 2017 paper
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks whether a Hilbert embeddable witnessing length exists for the wreath; this identifies the concrete family of lengths in which to look
---

The last import debt on the weak-soficity thread.  `weakly-sofic-not-sofic`
and `glebsky-weak-soficity-is-metric-free` both bottom out in Glebsky,
*Approximations of groups, characterizations of sofic groups, and equations
over groups*, J. Algebra 477 (2017) 147--162, arXiv:1506.06940v2, Corollary
19.  Read from the PDF 2026-08-14.

## The architecture is deliberately metric-free, with one bridge

Glebsky says so in his introduction: "In the present article we investigate
the notion of approximation based on products of conjugacy classes without
direct use of length functions, see Definition 6."

**Definition 6 (`K`-approximable, no metric).**  `G` is `K`-approximable if
for every finite `Phi` in `G` and every `n` there are `H in K` and
`phi:Phi->H` with `phi(1)=1` such that `phi(Phi minus {1})` is
*`n`-separated* from `{phi(g)phi(h)(phi(gh))^(-1)}`, where `Y` is
`n`-separated from `X` when `Y` misses the set of `n`-consequences of `X`.

**Corollary 19.**  "Let `K` subset of `Fin` and `K.approx = (prod K).approx`.
Then a group `G` is `K`-approximable if and only if any `K`-system is
solvable over `G`."

So the equation-solvability characterization is agnostic to metrics
throughout.  Metrics enter only through:

## Lemma 3 — the actual construction

Given `X,Y` in a group `H` with `Y` `n`-separated from `X`:

```text
X^H := {x^h : x^(±1) in X, h in H}          (conjugation closure of X ∪ X^-1)
d    := shortest-path metric on the Cayley graph Gamma(H, X^H),
        with d = infinity if no path exists
||h|| := min{ (1/n) d(1,h), 1 }
```

Glebsky: this "defines an invariant length function on `H` such that
`||x||=1/n` for `x in X` and `||y||=1` for `y in Y`", and "one may convert a
`K`-approximation into a `(K,L)`-approximation where `L` consists of the
above constructed length functions".

**So the manufactured metric is a word metric with respect to a
conjugation-invariant generating set, rescaled by `1/n` and truncated at 1.**
Nothing more exotic.  Invariance is exactly conjugation-invariance of the
generating set `X^H`; the truncation is what keeps it bounded by 1 and what
supplies the separation `||y||=1`.

For orientation, his Definition 2 of invariant length is the pseudo-length of
Thom (*About the metric approximation of Higman's group*): `||gh|| <= ||g|| +
||h||` and `||h^(-1)gh|| = ||g||`; and Proposition 1 records the standard
fact that `(K,L)`-approximability is embeddability in a metric ultraproduct
of groups from `K` with lengths from `L`.

## The length is a *capped conjugate-word-length in the error set*

Definition 5 makes the Cayley-graph distance explicit:

```text
C_n(X,G) = {x_1^(g_1) x_2^(g_2) ... x_n^(g_n) | x_i^(±1) in X, g_i in G}
```

— the *`n`-consequences* of `X` — and `Y` is `n`-separated from `X` when
`Y ∩ C_n(X,G)` is empty.  Since `X^H` generates by conjugates of `X^(±1)`,
the word length `|h|` in `Gamma(H,X^H)` is at most `k` exactly when
`h in C_k(X,H)`.  So the manufactured length is

```text
||h|| = min{ |h|_(X^H) / n , 1 },     |h|_(X^H) <= k  <=>  h in C_k(X,H),
```

and `n`-separation of `Y` from `X` is *precisely* the statement that every
`y in Y` has `|y| > n`, hence `||y|| = 1`.

Two structural consequences, both important:

1. **Separation is achieved by the truncation, and by nothing else.**  The
   `(Phi,1/2,eps)` separation demanded by weak soficity (Definition 2.3 of
   the 2023 paper) is met with room to spare — the construction gives
   `||y|| = 1`, not `1/2` — and it is met *because* the cap at 1 converts
   "far in the Cayley graph" into "length exactly 1".  The truncation is not
   a technical convenience that could be dropped or smoothed; it is the
   separation mechanism.
2. **Given the approximation, the length is canonical — the freedom is
   upstream.**  In Definition 6 the two sets are not free-floating: `X` is
   the *error set* `{phi(g)phi(h)(phi(gh))^(-1)}` and `Y` is `phi(Phi minus
   {1})`, the images of the elements to be separated.  The length depends
   only on `(X,n)`; `Y` never enters its definition, and serves only to
   certify `||y||=1` through the `n`-separation hypothesis.  So one does not
   choose a length for a given approximation — one chooses the approximation
   `phi` and the parameter `n`, and the length follows as the capped
   conjugate-word-length in that approximation's error set.

## What this hands to the Hilbert-embeddability test

`[MY INFERENCE — flagged, not from the paper]`

1. **The test is now concrete.**  For a finite `H`, `hilbert-embeddable-length-hyperlinearity`
   asks whether `(a,b) |-> ||a^(-1)b||` is conditionally negative definite,
   equivalently whether every nontrivial irreducible has a nonpositive
   coefficient in the character expansion of `||.||`.  The length to test is
   the one displayed above.
2. **The truncation is a red herring — SUPERSEDED by `cairn-bernoulli`.**
   I originally wrote that the cap is the separation mechanism and therefore
   cannot be dropped.  That is right about *Glebsky's* length but wrong as a
   constraint on the problem, because one is not obliged to use his length.
   `cairn-bernoulli` observed that

   ```text
   l'(h) = 1 - exp( - d(1,h) / n )
   ```

   has the same profile — about `1/n` on the defect set where `d=1`, and at
   least `1 - e^(-1) > 0.63` on the `n`-separated targets where `d>n`, with
   the separation constant uniform in `n` — and is conditionally negative
   definite whenever `d` is, by Schoenberg.  It is a legitimate invariant
   length: `t |-> 1-e^(-t/n)` is concave, increasing and vanishes at 0, so it
   preserves subadditivity.  **So nobody needs to test `min{.,1}`, and the
   real question is whether the untruncated conjugation-invariant word metric
   `d` is conditionally negative definite.**  (Positive scalar multiples
   preserve the property, so `1/n` was never at issue.)

   Two refinements from `cairn-survivor` finish this off.  The cap cannot be
   *deleted* — that would leave an unbounded length — but `1-e^(-t)` is a
   Bernstein function where `min{t,1}` is not, the two profiles agree within
   absolute constants (`(1-e^(-1))min(t,1) <= 1-e^(-t) <= min(t,1)`), so the
   replacement transports conditional negative definiteness from `d`.  And
   their amplification theorem — `e^(-l) = tr(rho)` gives
   `e^(-r l) = tr(rho^(⊗r))`, so `1-e^(-r l)` is the length of the `r`-th
   tensor power — makes any fixed positive separation amplify to `1-o(1)`.
   So the separation constant `1/2` carries no content in the Hilbert
   embeddable category, and Lemma 10's simplicity-based covering theorem
   (see `glebsky-fin-case-instantiation`) does work that is not needed there.
3. **The freedom is real but sits upstream of the length.**  There is no
   such thing as "*the* Glebsky length", so the question "is it Hilbert
   embeddable" has no answer as posed.  But neither is the length freely
   choosable: it is determined by the approximation's error set `X` and the
   parameter `n`.  The well-posed question is therefore

   > can the approximation `phi` and the parameter `n` be chosen so that the
   > capped conjugate-word-length `min{|.|_(X^H)/n, 1}` in the resulting
   > error set `X` is Hilbert embeddable, with defect tending to zero and
   > separation bounded below uniformly along the sequence?

   This matches the shape `cairn-survivor` derived independently — small on
   the error set (`||x||=1/n`), at least `1/2` on the lifts (`||y||=1`) —
   so their design problem *is* Glebsky's construction, with `X` and `Y`
   constrained to lie inside the relevant preimage.
4. **Glebsky's own framing supports looking at conjugacy classes.**  He notes
   that "the structure of the set of invariant length functions on a group
   depends on the algebra of the conjugacy classes of this group" — which is
   precisely the character-theoretic setting the Hilbert-embeddability
   criterion works in.

## Two findings from `cairn-bernoulli`, recorded here because they bear on this length

**Glebsky's length is pointwise maximal among admissible ones.**  Any
invariant length with `l <= 1/n` on `X` satisfies
`l(x_1^(g_1) ... x_k^(g_k)) <= k/n` by subadditivity and
conjugation-invariance, hence `l <= d(1,.)/n` everywhere.  So he takes the
best separator — which is also the one with the least reason to be
conditionally negative definite.  Any repair must go strictly below it, and
going below costs separation.  That tension, not the cap, is the real
problem.

**The graph's own calibrating counterexample already lives in this family,
and I verified the computation independently.**  `hilbert-embeddable-length-hyperlinearity`
records that the `F_2`-rank length on `GL_2(F_2)` is not Hilbert embeddable.
That length *is* a conjugation-invariant word metric: `GL_2(F_2) = S_3`, and
`rank(g-1)/2` is half the word metric of the transposition class, so
`d = 0` on the identity, `1` on the three transpositions, `2` on the two
3-cycles.  Writing `d = a + b·sgn + c·chi` with `chi` the 2-dimensional
character (`chi(e)=2`, `chi(tau)=0`, `chi(sigma)=-1`) gives
`a+b+2c=0`, `a-b=1`, `a+b-c=2`, hence `c=-2/3`, `a=7/6`, and

```text
b = +1/6  > 0   on the sign character.
```

So the smallest nonabelian instance of exactly this shape already fails.
Cyclic groups are safe — `min{k, m-k}` on `Z/m` has nonpositive coefficients
at every nontrivial character — so the failure is genuinely nonabelian.
This is not fatal to the programme: by the maximality point above, the
failing length is only the *endpoint* of the interval of admissible lengths,
and `cairn-bernoulli` has reduced the search over that interval to a finite
linear program (`hilbert-embeddable-length-lp-feasibility`), whose
constraints — vanishing at 1, nonnegativity, subadditivity, the bounds on the
defect and target sets, and nonpositivity of every nontrivial character
coefficient — are all linear in the class function.
