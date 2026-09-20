---
rg: 2
id: invariant-norm-ratio-witnesses-localize-hyperlinear
kind: claim
title: For a simple group with an involution, a ratio witness in any unitarily invariant norm localizes to a hyperlinear model, so for Thompson's V every such witness is exactly hyperlinearity
distinct_from:
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that amplifies op, HS and rank ratio witnesses by tensor powers of each word separately and works for any presented group; this uses the joint structure of the words, namely normal generation by an involution, and covers every unitarily invariant norm, including every Schatten p.
  schatten-p-ratio-data-defeat-tensor-replica-amplification: that shows eigenvalue data alone cannot amplify Schatten-p ratio witnesses for p not in {2, infinity}; this shows the data are irrelevant for simple groups with an involution, because the witness localizes instead of amplifying.
  gapped-normal-generators-give-a-hyperlinear-quotient: that reblocks an exact norm-corona homomorphism around spectrally gapped normal generators; this starts from a relative-scale far-mass condition with no norm-corona map, no spectral gap and no lower bound on any defect.
  thompson-v-has-unbounded-compact-unitary-relator-width: that is the width statement, certifiable by any conjugation-invariant length; this shows that certificates by unitarily invariant norm lengths are exactly as strong as thompson-v-hyperlinear.
artifacts:
  - experiments/involution-far-mass-localization-2026-09-17/check_localization.py
  - experiments/involution-far-mass-localization-2026-09-17/output.txt
---

**ESTABLISHED** by `invariant-norm-ratio-witnesses-localize-hyperlinear-proof`.

## Notation

For `x in U(d)` and `delta > 0`, the **far mass** is

```text
F_delta(x) = #{ eigenvalues z of x (with multiplicity) : |z - 1| > delta } / d .
```

A **unitarily invariant norm** on `M_d` is a norm `N` with `N(WXW') = N(X)` for all `W, W' in U(d)`.
The norm may depend on `d` in any way, and it need not be normalized.

## Statement

Let `G = <S | R>` with `S` finite and `R` countable. Let `sigma in F(S)` represent an element of order `2` whose
normal closure is `G`.

**(A) Far-mass criterion.** Suppose there are `d_n` and `U_n in U(d_n)^S` such that

```text
eta_n := #{ eigenvalues z of sigma(U_n) with Re z < 0 } / d_n  >  0,
F_delta(r(U_n)) = o(eta_n)   for every r in R and every fixed delta > 0.            (FM)
```

Then there are subspaces `E_n <= C^(d_n)` and tuples `Uhat_n in U(E_n)^S` such that, in normalized
Hilbert--Schmidt length `l_2` on `U(E_n)`,

```text
l_2(r(Uhat_n)) -> 0  for every r in R,        liminf l_2(sigma(Uhat_n))^2 > 0 .
```

So `G` has a homomorphism into a tracial ultraproduct `prod_omega U(D_n) / {l_2 -> 0}` that does not kill `sigma`.
If `G` is simple, `G` is hyperlinear.

**(B) Ratio witnesses in every unitarily invariant norm.** Let `G` be simple and finitely presented, with an
involution `sigma`, and let `a in F(S)` represent a nontrivial element. Let `N_d` be unitarily invariant norms on
`M_d` and `l(x) = N_d(x - I)`. Suppose there are `U_n in U(d_n)^S` with `a(U_n) != I` and

```text
max_(r in R) l(r(U_n)) / l(a(U_n)) -> 0 .                                          (W)
```

Then (FM) holds for `sigma`, so `G` is hyperlinear.

**(C) Thompson's group V.** `V` is finitely presented, infinite and simple
(`thompson-v-finitely-presented-infinite-simple`). It contains the involution that swaps the leading letter,
`0w <-> 1w`. So a ratio witness for `V` in the length of **any** unitarily invariant norm implies
`thompson-v-hyperlinear`. This covers every Schatten `p`, `1 <= p <= infinity`, normalized or not, Ky Fan norms, and
norms that vary with the dimension.

Conversely, `thompson-v-hyperlinear` gives a ratio witness in every normalized Schatten norm with `p < infinity`. For
unitaries `|z - 1| <= 2`, so `l_p -> 0` iff `l_2 -> 0`, and a lower bound on one gives a lower bound on the other. So
for these norms "ratio witness exists" is equivalent to hyperlinearity of `V`. For the operator norm the converse would
be "hyperlinear implies MF" for `V`, which is not claimed.

## What this kills

- **The Schatten survivor.** `thompson-v-has-unbounded-compact-unitary-relator-width` had Schatten-`p` ratio
  witnesses, `p not in {2, infinity}`, as the last independent metric format.
  `schatten-p-ratio-data-defeat-tensor-replica-amplification` showed that eigenvalue data cannot amplify them.
  Part (B) shows that for `V` they reduce to hyperlinearity anyway. The mechanism is localization, not amplification.
  - The data (S>) and (S<) of that claim are realized by the words of `V` only in models that already produce a
    hyperlinear model of `V`.
- **The width route over these lengths.** Consider `kl-holds-over-thompson-v-via-unbounded-unitary-width` with its width
  prerequisite certified by a unitarily invariant norm length. That route is no easier than `thompson-v-hyperlinear`,
  and for normalized Schatten norms with `p < infinity` it is equivalent to it.
  Hyperlinearity alone already gives Kervaire--Laudenbach over `V`, through `kervaire-laudenbach-holds-for-hyperlinear`.
  So the route adds nothing along these lengths.
- **The invariant.** It is the far mass of the involution, `eta_n`. Two facts do the work:
  - `sigma^2` is a product of relators, which forces the spectrum of `sigma(U_n)` onto `{1, -1}` at every fixed
    resolution, up to `o(eta_n)`.
  - `sigma` normally generates. So every generator has far mass at most `N eta_n` at **every** threshold, with the same
    `N`. A scale-free bound of this kind is exactly what eigenvalue data of a single word cannot see.
- **Where every member dies.** Every such witness dies at Step 4 of the proof, when each generator is replaced by its far
  spectral part on the span `E_n` of the far spectral subspaces. There `dim E_n <= K eta_n d_n`, and the relator far mass
  `o(eta_n d_n)` becomes a vanishing fraction of `dim E_n`.

## What survives for the width node

- Lengths not of the form `N(x - I)` for a unitarily invariant norm, for which (N1) or (N2) of Section 2 of the proof
  can fail. Examples are model-dependent lengths, such as the conjugacy word length of the relator images.
- Non-metric certificates of `Rad_cw(V) = 1`.

## Numerical check

`experiments/involution-far-mass-localization-2026-09-17/check_localization.py` checks the far-mass subadditivity on
random unitaries. It also runs the localization on an `S_1` ratio family for `A_5 = <x, y | x^2, y^3, (xy)^5>`: the
exact permutation representation plus the identity, times spread noise. After localization, the relators have
`l_2^2 < 10^-7` on `E` and `sigma` has `l_2^2 = 2`. On the full space `sigma` has `l_2^2 = 0.04`. The output is in
`output.txt`. The check is not part of the proof.
