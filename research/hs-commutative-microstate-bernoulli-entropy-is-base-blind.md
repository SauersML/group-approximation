---
rg: 2
id: hs-commutative-microstate-bernoulli-entropy-is-base-blind
kind: claim
title: Hilbert--Schmidt commutative microstate entropy of a Bernoulli shift is infinite along amplified approximations, for every base
artifacts:
  - research/artifacts/stability-approximation-transplant-to-bernoulli-rokhlin-2026-09-17.md
  - research/artifacts/hs-commutative-microstate-bernoulli-entropy-is-base-blind-proof-attempt-2026-09-17.md
distinct_from:
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is the open lower bound for Bernoulli Rokhlin entropy on every group; this is an established obstruction showing that the unitary (HS) transplant of sofic entropy violates the multinomial upper bound and cannot supply that lower bound.
  coherent-bernoulli-actor-tables-are-cartan-soficity: that says diagonal (Cartan) microstate tables exist exactly when the Bernoulli action is sofic; this concerns the non-diagonal commuting-projection count, which always has room and blows up.
  cartan-algebras-are-strongly-one-bounded: that bounds the quadratic-scale 1-bounded entropy, which quotients by unitary conjugacy, above by zero; this is the unquotiented count at every scale n^beta with beta<2, which is infinite.
  diffuse-pin-centralizer-has-zero-quadratic-covering: that shows the centralizer of a diffuse pin is quadratically thin; this uses the macroscopic commutant U(m) of an amplified model, whose M^2-dimensional volume is what makes the count explode.
  coset-wreath-microstates-carry-excess-entropy: that asks for a quadratic non-conjugate parameter family in wreath microstate spaces conditional on hyperlinearity; this builds an explicit conjugate-by-commutant family for Bernoulli projection microstates along any amplified approximation, unconditionally.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that rules out weak-equivalence invariants as a lower-bound tool; this rules out the Hilbert--Schmidt microstate count, which is not a weak-equivalence invariant.
  borel-structurability-invariants-are-bernoulli-base-blind: that is base-blindness of measure-free Borel invariants; this is base-blindness at value infinity of a measured unitary microstate count.
---

**OPEN (referee lens 1 refuted Step 3 of the direct proof on 2026-09-17; see `## Attempts`).** Let `G` be countably infinite and `A` finite with `q=|A|>=2`. For
`sigma: G -> U(n)` let `Mic(sigma,F,delta)` be the set of `A`-tuples of projections
`(p_a)` with `sum_a p_a = 1`, such that:

- the translates `sigma(g)p_a sigma(g)^*`, `g in F`, pairwise commute, and
- every `F`-pattern moment `tr_n(prod_(g in F) sigma(g)p_(w(g))sigma(g)^*)` is within
  `delta` of `q^(-|F|)`.

The count uses `rho(p,p') = max_a ||p_a-p'_a||_2` (normalized HS) and

```text
h^beta_Sigma(A) = sup_eps inf_(F,delta) limsup_j n_j^(-beta) log N_eps(Mic(sigma_j,F,delta), rho).
```

Take any `Sigma=(sigma_j: G -> U(d_j))` along which `Mic(sigma_j,F,delta)` is eventually
nonempty for every `(F,delta)`. Take `beta in [1,2)` and even `m_j` with
`m_j^(2-beta)/d_j^beta -> infinity`. Then

```text
h^beta_(Sigma (x) 1_m)(A) = +infinity    for every finite A with |A|>=2.        (HSB1)
```

More precisely, for all `eps < 1/(2000q)`, all `(F,delta)` with `delta<1/(2q)`, and all large `j`:

```text
N_eps(Mic(sigma_j (x) 1_(m_j),F,delta), rho) >= (1/2)(16/e)^((m_j/2)^2).          (HSB2)
```

The same holds for every relaxation of `Mic` (approximate commutation, longer windows),
and for any microstate space defined by joint `*`-moment conditions on `(sigma,p)`.

If `Sigma` consists of permutation matrices, so does `Sigma (x) 1_m`. Hence `(HSB1)` holds
along sofic approximations of `Z`, where `h^Rok(A^Z) = log q`. The transplanted count
therefore violates the multinomial bound `h_Sigma <= H(P)` for a generating partition `P`,
which is the step every sofic-entropy lower bound for Rokhlin entropy passes through. This
kills, as a route to `bernoulli-rokhlin-entropy-maximal-for-every-group`, every
unquotiented Hilbert--Schmidt commutative-microstate count along unitary approximations
with macroscopic exact commutant.

The invariant responsible is the volume of the commutant of `sigma(G)`: `U(m)` for
`sigma (x) 1_m`. Commuting (diagonal) rotations give only `O(m)` parameters and do not
suffice. A candidate proof, held OPEN, is in
`research/artifacts/hs-commutative-microstate-bernoulli-entropy-is-base-blind-proof-attempt-2026-09-17.md`.

## Attempts

* **2026-09-17: direct proof by commutant rotation and packing (route
  `hs-commutative-microstate-amplification-proof`, requires: []), held OPEN.** The route was withdrawn to
  `research/artifacts/hs-commutative-microstate-bernoulli-entropy-is-base-blind-proof-attempt-2026-09-17.md`.
  - **Referee lens 1: refuted.** Verbatim: "First step that does not follow: Step 3 of hs-commutative-microstate-amplification-proof (Step 3 of Theorem K1 in the artifact), the sentence "The F={e} moments give s^2 >= 2/q-2delta >= 1/q". The pair a0 != a1 is fixed arbitrarily in Step 1, and (F,delta) is any window with delta<1/(2q). The single-letter moment tau(p_a) is a moment condition only when F={e}. For |F|>=2 you can only get it by summing q^(|F|-1) pattern moments, which gives |tau(p_a)-1/q| < q^(|F|-1)delta. That is not delta, and it can be vacuous. The inequality is actually false. Counterexample: q=10, F={e,g}, delta=0.049<1/(2q). Take p supported uniformly and roughly independently on 8 letters, with p_(a0)=p_(a1)=0, which is available along sofic approximations of Z. Every 2-pattern moment is either 0 or about 1/64, both within 0.049 of 1/100, so p is in Mic. But s^2=tau(p0+p1)=0. Then the separation (s/2)(r/48)=s^2/960 in Steps 4-6 is 0, and the (HSB2) count gives nothing. The claim can be repaired: choose a0,a1 as the two heaviest letters, so s^2>=2/q. But the step as written does not hold. Other gaps: (i) the statement says (HSB1) holds 'for any microstate space defined by joint *-moment conditions on (sigma,p)', but Step 7 only shows this for spaces that are closed under block averaging, invariant under the swap pi, and invariant under commutant conjugation. Non-convex or non-uniform moment conditions fail the first two. (ii) Step 7 uses h^Rok(A^Z)=log q (Rokhlin/Kolmogorov) and nonemptiness of Mic along sofic approximations of Z with no verbatim citation. It also asserts without support that 'every sofic lower bound passes through h<=H(P)'. The route has requires: [] and no experiment script. Steps 2, 4 (the telescoping bound 2(e^(2r)-1)), 5 (net, Ginibre small-ball and packing) and the scaling in 6 check out."
  - **Referee lens 2: survives**, with caveats that Step 3 needs `e in F` or a heaviest-letter swap, that the
    result covers uniform bases only, and that "any joint `*`-moment conditions" is justified only for conditions
    stable under block averaging and letter swaps.
  - **Fix.** In Step 1 swap the two heaviest letters, so `s^2 >= 2/q`, and adjust the constants in Step 6. Restrict
    the "any moment conditions" sentence to conditions preserved by block averaging, the swap and commutant
    conjugation. Cite `h^Rok(A^Z)=log q` and nonemptiness of `Mic` along sofic approximations of `Z` verbatim.

* **Quotiented and diagonal species (a-gs-pull-9, 2026-09-17).**
  - Quotienting by the `eta`-approximate commutant with `eta` independent of `delta` gives
    orbital count `1`, so zero entropy for every base, on infinite amenable `G`. The argument
    uses uniqueness up to unitary conjugacy of embeddings of `R` into `R^omega`, which is not
    imported verbatim.
  - Diagonal microstates exist iff the Bernoulli action is sofic
    (`coherent-bernoulli-actor-tables-are-cartan-soficity`).
  - The one surviving species is the tied-tolerance orbital count, `eta(delta) -> 0`. Its
    prerequisites (P1)-(P4) are listed in artifact Section 4.
