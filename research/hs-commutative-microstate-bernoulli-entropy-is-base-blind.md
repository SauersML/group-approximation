---
rg: 2
id: hs-commutative-microstate-bernoulli-entropy-is-base-blind
kind: claim
title: Hilbert--Schmidt commutative microstate entropy of a Bernoulli shift is infinite along amplified approximations, for every base
artifacts:
  - research/artifacts/stability-approximation-transplant-to-bernoulli-rokhlin-2026-09-17.md
distinct_from:
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is the open lower bound for Bernoulli Rokhlin entropy on every group; this is an established obstruction showing that the unitary (HS) transplant of sofic entropy violates the multinomial upper bound and cannot supply that lower bound.
  coherent-bernoulli-actor-tables-are-cartan-soficity: that says diagonal (Cartan) microstate tables exist exactly when the Bernoulli action is sofic; this concerns the non-diagonal commuting-projection count, which always has room and blows up.
  cartan-algebras-are-strongly-one-bounded: that bounds the quadratic-scale 1-bounded entropy, which quotients by unitary conjugacy, above by zero; this is the unquotiented count at every scale n^beta with beta<2, which is infinite.
  diffuse-pin-centralizer-has-zero-quadratic-covering: that shows the centralizer of a diffuse pin is quadratically thin; this uses the macroscopic commutant U(m) of an amplified model, whose M^2-dimensional volume is what makes the count explode.
  coset-wreath-microstates-carry-excess-entropy: that asks for a quadratic non-conjugate parameter family in wreath microstate spaces conditional on hyperlinearity; this builds an explicit conjugate-by-commutant family for Bernoulli projection microstates along any amplified approximation, unconditionally.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that rules out weak-equivalence invariants as a lower-bound tool; this rules out the Hilbert--Schmidt microstate count, which is not a weak-equivalence invariant.
  borel-structurability-invariants-are-bernoulli-base-blind: that is base-blindness of measure-free Borel invariants; this is base-blindness at value infinity of a measured unitary microstate count.
---

**ESTABLISHED.** Let `G` be countably infinite and `A` finite with `q=|A|>=2`. For
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
suffice. The proof is in `hs-commutative-microstate-amplification-proof`.

## Attempts

* **Quotiented and diagonal species (a-gs-pull-9, 2026-09-17).**
  - Quotienting by the `eta`-approximate commutant with `eta` independent of `delta` gives
    orbital count `1`, so zero entropy for every base, on infinite amenable `G`. The argument
    uses uniqueness up to unitary conjugacy of embeddings of `R` into `R^omega`, which is not
    imported verbatim.
  - Diagonal microstates exist iff the Bernoulli action is sofic
    (`coherent-bernoulli-actor-tables-are-cartan-soficity`).
  - The one surviving species is the tied-tolerance orbital count, `eta(delta) -> 0`. Its
    prerequisites (P1)-(P4) are listed in artifact Section 4.
