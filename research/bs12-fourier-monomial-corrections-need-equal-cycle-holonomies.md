---
rg: 2
id: bs12-fourier-monomial-corrections-need-equal-cycle-holonomies
kind: claim
title: An exact BS(1,2) pair that is monomial in the Fourier basis has conjugator holonomy equal to its mean on every doubling cycle, so no reweighting of base or conjugator brings the Bessel-twisted pair within s of an exact pair, uniformly in N
artifacts:
  - experiments/bs12-weighted-shift-2026-09-17/fourier_monomial_obstruction.py
  - experiments/bs12-weighted-shift-2026-09-17/run_output.txt
distinct_from:
  bs12-separated-doubling-spectra-correct-conjugators-unpadded: that bounds corrections keeping the base D fixed and letting the conjugator be arbitrary; this lets both the base and the conjugator move inside the Fourier-monomial class and proves the conjugator cost is unchanged, with the base weights invisible to the invariant.
  bs12-trivially-padded-opnorm-correction: that is the open uniform statement (ESS Question 3 for BS(1,2)); this kills one class of corrections of its sharp test family and does not decide it.
  bs12-conjugator-correction-is-power-uniform-defect: that measures fixed-base correction by the power-uniform defect; here the base moves and the obstruction is a determinant-normalized holonomy, not a power defect.
---

**ESTABLISHED** by `bs12-fourier-monomial-holonomy-rigidity-proof`
(elementary; not Lean-verified).  This is
the nonlinear, exact form of the first-order Livsic functional `Phi` recorded
in the Attempts of `bs12-trivially-padded-opnorm-correction`.  It kills a
class of corrections of the test family `(A_s, D)`.

## Setting

`N` is odd, `w = e^(2 pi i/N)`, `h = (N+1)/2`.  On `C^N`, `D e_j = w^j e_j`,
`V e_j = e_(j+1)`, `W e_j = e_(hj)`, and `A_s = W exp(is(V+V^*))`.  In the
Fourier basis `f_m = N^(-1/2) sum_j w^(-jm) e_j`,

```text
V f_m = w^m f_m,   D f_m = f_(m-1),   A_s f_m = e^(i g_m) f_(2m),
g_m = 2 s cos(2 pi m/N).
```

The relator defect is `||A_s D A_s^* - D^2|| <= 4 pi s/N`.  A *doubling
cycle* is an orbit `gamma` of `m -> 2m` on `Z/N`.  For example, `{0}` is a
doubling cycle, and so is `{N/3, 2N/3}` when `3 | N`.

**Class F (Fourier-monomial pairs).**  These are the pairs of the form

```text
C f_m = e^(i a_m) f_(2m),      Z f_m = e^(i t_m) f_(m-1),      a, t in R^N.
```

Equivalently, `C = W e^(i a(V))` and `Z = D e^(i t(V))`.  If `C` and `Z` are
unitaries that are monomial in the basis `(f_m)`, with `||C - A_s|| < sqrt 2`
and `||Z - D|| < sqrt 2`, then the pair is in class F.  The reason is that a
monomial column placed off the positions `2m` (or `m-1`) is at distance
`sqrt 2` from `A_s f_m` (or `D f_m`).

## Theorem

1. **Holonomy rigidity.**  Let `(C, Z)` be in class F with `C Z C^* = Z^2`,
   and let `a` be a real lift with `|a_(m-1) - a_m| + 3 max|t| < 2 pi` for all
   `m`, where the lift of `t` takes values in `(-pi, pi]`.  Then for every
   doubling cycle `gamma`,

   ```text
   (1/|gamma|) sum_(m in gamma) a_m  =  (1/N) sum_m a_m ,        sum_m t_m = 0.   (HR)
   ```

   In operator terms, the monodromy `C^|gamma|` on `span{f_m : m in gamma}`
   is `det(W^* C)^(|gamma|/N)`, taken with the lifted phases.  The base
   weights `t` do not enter, and `Z` has exactly the spectrum of `D`.
2. **Uniform class-F distance.**  Let `s <= pi` and `N > 4s`.  Suppose
   `(C, Z)` is an exact pair in class F with `||C - A_s|| <= eps` and
   `||Z - D|| <= eps`, where `eps <= 1/2`.  Then

   ```text
   eps >= 2 sin( (1/2) * max_(gamma, gamma') |avg_gamma g - avg_gamma' g| / 2 )
       >= 2 sin(s/2).
   ```

   If `3 | N`, the middle quantity is at least `2 sin(3s/4)`.  So every
   Fourier-monomial exact pair is at distance at least `min(1/2, 2 sin(s/2))`
   from `(A_s, D)`, uniformly in `N`, while the relator defect tends to `0`.
   The trivial correction `(W, D)` is at distance at most `2 sin s`.
3. **General weights.**  Item 2 holds for every pair `(W e^(i g(V)), D)`
   with `g` real on `Z/N`, `|g_(m-1) - g_m| <= 1`, and `eps <= 1/2`.  In that
   case the class-F distance is at least `2 sin(osc_gamma(avg_gamma g)/4)`.
   Here `osc_gamma` is the spread of the cycle averages of `g`.  The bound
   is vacuous exactly when all doubling-cycle averages of `g` agree, which
   is the discrete Livsic condition.  The converse, that the class-F
   distance is then small, is not proved.

## Proof

Proof route: `bs12-fourier-monomial-holonomy-rigidity-proof`
(five elementary steps: cocycle equation over `R`, the Bernoulli cokernel
identity (B), cycle averaging of translates, pairing, distances).

## Evidence (numerical, not part of the proof)

`fourier_monomial_obstruction.py` (output in `run_output.txt`) checks three
identities:

- the setting identities at `N = 27`, `s = 0.3`, with error `5e-15` and
  relator defect `0.139`;
- (B) in exact rationals for all odd `N < 400`;
- (HR) on 50 random exact class-F pairs at `N = 45`, with error `1e-15`.
  The same check on every cycle for `N = 25, 27, 35, 45, 63` also gives
  error `1e-15`.

It also solves the linear program

```text
min max(|b|_inf, |t|_inf)   subject to   T t = grad(g + b).
```

This is the exact class-F distance in angle sup-norm, in the lift regime.

- For `3 | N`, at `N = 27, 81, 243, 729` and `s = 0.05, 0.1, 0.3`, the
  optimum is `1.5000 s` every time.  So the bound `beta = 3s/2` is attained,
  and base weights `t` can always be found once `b` meets (HR).
- For `N = 25, 35, 125`, the optimum is `1.25 s`.  That is the spread of
  the fixed point against the cycle `{N/5, ...}`, whose average is `-s/2`.

The class-F distance therefore does not decay with `N`.

## What this kills

**Class.**  This kills every correction of `(A_s, D)` that reweights the
doubling and the shift in the Fourier basis.  The weights may be
arbitrary: discontinuous, `N`-dependent, and applied to base and conjugator
together.  The class includes:

- all gauge transforms by unitaries diagonal in `(f_m)`;
- the first-order Livsic gauge of the recorded Attempts;
- the weighted-shift ansatz for the base.

**Invariant.**  The doubling-cycle holonomies of the conjugator,
normalized by `det(W^* C)^(1/N)`.  They are read by the translated
Bernoulli vectors `y^gamma`, which lie in the cokernel of the base cocycle
operator `T`.

**Step where it dies.**  Every member reaches the exact cocycle equation
`T t = grad a` over `R`.  There, the pairing with `y^gamma` removes `t`
entirely and forces `avg_gamma a = mean a`.  For `g = 2s cos`, this costs
`beta >= s` (at least `3s/2` when `3 | N`).

**Consequence for `(TPC)` and ESS Question 3.**  Moving the base does not
help as long as `Z` stays monomial in the Fourier basis.  The spectrum of
`Z` is then frozen at that of `D` (step 1), and the base weights are
invisible.  A correction of `(A_s, D)` within `o(s)` must make `Z`
non-monomial in `(f_m)`, and must also move `C` off the weighted-doubling
form.  Fixed-base corrections, which are arbitrary in `C`, also cost about
`s/2` by `bs12-separated-doubling-spectra-correct-conjugators-unpadded`.
So both coordinate-adapted classes are dead with cost `Theta(s)`, uniformly
in `N`.

## What this does not do

It does not decide whether `(A_s, D)` is uniformly far from all exact pairs,
so ESS Question 3 stays open.  The next test is the class of exact pairs
with `Z` unitarily equivalent to `D` by a unitary that is not monomial in
either basis.  For those, `C` is conjugate to a weighted `W` in the
`D`-eigenbasis, and the invariant here has no evident analogue.
