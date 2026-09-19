---
rg: 2
id: star-list-structure-is-circular-on-decodable-yes-inputs
kind: claim
title: The per-selector star-list prerequisite (Star-List^C) of Theorem CLV is circular -- on J-instances a polynomial-time flip orientation o* (the defect-line labelling's preferred preimages, flipped on the degenerate half of every flat star) has lift value 0.605 while every lift labelling W of it has val(U_o*, W) <= 1/2 + D^C_L(proj W, Lambda) + E for every list of L <= gamma'^2 2^(k-l-16) arbitrary outer labellings; splicing o* into any constant-bias selector by Gaussian elimination gives a constant-bias selector violating (Star-List^C), so (Star-List^C) for every selector is equivalent to the nonexistence of selectors, which implies P != NP
distinct_from:
  value-free-star-list-references-put-np-in-rp: that proves Theorem CLV (Star-List^C on every YES input implies RP) and leaves (Star-List^C) open; this shows that (Star-List^C), quantified over all constant-bias selectors and all YES inputs of regular Gap3Lin, holds iff no constant-bias selector exists, so it cannot be proved without proving the conclusion (and P != NP).
  dkkms-ev-list-structure-needs-lists-exponential-in-k: that refutes the selector-free list structure for one labelling h of the inner game G; this refutes the per-selector form, for every lift labelling of a constructed orientation (Theorem O), which needs the flip on flat stars and a Q-uniformity bound, and closes the transfer to D^C that the CLV node left unchecked.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this kills the star-list structure route to its constant-bias cell and leaves the hole open.
  list-star-coherent-selector-witnesses-put-np-in-rp: that is Theorem CL with good references; its Star-List prerequisite implies (Star-List^C) (Corollary IMP there), so it is circular in the same way.
artifacts:
  - experiments/ugc-star-splice-2026-09-17/check_star_splice.py
---

**ESTABLISHED** (Theorem O, Proposition S, Corollaries CIRC, PNP, TR and N).
Route: `star-list-structure-is-circular-on-decodable-yes-inputs-proof`.
Nothing here is conditional on a complexity assumption; Corollary PNP is an
unconditional implication.

## What was asked

H1 (`parity-leaking-branch-selectors-reach-near-perfect-completeness`) is open
in its constant-bias cell. Theorem CLV
(`value-free-star-list-references-put-np-in-rp`) reduces that cell, on DKKMS, to
one structure hypothesis on selector witnesses:

> **(Star-List^C)** on every YES input, with probability `>= theta` over the
> coins of the selector `S`, the orientation `o = S(x)` has a lift labelling `W`
> with `val(U_o, W) >= 1/2 + gamma` and a list `Lambda` of at most `L` ARBITRARY
> outer labellings with `D^C_L(proj W, Lambda) <= gamma - gamma'`,

with `L` up to the Corollary DK^C budget `(p gamma'/3)^(1/2) exp(k/(4 exp(ql)))`.
The CLV node records that a transfer of Lemma A of
`dkkms-ev-list-structure-needs-lists-exponential-in-k` would refute
(Star-List^C), and that this transfer "has not been checked". Such a transfer
must be made to hold for lift labellings of the selector's orientation. A
selector-free labelling of `G` is not enough, because in the doubled lift the
free bit `b_q` makes star-wise agreement two-sided. This node does it and
draws the consequence for the whole route.

## Setting

The notation is that of Theorem CLV and of Theorems LS and EL. The doubled lift
`U_o` of an orientation `o` has B-labels `(tau, b)`. A copy `e` with seed
`q = (V, L')`, target `U` and direction `x_e` (`L = L' + <x_e>`) has a
preferred preimage `pref_e(tau)` for every label `tau` of `L'`. It is
lift-satisfied by `(sigma, (tau, b))` iff

```text
sigma_(U,L)|_(L')  =  tau_q     and     sigma_(U,L)  =  pref_e(tau_q) + b_q nu_(L'),
```

where `nu_(L')` is the functional on `L` with kernel `L'`. A **star** is
`(q, U)`. The instance is a J-instance of rank `n = l + s` (LS Step 7), with
the solution `x = 0`, and `Phi = (phi, zeta)` a kernel map. `c(S) = Phi(S) ∩ K`
and `W_U := X_U ∩ phi^(-1)(phi(L'))` are as in LS.

* **Generalised defect labelling `h_G`.** Fix `G` with `G(0) = 0` and
  `G(c) ∈ c \ 0` for `c != 0`. Put `h_G(S) := y_(G(c(S)))|_S` on A- and
  B-vertices, where `y_d = x + <d, zeta(.)>`.
* **Flat star.** A star is flat if `Phi` is onto `X_V`, `c(L') = 0` and
  `M̄ ∩ N0 = 0` (nullity `N = 0`). Then its branch is `a* = x` and `W_U` is a
  hyperplane of `X_U`. On a flat star, `L` is **degenerate** iff
  `x_e ∈ W_U` (equivalently `L <= W_U`).

**The flip orientation `o*`.** For a star with branch `a* := y_(G(c(L')))` and
`tau_h := a*|_(L')`:
* at `tau_h`, if `x_e ∉ W_U`, then `pref_e(tau_h) := a*|_L`;
* at `tau_h`, on a flat star with degenerate `L`,
  `pref_e(tau_h) := x|_L + nu_(L')` (**the flip**);
* at every other `(e, tau)`, `pref_e(tau)` is one of the two preimages,
  chosen so that the star is **balanced**. That is, for every functional
  `lambda` on `X_U`, every `tau` and every `b`, the mass of these free copies
  of the star with `lambda(x_e) = pref_e(tau)(x_e) + b` is within
  `eta := 2^(-k)` of half their mass.

Balanced choices exist once `2^(3k+l+1) exp(-2^(k-l)) < 1` (Hoeffding), and
they are found by resampling per star in time `2^(O(k))`. The same
construction works if the orientation is fixed per multi-edge `(U,L)-(V,L')`
rather than per copy, since degeneracy depends only on `L`.

## Statements

Put `E := eta + 2^(l-1-2k) + 1/(2^l - 1) + SD* + (L+1) 2^(-s-1) + beta_bad`.
Here `SD* = beta sqrt(k) 2^(l+3) + 3 2^(l-k)` is the Q-distance of
`dkkms-near-perfect-labellings-are-outer-honest` (from DKKMS Lemma 4.9), and
`beta_bad` is the `G_multi` mass of tuples on which `Phi` is not onto `X_V`.

**Theorem O (the flip orientation defeats star lists).** Let `Phi` be any
kernel map of rank `n = l + s` (`l >= 3`, `s >= 2`) on a DKKMS instance, and
let `x` be any assignment. Then:
1. If `x` satisfies every equation, then
   `val(U_o*, (h_G, (h_G, 0)))  >=  v(l) - 2^(l-k) - beta_bad`, where
   `v(l) >= 0.6096` for `l >= 8` (Theorem LS). If `x` violates equations, the
   same bound holds with the mass `delta_dirty` of tuples containing a
   violated equation also subtracted.
2. For every lift labelling `W'` of `U_o*` and every list `Lambda` of `L`
   ARBITRARY per-tuple functionals `lambda^j_U`, with no value or consistency
   condition:

```text
val(U_o*, W')  <=  1/2  +  D_L(proj W', Lambda)  +  E
               <=  1/2  +  D^C_L(proj W', Lambda)  +  E .
```

Here `D_L` is the ev-only star mass, `E_star min_j mu(X(H, lambda^j) | star)`,
which is at most `D^C_L` because `X ⊆ X^C`. Item 2 does not use that `x`
satisfies anything.

**Proposition S (the splice).** Let `S` be any randomized polynomial-time
selector. The algorithm `S'` works as follows on an input.
* It splits the variables into the connected components of the equation
  hypergraph.
* Call a component a J-copy if it is a copy of `F_2^n \ 0` carrying one
  equation on every line. Since `n` depends only on `k` and `gamma'`, this is
  recognised in constant time per component.
* Suppose every component is a J-copy and there are `>= k` of them. Then `S'`
  takes `Phi` to be, on each copy, the coordinates of a basis of the linear
  functions on that copy, and takes `x := 0`. It computes `beta_bad`, `o*` and
  `val(U_o*, (h_G, (h_G, 0)))` exactly. If `beta_bad <= 2^(n-k+1)` and the
  value is `>= 1/2 + gamma`, it outputs `o*`.
* Otherwise it outputs `S(x)`.

Then:
* `S'` runs in polynomial time;
* `S'` is a constant-bias selector whenever `S` is, meaning lift value
  `>= 1/2 + gamma` with probability `>= theta` on every YES input;
* on every J-instance of rank `n`, noisy or not (Corollary N), with `N >= k`
  copies, `S'` outputs `o*` deterministically, for every `gamma <= 0.105`
  (at large `k`).

**Corollary CIRC (the route is circular).** Fix `l >= 8` and
`2^(2-l) <= gamma' < gamma <= 0.105`, and let `L <= gamma'^2 2^(k-l-16)`. Take
`n = k - c`, with `c = ceil(log2(1/gamma')) + 12`. Then for all large `k`:

```text
(Star-List^C) holds for every constant-bias selector
    <=>  no constant-bias selector exists.
```

Direction `<=` is vacuous. For `=>`, let `S` be a constant-bias selector. On
J-instances, `S'` outputs `o*`, which has a lift labelling of value
`>= 0.605 >= 1/2 + gamma`. Every `W'` with value `>= 1/2 + gamma` has
`D^C_L >= gamma - E > gamma - gamma'`.

The range of `L` is `2^(k - O(l))`. That exceeds the Corollary DK^C budget
`exp(k/(4 exp(ql)))` for every `q >= 0`. So Theorem CLV plus (Star-List^C)
proves exactly "no selector exists", and the prerequisite already is that
statement.

**Corollary PNP.** If P = NP, a constant-bias selector exists. It finds a
labelling `H` of `G(x)` with `val_G(H) >= 1/2 + gamma` by self-reduction, and
orients each constraint by `pref_e := H`'s A-label. So "(Star-List^C) for
every selector" implies P != NP. It cannot be proved by any argument that does
not prove P != NP.

**Corollary TR (the unchecked transfer, selector-free form).** For every
labelling `H` of `G` and every list, `D^C_L(H, Lambda) >= D_L(H, Lambda)`,
where `D_L` takes the best index per star, `i(U,V,L')`. So Corollary EL gives
the following on rank-`(k-8)` J-instances: the LS labelling `h` has
`D^C_L > 0.110` for every list of `L < 2^(k-l-11)` arbitrary outer labellings.
Hence the selector-free (Star-List^C) fails for `gamma <= 0.105`. This settles
the transfer that the CLV node left unchecked. Theorem O is the
per-orientation form: it covers every lift labelling of `o*`, not only `h`.

**Corollary N (value < 1 does not help).** Take a noisy J-instance: a
J-instance in which at most one line equation per copy has right-hand side `1`.
Such an instance has value `< 1` once one line is flipped (for `n >= 3`), and
it is a YES input of Gap3Lin(`1 - eps`, ...) for
`eps >= 3/((2^n - 1)(2^(n-1) - 1))`. The zero assignment violates only the
flipped lines, and
`delta_dirty <= 3k/((2^n - 1)(2^(n-1) - 1)) <= 2^(n-k)` at large `k`. So
Theorem O holds with the same `E`, and item 1 loses at most `2^(n-k)`.
Corollary CIRC therefore survives restricting (Star-List^C) to YES inputs of
value `< 1`.

## Why the flip is needed

Without the flip, the obvious orientation is `pref = a*|_L` off `W_U` and
random on `W_U`. On a flat star the honest labelling `x` with `b = 0` then
satisfies all of the non-degenerate half and about half of the degenerate half,
which is `3/4` of the star. Flat stars carry mass about
`P(N_l = 0) = b_l ≈ 0.58`, and elsewhere `x` gets about half. So the lift
labelling `(x, (x, 0))` has value about `0.58 · 3/4 + 0.42 / 2 ≈ 0.64`, with
`D^C = 0` against the one-element list `{x}`. The naive orientation therefore
has a witness that passes (Star-List^C), and it refutes nothing. The flip puts the
degenerate half of a flat star at `b = 1` and the non-degenerate half at
`b = 0`. The single bit `b_q` can then serve only one half. Any A-label other
than `x|_L` passes only when its kernel is exactly `L'`, and that is a
cross-star event of mass `<= 1/(2^l - 1) + SD*`, by Q-uniformity of `L'` given
`L`. The artifact (Part B) shows the gap exactly on toy stars: honest `x` gets
`0.667` under the flip against `0.847` under the random orientation.

## What this kills (impact types 3 and 1)

**Class killed.** The class is every closure of the constant-bias cell of H1
through a star-list structure hypothesis in ev-form or consistency-charged
form (Star-List, Star-List^C, List-Str_t, or any hypothesis implying them),
where the hypothesis is:
* quantified over all constant-bias selectors, or over the witnesses of one
  given selector on all YES inputs of regular Gap3Lin;
* stated with `L <= gamma'^2 2^(k-l-16)` references;
* for `gamma <= 0.105` and `gamma' >= 2^(2-l)`.

The decoder does not matter, since Theorem O is about the hypothesis itself.
This includes the remaining prerequisite of Theorem CLV, need `(Star-List^C)`
posted by swarm-0917-w15-w15-ugc-last1. It also includes the Star-List
prerequisite of Theorem CL, through Corollary IMP there.

**Invariant.** Perfectly or near-perfectly satisfiable YES inputs of large
kernel rank are decodable in polynomial time. That makes a quantifier over
"every selector" range over selectors that know the solution. The flip
orientation `o*` is built from the solution. It has value `0.605`, and its
lift value above one half is bought only by the `2^(s)` defect branches.
No short list covers them (one branch per reference, mass `< 2^(-s-1)` each),
and no single bit covers the flat stars.

**Where every member dies.** It dies at the step "every constant-bias
selector's witness admits a short list". For the spliced selector `S'` this
step is false. So the step is equivalent to the nonexistence of selectors,
which is the goal itself. By Corollary PNP it is also at least as strong as
P != NP.

## What survives

* **Structure hypotheses that exclude decodable inputs.** These are
  hypotheses stated only for YES inputs whose kernel rank is
  `< k - 2l - O(log(1/gamma'))`, or only for sources, such as PCP images with
  spanning equation vectors, on which no polynomial-time algorithm is known to
  find a near-solution. The decoder of Theorem CLV must still work on every
  YES input. It may, however, treat decodable inputs separately, since those
  are accepted directly (Gaussian elimination, or the J-copy test of
  Proposition S). So a route that proves (Star-List^C) only on non-decodable
  YES inputs, and runs CLV only there, is not killed here. That escape needs a
  definition of "non-decodable" that the decoder can test, and that is its
  first prerequisite.
* **`gamma > 0.105`.** The value of `o*` is about `0.61`.
* **`gamma' < 2^(2-l)`.** Here `E >= 1/(2^l - 1)`. The `T2` term (A-labels
  with kernel exactly `L'`) is the one place where Theorem O is not sharp.
* **Hypotheses using the selector's behaviour off one input**, such as
  consistency of `S` across inputs, or witnesses on NO inputs. These are not
  star-list statements about one orientation.

## Belief change

The CLV node ended with "(Star-List^C) OPEN, likely false at small gamma via
Lemma A (transfer unchecked)". Both parts are now settled, and the answer is
stronger than "false". In the per-selector form that CLV needs, (Star-List^C)
cannot be a lemma at all. For any selector it fails for a polynomial-time
modification of that selector. So the star-list family of routes to the
constant-bias cell is closed, on the whole YES set of regular Gap3Lin, without
reference to any decoder loss.

## Attempts

* **Splice plus flip orientation (2026-09-19, swarm-0917-w15-w15-ugc-follow).**
  Family quantifier-shift.
  * Tried first: the affine orientation `x + psi_W + 1`. It fails, because the
    free bit `b_q` absorbs constants. Tried second: random bits on `W_U`. It
    fails, because honest `x` gets `3/4` of the flat stars with `D^C = 0`.
  * The flip plus Q-uniformity works. It proves Theorem O, and Proposition S
    turns it into Corollary CIRC.
  * The artifact checks, all PASS:
    * the flat-star case lemma, exhaustively for `m <= 5`;
    * the exact flip-toy optimum against its bound, and the naive gap;
    * one-branch covering, and exactly-half agreement off the covered set, in
      the image model;
    * the parameter table for `8 <= l <= 20`.
