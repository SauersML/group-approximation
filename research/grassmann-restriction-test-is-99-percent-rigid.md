---
rg: 2
id: grassmann-restriction-test-is-99-percent-rigid
kind: claim
title: Every labelling of the linear Grassmann restriction test over F_2 that passes with probability 1 - eta agrees with a single global linear functional on all but 800 eta of the l-spaces, with a constant independent of l and of the ambient dimension
distinct_from:
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is the 99 percent statement for the folded, smoothed, multi-edge DKKMS game, whose seeds live in the subspaces X_V of smoothed tuples and whose conclusion is a locally honest patchwork of an outer labelling; this is the statement for the plain Grassmann restriction test on one ambient space, with a single global linear functional and an absolute constant, and it is the analytic engine that statement is missing.
  two-to-two-games-theorem: that is the 1 percent soundness theorem of Khot--Minzer--Safra, which needs the Grassmann expansion machinery and decodes to a list through zoom-ins and zoom-outs; this is a 99 percent statement whose whole proof is six applications of the test plus BLR plus the ordinary spectral gap of the Grassmann graph, and whose conclusion is a single functional, not a list.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that builds one gauge labelling of the branch-blind coarsening and is a completeness statement about a quotient; this bounds every near-perfect labelling of the test itself and reads the branch coordinate the coarsening discards.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that is about verifiers whose views are affine in the outer label; this is about arbitrary labellings of one fixed agreement test and uses no verifier at all.
  view-local-branch-selectors-are-gauge-blind: that bounds the honest lift value of selectors with parity-faithful views by a gauge-uniformity argument on the 3LIN source; this says nothing about selectors or gauges and is a structure theorem for labellings of the inner Grassmann layer.
  dkkms-smoothing-leaves-the-branch-coordinate-untested: that is the negative transfer statement, measuring how far the DKKMS edge law is from this test and naming the weight (1 - 3 beta / 4)^k the transfer would have to pay; this is the positive theorem for the test itself, with no smoothing and no folding.
artifacts:
  - experiments/grassmann-99-rigidity-2026-09-18/check_grassmann_99_rigidity.py
  - research/artifacts/grassmann-restriction-99-percent-rigidity-proof-2026-09-18.md
---

**OPEN** (claimed 2026-09-18 via a direct-proof route, returned to OPEN at
landing because the wave's three-lens referee stage returned a refutation
against this lane — lens 2 refuted the companion node
`dkkms-smoothing-leaves-the-branch-coordinate-untested`, so the lane lands
demoted as a whole. **No referee found an error in Theorem R**: all three
lenses walked the proof step by step and reported that it holds, and lens 2
wrote "What holds: Theorem R itself survives the check." The proof is kept as
the attempt artifact
`research/artifacts/grassmann-restriction-99-percent-rigidity-proof-2026-09-18.md`;
see `## Attempts`.)

## The test

Let `X = F_2^D` and let `2 <= l <= D - 2`. Write `Gr(X, d)` for the set of
`d`-dimensional subspaces and `L^*` for the `2^d` linear functionals on
`L in Gr(X,d)`. A **labelling** is a pair

```text
sigma : Gr(X, l)   -> labels,   sigma_L in L^*,
tau   : Gr(X, l-1) -> labels,   tau_Q  in Q^*.
```

The **restriction test** `T` draws a uniform *flag* `Q < L`, meaning a uniform
`Q in Gr(X, l-1)` followed by a uniform `L in Gr(X,l)` with `L > Q` (this is the
same distribution as a uniform `L` followed by a uniform hyperplane `Q` of `L`),
and accepts iff `sigma_L|_Q = tau_Q`. This is the inner layer of every Grassmann
2-to-1 game: an A-label is a functional on an `l`-space, a B-label is a
functional on a hyperplane of it, and the constraint is restriction.

## Statement

**Theorem R.** Suppose `Pr[T accepts] >= 1 - eta` with

```text
eta <= 1/2000        and        2^(l - D) <= eta.
```

Then there is a single `A in X^*` with

```text
Pr_(L in Gr(X,l)) [ sigma_L = A|_L ]      >= 1 - 800 eta,
Pr_(Q in Gr(X,l-1)) [ tau_Q  = A|_Q ]     >= 1 - 801 eta.
```

The constant `800` is absolute: it does not depend on `l`, on `D`, or on the
labelling.

**Corollary R1 (seed prediction functions are linear).** For
`Q in Gr(X, l-1)` define the **prediction function**

```text
F_Q : X \ Q -> F_2,      F_Q(x) := sigma_(Q + <x>) (x),
```

the value that the A-label of the unique `l`-space through `Q` and `x` gives to
the new direction `x`. This is the quantity a branch selector's bit function is
*predicting*, not the value it returns: the annotation item of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` defines
`g_e(sigma') := A_(o_e(sigma'))(U,L)(x_e)`, the value of an orientation-chosen
preimage, and item (5) of `orientation-lifts-sandwich-2to1-game-values` writes
the branch as `o_e(sigma) = sigma(x_e) xor g_e(sigma|_(L'))`. (Correction made
2026-09-18 after referee lens 2 flagged the original wording.) Then

```text
E_Q Pr_(x,y in X) [ F_Q(x+y) != F_Q(x) + F_Q(y) ]   <=   7.5 eta       (defect)
E_Q Pr_(x in X)   [ F_Q(x)   != A(x) ]              <=   400 eta       (one A)
```

with the **same** `A` as in Theorem R. So on this test the branch predictor at a
typical seed is an approximate homomorphism with defect `O(eta)` and is
`O(eta)`-close to one global linear function, the same one for almost every
seed.

## Why the constant is uniform in `l`

The only global input is the spectral gap of the down-up walk `W` on
`Gr(X, l-1)`: pick a uniform hyperplane `P < Q`, then a uniform `Q~ > P`. Its
non-trivial eigenvalues satisfy `|lambda| <= 1/2`, uniformly in `l` and `D`
(Grassmann scheme; see the attempt artifact for the two-line inequality on the closed
formula). Every other step of the proof is a union bound over six uses of the
test, and each of the six is an *exactly* uniform flag because the gadget maps
are `GL(X)`-equivariant and `GL(X)` is transitive on flags. Nothing in the
argument pays a `2^l`, which is the loss the note "Evidence against" of
`dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` feared from zoom
structures. Zoom-outs are not counterexamples: an `A'` used on the `l`-spaces
inside a fixed hyperplane `W < X` occupies `~2^(-l)` of `Gr(X,l)` and already
makes the test reject `~2^(-l)` of the time, so `dist ~ eta` there as well. The
artifact measures exactly this: the worst ratio `dist / eta` over honest, noisy,
zoom-in, zoom-out, mixed and uniform labellings at four sizes is `3.0`.

## What it does and does not give for the selector hole

The residual survivor left by `high-advantage-selector-witnesses-decode-good-outer-labellings`
is (H2-loc): a YES lift witness whose class labels on the `l`-spaces of a
constant fraction of `k`-tuples are **not** restrictions of one functional.
Theorem R says that on the plain Grassmann restriction test this survivor is
empty: value `1 - eta` forces one functional on all but `800 eta` of the
`l`-spaces, with no `2^l` anywhere.

**This gadget does not transfer to the DKKMS game, and that is all that is
recorded.** The three auxiliary seeds `P + <x>`, `P + <y>`, `P + <x+y>` sit at
the `l`-space `N = P + <x,y> != L` and must lie inside the space `X_(V'')` of a
smoothed tuple; a fresh smoothing contains a uniform direction with probability
exactly `(1 - 3 beta / 4)^k`, so *this* gadget transfers only with `eta`
replaced by `eta (1 - 3 beta / 4)^(-k)`, vacuous at the DKKMS parameter point.
The stronger reading — that *every* Grassmann agreement theorem must pay that
factor — was written into
`dkkms-smoothing-leaves-the-branch-coordinate-untested` and **refuted** by
referee lens 2 on 2026-09-18: at a fixed A-vertex `(U,L)` two distinct
hyperplane seeds span `L` and pin the A-label at every direction with neither
seed containing it, so an agreement argument free to use two queries at one
A-vertex pays `O(1)`, not `exp(Theta(beta k))`. So it is **not** recorded here
that the rigidity of the DKKMS test has to come from the folding classes; only
that the six-flag route to it is blocked.

Lemma F of the attempt artifact settles the other half of a hypothetical transfer
for free:
if the class labels of a window `U` do glue to a single linear `alpha` on `X_U`,
then `alpha|_(H_U) = h_U` automatically, so `alpha` satisfies the equations of
`U` and is a legal A-label of the outer game `Phi_k`. Folding does not have to
be paid for on that side.

This neither proves nor refutes UGC, the Rich 2-to-1 Games Conjecture, or
`efficient-branch-selector-on-proved-2to1-instances`.

## Check

`python3 experiments/grassmann-99-rigidity-2026-09-18/check_grassmann_99_rigidity.py`
(seed 20260918). Three independent checks, all exact, no sampling:

1. **Spectral.** The walk `W` is built and diagonalised for
   `(D,l) in {(4,2),(5,2),(6,2),(5,3),(6,3),(7,3),(6,4)}` and matched against
   the closed Grassmann-scheme formula to `1e-8`. Largest non-trivial modulus
   observed: `0.400` at `(D,l) = (6,4)`; every value is below `1/2`.
2. **Gadget uniformity.** For `(D,l) in {(4,2),(5,2),(4,3),(5,3)}` the six
   induced flag laws are computed by exhaustive enumeration over all
   `(Q, P, x, y)` in the generic event. Each of the six hits every flag exactly
   the same number of times (up to 312480 samples over 1085 flags). This is the
   step that makes each of the six union-bound terms cost `eta` exactly.
3. **End to end.** Exact rejection rate and exact
   `min_A Pr_L[sigma_L != A|_L]` for six labelling families at
   `(D,l) in {(5,2),(6,2),(5,3),(6,3)}`. All satisfy `dist <= 800 eta`; the
   worst ratio is `3.0`, attained by zoom-ins.

## Attempts

- **2026-09-18: direct proof via route
  `grassmann-restriction-99-percent-rigidity-proof`, `requires: []` (returned to
  OPEN at landing; kept as an attempt).** Wave `swarm-0917`, lane
  `e2-w2-ugc-selector-kill`. The proof is kept in full as
  `research/artifacts/grassmann-restriction-99-percent-rigidity-proof-2026-09-18.md`,
  with `experiments/grassmann-99-rigidity-2026-09-18/check_grassmann_99_rigidity.py`
  as its artifact.

  - *Reason it is not established.* The lane wrote this node and
    `dkkms-smoothing-leaves-the-branch-coordinate-untested` as a pair, and the
    wave's three-lens referee stage returned a refutation (lens 2) against the
    pair. The lane therefore lands demoted as a whole rather than half
    established. **No referee found an error in Theorem R.** All three lenses
    audited this proof line by line and reported that every load-bearing step
    holds; lens 2, the refuting one, wrote: "What holds: Theorem R itself
    survives the check. Its hypotheses (`eta <= 1/2000`, `2^(l-D) <= eta`,
    `2 <= l <= D-2`) are used exactly where the route says; (Sym) is correct
    ... the Grassmann-scheme eigenvalue import (BCN Thm 9.3.3,
    `lambda_j = 2^(j+1)[k-j]_2[n-k-j]_2 - [j]_2`) expands as stated and both
    inequalities check out, and `2^(l-D) <= eta` forces `D-l >= 11`, which is
    what makes the claimed `lam <= 0.51` (hence `1/(1-lam) <= 2.001` in Lemma
    4.2) legitimate — the constant `800` has only `~0.6 eta` of slack but does
    hold."
  - *What the referees repaired, and is now filled in the artifact.* (a) Lemma
    4.2 asserted `lam <= 1/2 + s <= 0.51` without deriving the bound on `s`;
    `l <= D-2` alone does not give it (at `l = D-2`, `s = 1/15` and
    `1/2 + s = 0.567`). The other hypothesis `2^(l-D) <= eta <= 1/2000` forces
    `D - l >= 11` and `s <= 1/8191 < 1.3e-4`; that line is now written out.
    (b) With `lam ~ 1/2` the mixing bound is `1 - alpha/(1-lam) = 1 - 2.001
    alpha`, not `1 - 2 alpha`, so Lemma 4.3 reads `392 eta` (still `<= 400`)
    and Step 5 reads `784.4 eta` (still `<= 800`). Both constants in the
    statement above survive, with about two percent of slack.
  - *What was corrected in this node.* Corollary R1 said `F_Q(x)` "is exactly
    the quantity a branch selector's bit function returns". Lens 2 pointed out
    that the cited annotation item defines
    `g_e(sigma') := A_(o_e(sigma'))(U,L)(x_e)`, the value of an
    orientation-chosen preimage — the quantity the bit function *predicts*, not
    what it returns. Fixed above.
  - *Independent corroboration worth keeping (lens 3, calibration lens).*
    Theorem R uses group and field structure at four points and is false
    without each: (Sym) needs a group transitive on flags with a unique
    invariant law; BLR's three "`x+y`, `z` independent uniform" moves need
    translation invariance of counting measure on `(X,+)` plus inverses;
    Lemma 4.1's "two distinct functionals disagree on exactly half of `X`" is
    the index-2 kernel of a difference homomorphism, which has no monoid
    analogue and is what buys the factor `2`; and Lemma 3.2 needs the subspace
    lattice of a module over a field to be distance-regular. So the proof does
    not prove too much.
  - *What to do next.* Re-submit this to a clean referee pass. Nothing in it is
    known to be wrong; it awaits a wave whose verdict is not entangled with the
    companion node.
