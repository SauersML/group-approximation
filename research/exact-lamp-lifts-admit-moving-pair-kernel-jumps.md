---
rg: 2
id: exact-lamp-lifts-admit-moving-pair-kernel-jumps
kind: claim
title: Exact lamp lifts of a corona class can jump on moving pairs at every coordinate
distinct_from:
  corona-defect-is-not-uniform: that says corona representations supply pointwise but not uniform multiplicative defect; this fixes an exactly multiplicative lamp lift and shows its two-point kernel is still free at the moving frontier.
  finitary-alternating-augmentation-lamp-global-rounding-no-go: that is a locally finite group whose microstates cannot be globally exactified; this uses the finitely presented Thompson host and a two-dimensional exact model, and constrains the choice of lift rather than the possibility of rounding.
  thompson-pair-kernel-invariance-kills-even-lamps: that is the positive lemma consuming an invariant pair kernel; this shows that invariance is not a consequence of the corona data, so the lemma's hypothesis cannot be obtained by choosing a lift.
artifacts:
  - research/artifacts/finite-memory-pair-kernel-audit-2026-08-23.md
---

ESTABLISHED.  Let `X` be countably infinite, let `s` be a permutation of `X`
with an infinite orbit, and let `(A_n)` be **any** exhaustion of `X` by finite
sets.  Define a character and a two-dimensional representation of `I_X` by

```text
sigma_n(m) = (-1)^(|supp(m) cap A_n|),
tau_n(m)   = diag(1, sigma_n(m)) in U(2).                     (MJ1)
```

Then:

1. `tau_n` is an **exact** homomorphism of `I_X` whose image consists of
   commuting involutions;
2. for every **fixed** `m in I_X` one has `tau_n(m)=I` for all large `n`.
   Hence `(tau_n)` represents the trivial corona class of every lamp, and
   together with the actor lifts `U_(g,n)=I_2` it evaluates every relator of a
   fixed finite presentation of `I_X rtimes V` to the identity for all large
   `n` — presentation defect exactly `0`, not merely `o(1)`;
3. for every `n` such that `A_n` meets the infinite `s`-orbit there are
   `x_n != y_n` with

   ```text
   tau_n(b_(x_n,y_n)) = I,
   ||tau_n(b_(s x_n,s y_n)) - I||_op = 2.                     (MJ2)
   ```

So the pair-kernel jump quantity `J_n(s)` of the finite-memory memo equals `2`
at every coordinate, for a model of dimension `2`.

**Consequence 1 — the moving-pair return checksum is false as stated.**  The
proposed target (memo id `thompson-moving-pair-return-checksum`: every
sufficiently accurate model, *after correcting its lamp subgroup to an exact
representation `rho`*, satisfies `rho(b_(x,y))=I => ||rho(b_(s x,s y))-I||<2`
simultaneously for all pairs) quantifies universally over admissible
corrections.  `tau_n` is an admissible correction of an exact model whose lamp
corona class is trivial, and it violates the conclusion at every coordinate.
No dimension-independent modulus can repair this: `d_n=2`.

**Consequence 2 — the existential reading is a restatement.**  If instead one
asks only that *some* exact correction have an invariant pair kernel, then
`rho=1` is admissible exactly when the corona representation already kills
every lamp, so the hypothesis is equivalent to the desired conclusion.  With
`thompson-pair-kernel-invariance-kills-even-lamps` this closes the loop: for a
fixed exact `rho` the invariance hypothesis and the triviality conclusion are
the same statement, so neither reading yields a smaller target.

**What is actually free.**  A corona representation pins an exact lift only at
fixed module elements; `(MJ1)` shows the lift is unconstrained at the moving
frontier, where `sigma_n` is a nonconstant character of `I_X` that vanishes on
every fixed element.  Kernel invariance is therefore not a property the corona
data transports, and the surviving formulation must constrain the correction
by the model's own word evaluations, uniformly over pairs — see
`thompson-pair-lamp-consistent-exactification`.

**Weaker vacuity variant.**  A tail partition (each point of `A_n` a singleton
class, `X \ A_n` one class) instead makes the fixed-pair implication
*vacuously* true — every fixed distinct pair is eventually separated — while
moving witnesses `x_n=s^(-n-1)x_0`, `y_n=s^(n+1)x_0` stay in the common tail
and are separated after applying `s`.  The character twist `(MJ1)` is the
stronger statement, because there the fixed-pair covariance holds
non-vacuously and with the actor exactly represented.

**Scope.**  This does not refute `operator-norm-finite-state-rounding`,
`self-copy-kadison-kastler-checksum`, or the goal
`finite-memory-self-hash-non-mf`.  It refutes one proposed shortcut to them:
the exact-involution `0`-versus-`2` dichotomy alone cannot convert corona data
into kernel invariance.
