---
rg: 2
id: balanced-parity-multicut-boundary-is-summable
kind: claim
title: Balanced parity makes recursive generated-adjoint cuts globally summable
distinct_from:
  bounded-low-gap-witness-gives-balanced-cut: that extracts one balanced cut from one bounded witness; this must organize every successive cut and spike support with one vanishing global budget
  hs-one-level-expander-block-decomposition: that asks for the corresponding partition for arbitrary Kazhdan almost-representations; this may use the balanced code's Loewner fundamental-cone inequalities and complete-pair Lyapunov energy
  central-adaptive-peeling-or-noncentral-stopping: that pastes coordinate-dependent anchor-tail resets into central blocks; this recursively cuts almost-central elements of the whole generated algebra and asks for a terminal adjoint gap on every retained block
---

OPEN.  Let a retained balanced-overlay block have parity and complete-pair
energy `epsilon`, and suppose its bounded faces have been exactified with the
established row-square ledger.  Recursively apply the low-gap clipping
dichotomy inside every current corner whose generated-adjoint Poincare
constant is below a threshold `lambda_0=lambda_0(epsilon)->0`.

Prove that the spectral cuts and spike quarantines can be chosen so that

```text
 sum_over_cuts (1/L)sum_i||[p_cut,Q_i]||_2^2=o(1),
 tau(total_spike_quarantine)=o(1),                       (BPM1)
```

and every terminal non-quarantined corner has generated-adjoint gap at least
`lambda_0`, with

```text
 epsilon/lambda_0 -> 0.                                 (BPM2)
```

The sums in `(BPM1)` are the actual orthogonal block-compression boundary
costs, not maxima over cuts.  Approximate parity errors created by earlier
cuts must be included in the same telescoping budget.

For exact parity, `adjoint-parity-cone-lifts-to-loewner-order` gives for any
physical projection `p` the boundary spreading estimate

```text
 ||[p,Q_i]||_2^2
 <=(1/(kappa L))sum_j||[p,Q_j]||_2^2                    (BPM3)
```

for every coordinate `i`.  Hence a single low-energy cut cannot hide its
boundary in a sparse set of parity coordinates, and the fixed-width parity
products survive its block-diagonalization at the same average scale.  The
missing theorem is a monotone potential which makes `(BPM3)` summable over
the full cut tree.  Entropy alone loses the cut depth, while a generic
quantum-expander decomposition is false by central mixtures of sparse
Clifford cycles; the proof must charge the cut tree to the balanced parity
and complete-pair Lyapunov energy.

The tree-accounting part is now exact.  If signs are deferred until the
terminal partition, `nested-common-cuts-have-exact-pythagorean-boundary-ledger`
shows that the sum of all actual cut boundaries is precisely the movement
under the one terminal pinching.  Separately,
`adaptive-spike-quarantines-have-summable-trace` gives every recursively
encountered spike a geometric trace allowance, so their union can have any
prescribed `o(1)` trace.  Hence this claim is reduced to the sharper gate
`terminal-common-pinching-displacement-vanishes`: construct terminal
positive-gap blocks whose one common pinching moves the tuple by `o(1)`.

## Attempts

Sequential balanced cutting gives no dimension-free estimate by itself.
Charging each split to the smaller child sums to an entropy and can grow like
the logarithm of matrix dimension.  Quarantining small children also fails:
many disjoint small children may cover unit trace.  The promising quantity
is the **drop of balanced parity plus complete-pair energy under the reducing
block compression**, since orthogonal off-diagonal blocks are then counted
only when first separated.  No proof currently shows that this drop
dominates the sign/polar repair and the parity error created at every level.
That domination, with a summable spike term, is exactly `(BPM1)`.

Repeated sign/polar repair is not a safe potential: it destroys the
orthogonality between boundaries from different levels.  Keeping compressed
contractions through the tree and signing once at the terminal PVM makes all
parity damage a one-shot function of the terminal displacement.  The
remaining issue is proving that displacement vanishes, not preventing the
same matrix block from being counted repeatedly.
