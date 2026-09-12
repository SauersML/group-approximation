---
rg: 2
id: dual-prefix-renyi2-rate-gap
kind: claim
title: The dual-prefix Leavitt system has a uniform Renyi-2 address-versus-reservoir rate gap
refuted_by:
  - dual-prefix-renyi2-rate-is-critical-under-rectangular-escape
distinct_from:
  paired-same-reservoir-boundary-lemma: that states the desired finite-matrix same-reservoir dichotomy directly; this asks for an information-theoretic realization and the strict rate inequality needed to derive it by soft covering.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that gives a fixed one-step Gram/rank obstruction after a common reservoir is already identified; this must stop multiplicity growth from hiding the address information over depth.
---

**REFUTED.**  At every fixed dual-prefix depth, functorially associate to the
recovered Leavitt address data a classical-quantum state `rho_XE` and a
codebook/reservoir rate `R` such that:

1. address mismatch or rectangular escape dominates the order-two
   soft-covering divergence by a dimension-independent multiple of the named
   normalized-HS boundary energy;
2. a fixed `epsilon>0`, independent of depth and matrix dimension, satisfies
   `R<=I_2(X:E)-epsilon`; and
3. successful covering identifies the two children and their return maps on
   the same multiplicity reservoir.

## Attempts

- The soft-covering theorem supplies no rate constraint.  Hyperlinear
  microstates may enlarge the spectator multiplicity arbitrarily, so the
  analogy has no force until clause 2 is proved from presentation relations.
- The exact Leavitt identity `R isomorphic to R^2` naturally exchanges label
  dimension for reservoir multiplicity and therefore points in the wrong
  direction unless a paired return or capacity relation caps that exchange.
- The useful target is an information gain per new prefix exceeding the
  allowed multiplicity growth.  Merely identifying `X` and `E` without this
  strict budget cannot imply a selector floor.
- `dual-prefix-renyi2-rate-is-critical-under-rectangular-escape` proves that
  this strict budget cannot follow from the canonical dual-prefix data.  A
  faithful `D`-address code has rate at least `log D`, while every cq state
  on a `D`-valued classical register has sandwiched Renyi-2 mutual
  information at most `log D`.  The exact rectangular model realizes the
  two possible readings sharply: the genuine spectator reservoir is
  independent of the address and has mutual information zero; adjoining the
  label factor makes the addresses orthogonal and saturates the bound
  `I_2=log D`, with no positive slack.
