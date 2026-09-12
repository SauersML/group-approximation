---
rg: 2
id: finite-left-inverse-identity-does-not-force-balance
kind: claim
title: Off groups the finite left-inverse identity does not force balance, as an unbalanced injective tree automaton shows
distinct_from:
  every-injective-ca-has-uniform-single-site-output-law: that is the open goal-equivalent statement that injective automata over groups are balanced; this is a calibration on the vertex set of a tree with a fixed end, where right cancellation of reads fails, and it says nothing about groups.
  strict-automata-give-injective-ca-with-skewed-site-marginals: that builds an unbalanced injective automaton over a group from a strict one; this is a direct construction on a homogeneous space of a non-unimodular group, where that theorem does not apply.
artifacts:
  - research/artifacts/injective-balance-needs-inf-and-nonlocal-2026-09-12.md
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
---

**ESTABLISHED** in the corrected form below.

- **Route:** `finite-left-inverse-identity-does-not-force-balance-proof`.
- **Verification:** verified and corrected forward by `w4-vf-positive-b`, Section 1 of its verification artifact.

**Correction 2026-09-12 (w4-vf-positive-b).**

- **What the first version said:** there is a *group* `Gamma` with an injective cellular automaton `kappa: B^Gamma -> B^Gamma`
  whose rule is not balanced.
- **Why that over-claims:** over a group, such an automaton is a counterexample to Gottschalk's conjecture, because bijective
  automata preserve the uniform measure.
- **Why the proof did not give it:** the witness was the end-fixing tree, which is not a group acting on itself, and the group
  theorem it quoted does not apply there.
- **Now:** the claim states only what holds on the tree.

**Setup.**

- `T` is the 3-regular tree with a fixed end `xi`, and `V` is its vertex set.
- `p(v)` is the parent of `v` toward `xi`, and `v'` is the sibling of `v`.
- `Gamma = Aut(T, xi)` acts on `V`.
- `A` has `q >= 2` symbols, including `0` and `1`, and `B = A^2`.

**The automaton.** Define

    kappa(x_0, x_1)(v) = ( x_0(v), z(v) ),
    z(v) = 0            if x_0(v) = 1 and x_0(v') = 0,
    z(v) = x_1(p(v))    otherwise.

**Established:**

- `kappa` is continuous, `Gamma`-equivariant and local.
- It is injective, and a finite equivariant decoder reads it back from the two children of each vertex. So it satisfies the finite
  left-inverse identity for every pattern on its window.
- Its one-site output law under the uniform product measure is not uniform: the symbol `(1, 0)` has mass
  `2q^-2 - q^-3 > q^-2`.

**What this shows.** Read the finite left-inverse identity as an identity on an abstract labelled incidence pattern. Then it does
not force balance.

**What it does not show.**

- It shows nothing about groups, and it does not show that a proof must be nonlocal.
- The tree pattern fails right cancellation: the two children read their parent in the same memory position. In a group,
  `eta m = eta' m` forces `eta = eta'`, and that is finite data of every window.
- On patterns realized inside a group, "the identity forces balance" is equivalent to
  `every-injective-ca-has-uniform-single-site-output-law`, and so to the goal.
- So a counting proof from the identity must use right cancellation of reads, as
  `end-fixing-tree-symmetries-carry-strict-automata` already indicates.

**Separate and still standing:** the entropy analysis in Section 1 of the artifact. The conjugacy-entropy proof of balance bounds
the site entropy below only by the Bernoulli Rokhlin entropy. So it factors exactly through INF
(`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`).
