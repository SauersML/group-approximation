---
rg: 2
id: durand-romashchenko-minimal-sft-simulation
kind: claim
title: Every effective minimal Z^d-shift is simulated, column-constantly, by a minimal SFT on Z^(d+1) (Durand--Romashchenko, Theorem 7)
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is the open group version over a finitely presented Λ_0 with a free Z^2-subaction, and quotes only the abstract; this imports the Z^d theorem itself, with the exact simulation definition read from the body, and asserts nothing about freeness or about groups other than Z^d.
  plane-constant-minimal-sft-factors-are-effective-minimal: that is the converse direction (a plane-invariant factor of a minimal SFT is effective minimal) over a general group; this is the realization direction, only over Z^d.
---

**Import.** B. Durand, A. Romashchenko, *The expressiveness of quasiperiodic
and minimal shifts of finite type*, arXiv:1802.01461 (Ergodic Theory Dynam.
Systems 41 (2021)). Read from the arXiv PDF body on 2026-09-17.

**Definition (verbatim, Section 1).** "A shift is called effective (or
effectively closed) if it can be defined by a computably enumerable set of
forbidden patterns."

**Definition 1 (verbatim).** "We say that a shift A on Z^d is simulated by a
shift B on Z^(d+1) if there exists a projection π : Σ_B → Σ_A such that for
every configuration f : Z^(d+1) → Σ_B from B and for all i_1, . . . , i_d, j, j′
we have π(f(i_1, . . . , i_d, j)) = π(f(i_1, . . . , i_d, j′)) (i.e., the
projection π takes a constant value along each column (i_1, . . . , i_d, ∗),
see Fig. 1), and the resulting d-dimensional configuration
{π(f(i_1, . . . , i_d, ∗))} belongs to A; moreover, each configuration of A can
be represented in this way by some configuration of B."

**Theorem 7 (verbatim).** "(a) For every effective minimal Z^d-shift A there
exists a minimal SFT B in Z^(d+1) such that A is simulated by B in the sense of
Definition 1. (b) Let A be a Z^d-shift simulated in the sense of Definition 1 by
some minimal SFT B of dimension d + 1. Then A is effective and minimal."

(Subscripts and exponents are transcribed from the PDF typography, e.g.
`Σ_B` for Σ with subscript B and `Z^(d+1)` for Z with superscript d+1.)

Freeness of `B` is not part of the theorem. For `d = 1` and aperiodic `A` it is
derived in `minimal-free-z2-sfts-have-arbitrarily-hard-row-languages-proof`.
