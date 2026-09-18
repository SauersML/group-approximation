---
rg: 2
id: fp-pl-groups-with-f-have-no-transcendental-support-endpoints
kind: claim
title: A finitely generated PL group with data in Q(λ), λ transcendental, that contains a dyadic copy of Thompson's F and a one-bump element in F's interval with an irrational endpoint is not finitely presented
distinct_from:
  fp-bieri-strebel-line-groups-are-deformation-rigid: that is the Bieri--Strebel line-group case, for arbitrary parameters (A,P), with the conclusion that the slopes are algebraic and the breakpoints lie in the slope field, proved from their explicit presentation; this is a general criterion for any finitely generated PL group of an interval or circle whose data lie in one purely transcendental field Q(λ), proved by deforming λ.
  complexity-bounded-host-classes-are-not-universal: that kills every host family sharing one recursive word-problem bound; this kills finite presentation itself for PL groups with transcendental data, which is the one PL family whose word problem is not bounded a priori.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the open Birget root; this closes one natural construction route to it (see Attempts there).
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

**ESTABLISHED** through `pl-transcendental-endpoint-non-fp-proof` (lane proof, elementary, not
independently reviewed). No priority is claimed: a bounded check of the Bieri--Strebel monograph
(arXiv:1411.2868v3, Chapter D and Notes N3.3b, read at source) found only the necessary conditions
of its Proposition D13.3 for finite presentation, and nothing on transcendental parameters.

## Statement

Let `λ ∈ R` be transcendental, and let `G` be a finitely generated group of orientation-preserving
PL homeomorphisms of `[0,1]` (or of the circle `R/Z`), each with finitely many breakpoints, such that
every breakpoint and every slope and intercept of every affine piece of every generator lies in the
field `Q(λ)`. Suppose

- **(F)** `G` contains the standard copy of Thompson's group `F` on a closed interval
  `D = [d_0, d_1]` with `d_0, d_1 ∈ Z[1/2]` (the conjugate of the usual `F ≤ PL([0,1])` by the affine
  map `[0,1] → D`, extended by the identity), and
- **(E)** `G` contains a one-bump element `u` (no fixed point inside its support) with support
  `(a, e) ⊂ D` where `e ∉ Q`.

Then `G` is not finitely presented. The same holds with `e` replaced by `a` (use `F`-bumps supported
on `(d_0, r)` instead).

**Equivalent hypothesis for (E).** Since `Q(λ) ∩ Q̄ = Q`, "irrational" and "transcendental" agree for
points of `Q(λ)`. Hypothesis (E) holds as soon as some element `g ∈ G` is affine on an open
subinterval `I ⊂ D` with `g(I) ⊂ D` and non-constant data (slope or intercept not in `Q`): conjugate
an `F`-bump supported in a small dyadic subinterval of `I`.

## Consequences

- **Bieri--Strebel groups with a transcendental parameter.** Suppose `2 ∈ P`, `Z[1/2] ⊆ A`, and
  `A, P ⊂ Q(λ)` with some element of `A` or `P` outside `Q`. Then the compact-interval groups
  `G([0,b];A,P)` (`b ∈ A_{>0}`) and the circle groups `T(A,P)` are not finitely presented,
  whether or not they are finitely generated. The same holds for every finitely generated group
  of PL maps with data in `Q(λ)` that contains one of them. Example: `A = Z[1/2][λ^{±1}]`,
  `P = gp(2, λ)`. *Witness for (E).* Take a dyadic `D ⊂ (0,b)`. For a slope `p ∈ P ∖ Q` and small
  `x_0, c ∈ A` with `[x_0, x_0 + c + pc] ⊂ D`, the element with slopes `1, p, 1/p, 1` and
  breakpoints `x_0, x_0 + c, x_0 + c + pc` lies in `G` and is affine with slope `p` on
  `[x_0, x_0+c]`. For a breakpoint `α ∈ A ∖ Q` in the interior of `D`, a dyadic-slope bump with
  support starting at `α` works directly.
- **Birget root.** A PL group containing `F` decides "`e < r`?" for dyadic `r` by the commutator
  `[u, k_r]` of `u` with an `F`-bump on `(r, d_1)`, so a computable transcendental parameter with
  hard digits would make such a group's word problem arbitrarily hard. This theorem shows that
  mechanism can never be finitely presented. It is recorded as Attempt 7 on
  `fp-simple-groups-with-arbitrarily-complex-word-problem`.

## Scope and what is not claimed

- One transcendental parameter only (data in `Q(λ)`). Several independent transcendentals, or
  algebraic extensions of `Q(λ)`, should go through by deforming one element of a transcendence basis
  and following simple roots continuously; this is not written out.
- Homeomorphisms only. PL bijections with finitely many discontinuities (`V`-type) should work
  verbatim with pieces taken as right-open intervals; not written out.
- Nothing is claimed for groups without a dyadic `F` or without an element as in (E); for line groups
  with arbitrary `(A,P)` see `fp-bieri-strebel-line-groups-are-deformation-rigid`.
