---
rg: 2
id: graded-corner-images-of-bloop-force-classical-solution
kind: claim
title: Homogeneous images of a generic synchronous-game BCS in a graded algebra with scalar identity component force a classical perfect strategy
distinct_from:
  binary-tracial-two-csp-has-classical-solution: that starts from a Boolean unary-binary CSP with a tracial operator solution; this starts from the multi-answer generic conversion of a synchronous game in an arbitrary nonzero unital algebra, and first proves that homogeneous images cap every question at two active answers, which is what lowers it to a 2-CSP.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that turns affine-hull-safe tracial supports into a non-CE LCS; this shows that for exactly-one/forbidden-pair sources affine supports leave no gap at all, and needs no trace.
  exact-label-coset-refinements-are-affine: that proves affine support for label-exact coset refinements of context games; this proves affine support for homogeneous generator images in any group-graded algebra with scalar identity component, including signed group-ring corners and twisted group algebras.
  leavitt-root-signs-cannot-host-the-perfect-synchbcs: that fences individual root spectral signs and the Clifford base; this kills every monomial occurrence map into a group-ring corner, over any group and any involution.
  agent-leavitt-not-bcs-negative-root-corner: that is the open corner construction; this proves every construction in it must use inhomogeneous (non-monomial) images.
artifacts:
  - research/graded-corner-images-bloop-classical-proof.md
---

**ESTABLISHED (kill of the monomial/solution-group class).**

**Setting.**  Let `G` be a finite synchronous game and `B_G` its generic
Mastel--Slofstra BCS, as in `lin-explicit-fixed-bcs-gap-via-generic-conversion`:
Boolean variables `x_(i,a)`, one exactly-one context per question `i`, and a
two-variable context forbidding `x_(i,a) and x_(j,b)` for each losing pair.
`A(B_G)` is its BCS algebra: involutions `z_x`, commuting inside contexts,
with every forbidden atom set to zero
(`paddock-slofstra-bcs-forbidden-projection-dictionary`).

Let `D` be a nonzero unital complex algebra graded by a group `H`,

```text
D = direct_sum_(h in H) D_h,   D_g D_h <= D_(gh),   D_e = C 1.      (GCB1)
```

**Theorem.**  If `Phi: A(B_G) -> D` is a unital algebra homomorphism and every
`Phi(z_x)` is homogeneous, then `G` has a perfect deterministic strategy.

The proof has two exact steps.

1. **Affine support.**  In each context `c`, the set of atoms with nonzero
   image is a coset of an `F_2`-subspace.  Hence a question has at most two
   *active* answers, meaning answers `a` with `Phi((1+z_(i,a))/2) != 0`.
   (The sign convention for "true" is fixed once.)
2. **2-SAT collapse.**  A representation in any nonzero unital algebra with
   at most two active answers per question gives a classical solution.  This
   uses implications between idempotents and the Aspvall--Plass--Tarjan
   criterion.

**Corollary (monomial corner maps are dead).**  Let `Gamma` be any group, let
`z in Gamma` be an involution, and put `P_z=(1-z)/2`.  There is no unital star
homomorphism `A(B_loop) -> P_z C[Gamma] P_z` with

```text
A_x in C . P_z g_x,        g_x in C_Gamma(z),                        (GCB2)
```

for every variable `x`.  The same holds with the target a twisted group
algebra `C^alpha[H]` and images scalar multiples of basis elements.  It also
holds for any map induced by a group homomorphism `Gamma' -> Gamma` sending
`J` to a central sign.

In particular, the following cannot supply `LNC3` of
`agent-leavitt-not-bcs-negative-root-corner`, for any support:

- solution-group-style homomorphisms into the Leavitt unit group or into
  Thompson's `V`;
- Weyl or root-sign monomial images;
- signed permutation images.

**Invariant and death step.**  The invariant is the context degree map
`d_c: F_2^c -> H`.  Its nonzero atoms form a coset of `(ker d_c)^perp`.
Every member of the class dies at the exactly-one context: an affine set of
one-hot vectors has at most two points.

**Survivors.**  Every `LNC3` diagram needs a question with at least three
active answers.  At least one of its answer involutions must be inhomogeneous
for every grading of the corner as in `(GCB1)`.  Examples of survivors are
signed Hecke projections and sums over several cosets of `<z>`.

**Scope note.**  The Corollary uses only that `B_loop` has no perfect
classical strategy.  Its quantum gap is not used.
