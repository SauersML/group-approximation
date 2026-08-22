---
rg: 2
id: three-label-affine-lowering-no-go
kind: claim
title: Three-label answer splitting makes the exact affine lowering classically satisfiable
distinct_from:
  tracial-support-affine-linearization: that constructs a perfectly tracial affine-support LCS for an arbitrary chosen trace; this claim constructs a separated source and trace for which that LCS has a scalar solution.
  linear-encoding-lcs-admits-odd-subset-cheats: that retains every compatible odd-subset profile under an arbitrary exact linear encoding; this claim gives a finite preprocessing which makes the support-affine relaxation itself trivial while preserving the source gap and later oracularizability.
  oracularizable-tracial-nonru-game-exists: that establishes the perfect oracularizable source interface; this claim proves that the same interface, even together with exact tracial support, cannot black-box imply an affine LCS gap.
---

There is a finite BCS `B^(3)` and a tracial satisfying state `tau` with all
three properties below.

1. `B^(3)` is not `R^U`-satisfiable.
2. The Fu--Mastel--Zhang constraint--variable game of `B^(3)` has a perfect
   commuting strategy which is oracularizable on every sampled pair, and its
   quantum-approximable value is strictly below one.
3. The exact affine-support LCS `L_tau` obtained from `tau` by
   `tracial-support-affine-linearization` is classically satisfiable.

The construction starts with the Paddock--Slofstra/MIP*=RE source, passes to
its associated synchronous game, and replaces every answer `a` by three
labels `(a,t)`, `t in F_3`.  The split verifier accepts only when the original
answers accept and the two labels agree.  Coarse-graining `(a,t) -> a` shows
that this operation cannot increase quantum-approximable value.  A perfect
tracial strategy survives by tensoring its answer PVMs with the three minimal
projections of `C^3`.

Apply the standard synchronous-game-to-BCS conversion to the split game.  Its
contexts are one-hot constraints and two-bit NAND constraints forbidding one
rejected answer pair.  In the split trace every pair of nonzero orthogonal
answer projections has a complement of positive trace: if the labels agree,
the other two label fibers remain, and if they differ, the third fiber
remains.  Consequently every such NAND context has all three allowed atoms in
tracial support and contributes no affine equation.  Zero answer projections
only set their own Boolean coordinates to zero.  Each one-hot context lowers
to odd parity on its nonzero answer coordinates.  Choosing one nonzero answer
coordinate independently for every question gives a scalar solution of
`L_tau`.

Thus perfect oracularizability plus a fixed finite-dimensional source gap does
not, even with access to the exact support of the perfect trace, imply that
the support-affine/noise-free LCS lowering retains any soundness gap.  This is
a black-box interface obstruction only.  It does not rule out a
source-specific global compiler whose extra relations retain information
beyond local affine support.
