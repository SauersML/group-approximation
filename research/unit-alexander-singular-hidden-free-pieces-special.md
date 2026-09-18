---
rg: 2
id: unit-alexander-singular-hidden-free-pieces-special
kind: claim
title: The minimal singular-extreme relators with unit Alexander polynomial kill every solvable witness, yet 16 of them are hyperbolic and virtually special and 24 more fail only the nonsingularity hypothesis
distinct_from:
  linton-graph-certificate-for-free-magnus-pieces: that certificate needs an interior letter occurring once; this runs it on pieces that are free only after a Whitehead change of basis, which that script reports as NONFREE, and one level down on the pieces themselves.
  length15-16-free-piece-residue-classes-hyperbolic-special: that certifies the length-15 and length-16 residue lists; this certifies length-19 relators with a singular extreme, a class that is empty up to length 16.
  nonsingular-magnus-extremes-separable-piece-sofic: that needs both extreme exponent sums nonzero; every relator here has a zero extreme exponent sum, so that theorem never applies.
  quasiconvex-hierarchy-piece-nonsingular-extremes-sofic: that is the theorem under (N) and (QC); this exhibits 24 relators where (QC) holds and (N) fails, so they are the minimal test cases for removing (N).
  rational-perfect-core-blocks-rrs-kernel-lifts: that is a general statement about lifts over a perfect core; this uses only the elementary fact that a unit Alexander polynomial makes the kernel perfect, applied to the Magnus piece.
  rank-two-bs-model-roots-need-infinite-order-witnesses: that shows Baumslag--Solitar roots in the piece block finite witnesses; here the pieces have no Baumslag--Solitar subgroups, so that obstruction misses.
artifacts:
  - experiments/one-relator-perfect-kernel-2026-09-18/gen_singular.py
  - experiments/one-relator-perfect-kernel-2026-09-18/gen19n1.out
  - experiments/one-relator-perfect-kernel-2026-09-18/gen19n2.out
  - experiments/one-relator-perfect-kernel-2026-09-18/gen19n3.out
  - experiments/one-relator-perfect-kernel-2026-09-18/whitehead.py
  - experiments/one-relator-perfect-kernel-2026-09-18/analyze.py
  - experiments/one-relator-perfect-kernel-2026-09-18/pieces19.out
  - experiments/one-relator-perfect-kernel-2026-09-18/open19.txt
  - experiments/one-relator-perfect-kernel-2026-09-18/lg19.out
  - experiments/one-relator-perfect-kernel-2026-09-18/linfree.py
  - experiments/one-relator-perfect-kernel-2026-09-18/linfree19.out
  - experiments/one-relator-perfect-kernel-2026-09-18/mmcert.py
  - experiments/one-relator-perfect-kernel-2026-09-18/mmcert19.out
  - experiments/one-relator-perfect-kernel-2026-09-18/calib16.py
  - experiments/one-relator-perfect-kernel-2026-09-18/calib16.out
---

ESTABLISHED (written proof, unreviewed). Proof:
[[unit-alexander-singular-hidden-free-pieces-special-proof]].

**Setting.**
- `G = <a,t | w>`, where `t` has exponent sum zero in `w` and `a_i = t^(-i) a t^i`.
- `W_0(a_0,...,a_n)` is the Magnus rewriting.
- The Magnus piece is `B_0 = <a_0..a_n | W_0>`, with Magnus subgroups `F_-` and `F_+`.
- `N = ker(G -> Z)` is the kernel of `t -> 1`.
- `eps_i` is the exponent sum of `a_i` in `W_0`, and `Delta(t) = sum eps_i t^i`.
- An extreme is *singular* if its `eps` is `0`. Every relator here is unpeelable at both extremes.

## Theorem

**(A) Obstruction (1) hits for the whole unit class.** Suppose `Delta = +-t^k`. Then `N = G'` is
perfect, so `G^(k) = N` for every `k >= 1`, and `B_0 <= N = G^(omega)`. Three consequences:
- Every solvable quotient of `G` kills `B_0`.
- Every quotient of `N` whose image is residually solvable is trivial. So no solvable, residually
  solvable or residually-`p` witness family can separate even one nontrivial element of `B_0`
  from `1`.
- Every finite witness that is nontrivial on `B_0` has a nontrivial perfect image of `N`, so it is
  non-solvable.

**(B) The minimal list.** Up to the census symmetries, the unit-`Delta` relators with a singular
unpeelable extreme have length at least 19. At length 19 they are:
- 182 relators with `n = 1`, all closed by the landed census certificates;
- 52 relators with `n = 2` (`gen19n2.out`), all with level sums `(0,0,+-1)`;
- none with `n >= 3`.

Of the 52, 4 are closed by the census certificates (`R1 PEEL/PP`). The other 48 are closed by no
census certificate, and the visible-free Linton script calls every one of them NONFREE
(`lg19.out`).

**(C) Sixteen are hyperbolic and virtually special.** For 16 of the 48, `W_0` is primitive in
`F(a_0,a_1,a_2)`, so `B_0` is free of rank 2, although no interior letter occurs once. A
Whitehead-tracked basis puts `G` in the form `K *_psi` with `K = F_2`. The graph-of-cyclic-stabiliser
certificate then passes on each of them with no loops of either kind (`linfree19.out`). The 16
relators are:

    AAtATattAATaTattaTT AAtATattATaTattaaTT AAtATattaTaTattAATT AAtATattaaTaTattATT
    AAtAtAATTataTattaTT AAtAtATTataTattaaTT AAtAtaTTataTattAATT AAtAtaTTattAATataTT
    AAtAtaaTTataTattATT AAtAtaaTTattATatATT AAtaTattATATattaaTT AAtaTattaTATattAATT
    AAtaTattaaTATattATT AAtatAATTatATattaTT AAtatATTatATattaaTT AAtataTTatATattAATT

For each of them:
- `G` is hyperbolic and virtually special, with no Baumslag–Solitar subgroup, so obstruction (2)
  misses.
- `G` is residually finite, hence **sofic**.
- The witness family is the finite quotients of `G`. They separate every finite subset of `B_0`
  from `F_-`, `F_+` and `1`, and by (A) every such witness is non-solvable.

**(D) Twenty-four fail only nonsingularity.** For 24 of the remaining 32, the Magnus–Moldavanskii
rewriting of `B_0` along a letter of zero exponent sum gives `B_0 = V *_psi`, where:
- `V` is free, since the rewritten relator is primitive;
- the edge groups have rank at most 2;
- the certificate passes (`mmcert19.out`).

So `B_0` satisfies (QC) of [[quasiconvex-hierarchy-piece-nonsingular-extremes-sofic]]. It is
hyperbolic and virtually special, and it has separable Magnus subgroups (hypothesis (S)). Obstruction
(1) hits and obstruction (2) misses. The only hypothesis of the landed theorem that fails is (N),
because `eps_0 = 0`. Example: `AAtATatatAATTattaTT`, with `W_0 = x^-2 y^-1 x y z^-2 x z`. It can
also be written as `B_0 = <x,z,y | y^-1 x y = x^2 z^-1 x^-1 z^2>`, a cyclic HNN extension of `F_2`
along non-conjugate maximal cyclic subgroups.

**Open remainder.** The remaining 8 give edge rank 3 or a non-free vertex group at the second level:

    AAtATattAATTattaTaT AAtATattATTattaaTaT AAtATattaTTattAATaT AAtATattaaTTattATaT
    AAtAtAATTattaTTataT AAtAtATTattaaTTataT AAtAtaTTattAATTataT AAtAtaaTTattATTataT

**Calibration.**
- The tracked-basis route reproduces all 70 landed length-16 PASS verdicts (`calib16.out`).
- It also certifies 34 more length-16 classes that the visible-free script called NONFREE. These
  were already residually finite by virtual fibring.
- `lintongraph.py calib` still reproduces Linton's Example 1.2 (PASS) and Example 6.12 (a
  Baumslag–Solitar alternating cycle).

## What this settles for the lane

The step asked, for an unpeelable relator, whether (1) `B_0` meets `G^(omega)` and whether (2) the
singular extreme carries a Baumslag–Solitar root.
- On the minimal singular class, (1) always hits: every solvable alphabet in the (AA) and (AA_G)
  dictionaries is dead there.
- (2) misses on 40 of the 48 open relators.
- Where (2) misses and the group is hyperbolic (16 relators), finite, necessarily non-solvable
  witnesses exist. No infinite-order witness is needed.
- The 24 relators of (D) are the minimal instances of the singular-extreme problem with a (QC)
  piece. Proving soficity for them needs exactly a replacement for the backward step of the
  shift dictionary, which is a singular equation.
