---
rg: 2
id: every-gl-n-z-embeds-in-2v
kind: claim
title: Every GL_n(Z) embeds in the Brin-Thompson group 2V
distinct_from:
  every-gl-n-z-embeds-in-some-brin-thompson-group: that allows the dimension m of mV to grow with n; this fixes m = 2, so it implies that claim.
  zaremsky-2-19d-every-gl-n-z-in-2v-resolved: that claim is Zaremsky's question 2.19(d); this claim is its affirmative answer.
---

For every `n >= 1`, `GL_n(Z)` is isomorphic to a subgroup of `2V`.
Equivalently, a finite-index subgroup of `SL_n(Z)` embeds in `2V` for every `n`.
It implies `every-gl-n-z-embeds-in-some-brin-thompson-group` through
`every-gl-n-z-in-some-nv-from-2v`.

## Attempts

- 2026-09-13 (lane z2-19-glnz-q-2v, unreviewed): `n <= 2` holds, since `GL_2(Z)`
  embeds in `V <= 2V`.
- For `n >= 3`, `2V` would contain `H_3(Z)` and the infinite Kazhdan group
  `SL_3(Z)`. That needs a drift-free central element, which exists in `2V`
  (`brin-thompson-mv-contains-a-distortion-element`, m = 2), and it needs `2V` to
  fail the Haagerup property.
- Every RAAG sits in some `GL_N(Z)`, so this claim puts every RAAG in `2V`. That
  contradicts the Belk–Bleak–Matucci conjecture that `Z^3 * Z` does not embed in
  `2V` (arXiv:1602.08635, Conjecture 1.7). A proof of that conjecture for
  `m = 2` would refute this claim. The statement that all RAAGs embed in some
  `GL_N(Z)` (Davis–Januszkiewicz embedding in right-angled Coxeter groups plus
  the integral Tits representation) was not re-read.
- 2026-09-17 (c-glnz2v, swarm-0917, correction): the previous bullet no longer
  counts against this claim. `every-raag-embeds-in-brin-thompson-group-2v` is
  ESTABLISHED. Salo (arXiv:2103.06663, abstract) writes: "The group $\llb X \rrb$
  embeds in the higher-dimensional Thompson group $2$V, so it follows that $2$V
  contains all RAAGs, refuting a conjecture of Belk, Bleak and Matucci." So the
  RAAG side is consistent with this claim, but it gives no evidence for it, as
  the next bullet shows.
- 2026-09-17 (c-glnz2v, class kill: Salo's host and every Z^d-subshift
  full-group host). Established
  `subexponential-schreier-growth-excludes-sl3z-and-bs1k`. Any faithful action
  of subexponential orbit growth excludes `SL_3(Z)` and `BS(1,k)`. Subquadratic
  orbit growth also excludes `H_3(Z)`. The invariant is the size of Schreier
  balls. Every member of the class dies at the pigeonhole count: the distorted
  root element `x_13`, with `|x_13^N| <= 3 log_φ N + 9` from exact Zeckendorf
  words, has more than `M` orbit points inside a ball of radius `O(log M)`.
  Hence `[[{0,1}^Z]] ≤ 2V`, which carries every RAAG, contains no `H_3(Z)` and no
  `GL_3(Z)`. No topological full group of a `Z^d`-action contains `SL_3(Z)`. The
  RAAG technique cannot be extended to this claim. A host must have exponential
  orbit growth on every faithful invariant set, as the rewriting machines
  `RTM(n,k)` of Callard–Salo do.
- 2026-09-17 (c-glnz2v, class kill: fibred and triangular constructions).
  Established `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`. Every
  infinite-order element of `nV` that preserves the coordinate flag in both
  directions has a periodic orbit with nonzero offset. The proof inducts on the
  flag: a hyperbolic periodic base point gives a nonzero base offset, and
  otherwise a fibre return map of infinite order gives one.
  - Heisenberg centres and root elements of `SL_3(Z)` must be drift-free. So no
    embedding `GL_3(Z) → 2V` sends a nontrivial root-element power into any
    conjugate of `V × V`, of `C(C,V) ⋊ V`, or of their coordinate swaps.
  - The candidate dies at `e_13 = [e_12, e_23]`. The invariant is the offset
    vector of a periodic orbit.
  - An embedding must use elements whose inverses break the fibration, as the
    baker's map does.
- 2026-09-17 (c-glnz2v, reframing, not a separate node). For odd `n >= 3`,
  `SL_n(Z)` has trivial centre. By
  `higher-rank-lattice-normal-subgroups-central-or-finite-index`, every
  homomorphism `SL_n(Z) → 2V` with infinite image is injective. The image is
  infinite iff `φ(e_12)` has infinite order: if `φ(e_12)^m = 1`, the kernel is
  non-central, so it has finite index. `GL_n(Z)` embeds in `SL_{n+1}(Z)` by
  `A ↦ diag(A, det A)`.
  - So this claim holds iff, for every odd `n >= 3`, some assignment of the
    elementary generators that satisfies a finite presentation of `SL_n(Z)`
    sends `e_12` to an infinite-order element of `2V`. Faithfulness never has to
    be checked.
  - There is no generic machine certificate. Belk–Bleak (arXiv:1405.0982,
    abstract): "we prove that the torsion problem for elements of the
    Brin-Thompson group 2V is undecidable". The drift test cannot certify
    infinite order here either, because `φ(e_12)` must be drift-free.
