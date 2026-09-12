---
rg: 2
id: far-sector-length-control-extension-gap
kind: claim
title: Extending the skeleton length control to the full congruence relators is exactly the open far sector, and its precise obstruction
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  bs14-strict-hs-dehn-separation: that establishes linear HS length control for trivial words INSIDE the parabolic skeleton BS(1,4); this is the claim that extends it to trivial words in the normal closure of u^p in the full projective arithmetic group, together with the precise reason it does not extend for free.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that is the finished HNN theorem consuming full stability; this is the specific length-control estimate that a de la Salle style promotion would need in place of full stability.
---

Fix first an odd prime `p`.  A microstate `U` of the projective
`SL_2(Z[1/2])` presentation with the `BS(1,4)` skeleton exactified has
`||u^p(U) - 1||_2` small.  By `iwahori-mod-p-quotient-is-psl2`, the relevant
finite quotient is exactly

```text
Q_p = PSL_2(Z[1/2])/<<u^p>> = PSL_2(F_p).               (FLC1)
```

The de la Salle promotion (arXiv:2204.07084 Thm 1.4) would exactify `U` as
an averaged almost-representation of `Q_p`, then finish with `(tau)` plus
co-density.  Its cost is the transport of the microstate defect to `Q_p`'s
averaged multiplication defect, which is an HS length-control estimate for
the trivial words

```text
w in <<u^p>>_(PSL_2(Z[1/2])),
```

the normal closure of `u^p` in the WHOLE group.

**What is established (skeleton).**  For `w` in the parabolic skeleton
`<u, h> = BS(1,4)`, `bs14-strict-hs-dehn-separation` gives linear-in-length
control `||w(U) - 1||_2 = O(|w| eps(t))`, exponentially below the area bound.

**Why it does not extend for free (the precise obstruction).**  A general
`w in <<u^p>>` is a product of `A = Area(w)` conjugates `g_i u^p g_i^(-1)`,
and

```text
||g_i u^p g_i^(-1)(U) - 1||_2 = ||U(g_i)(u^p(U)-1)U(g_i)^*||_2 approx ||u^p(U)-1||_2,
```

conjugation by the near-unitary `U(g_i)` preserving the HS norm up to
`O(|g_i| t)`.  Summing over the `A` factors gives
`||w(U)-1||_2 <= A(||u^p(U)-1||_2 + O(max_i |g_i| t))`, and `A` is
EXPONENTIAL in `|w|` for `SL_2(Z[1/2])` (Taback: exponential Dehn function).
So the naive extension is area-exponential; the skeleton's linear control
does not transfer, because a congruence relator uses exponentially many
conjugates of `u^p` by unbounded-length elements involving the involution
`S` (`S u S^(-1) = l^(-1)`, the opposite unipotent).

**The one structural point in favour.**  The area-tracking-defect witness of
`centralized-cyclic-distortion-hs-dehn-tracks-area` needs an element
centralizing `u` but OFF the abelian unipotent sheet; in `SL_2(Z[1/2])` the
centralizer of `u` is exactly the abelian unipotent group `{[[1,x],[0,1]]}`,
so that witness does not embed.  Hence the exponential lower bound is NOT
forced by the known mechanism, and the far-sector length control is genuinely
open in BOTH directions.

**Precise open statement.**  Is `Phi(l, t) = O(l eps(t))` (linear in length)
for trivial words in `<<u^p>>_(PSL_2(Z[1/2]))`, uniformly over odd primes
`p`?  A positive answer, with de la Salle Thm 1.4 and `(tau)` plus
co-density, closes the prime-level promotion step toward the far sector.
The averaged (rather than worst-case) form -- controlling
`E_(g,h in Q_p) ||U(g~ h~) - U(g~)U(h~)||_2^2` rather than every
`<<u^p>>` word -- is the weaker statement de la Salle's averaging actually
consumes and is the right target: it may hold even though the worst-case
linear bound above is obstructed, because averaging over `Q_p` samples short
lifts with high probability and the spectral gap of `Q_p` (Selberg/(tau))
suppresses the tail.

For arbitrary odd composite `M`, the analogous identification of
`PSL_2(Z[1/2])/<<u^M>>` with the intended congruence quotient has not been
proved in Cairn and must not be silently imported from the prime theorem.
Either prove that composite-level presentation or show that prime levels
alone provide the periodic approximation needed by the far-sector argument.
This arithmetic issue is separate from the normalized-HS length estimate.

## Attempts

- **Worst-case extension: obstructed** (exponentially many long conjugates,
  above). Do not pursue the worst-case bound directly.
- **Averaged extension via de la Salle: the live target.** Needs the
  transport of generator-defect to averaged-`Q`-defect; the missing estimate
  is that the average over `Q` of the lift-length-weighted defect is
  controlled by `(tau)` of `Q`, an effective-mixing statement for the
  congruence quotients. Dogon--Vidick arXiv:2607.20135 effective
  approximate-invariant-measure machinery is the closest tool.
- **Skeleton is done** (`bs14-strict-hs-dehn-separation`); the involution is
  the only new ingredient, and it enters only through the lengths of the
  conjugating elements, not through a new relator.
