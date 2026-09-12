# Two counterexamples to deleting the rigidity hypothesis

2026-09-07.  Audit of the seventh and eighth forwarded dossiers, both
answering the same question — can property (T) be removed from the
compression mechanism — and both answering it negatively by exhibiting an MF
group in which the compression defect survives.  Every identity below was
re-derived here by hand.

Both dossiers are explicit that they do **not** supply a property-(T)-free
existence proof.  That honesty is the load-bearing part of them and is
recorded here as such: nothing in this artifact closes
`property-t-free-manuscript-results`.

## The finding that should be read first: most of both dossiers is already here

Of the seventh dossier's four sections, three were already wired:

- its §3 corner inequality
  ```text
  1 <= ||t_0s_0 - p|| + ||t_1s_1 - p|| + ||s_0t_0 + s_1t_1 - p||
  ```
  is `atomic-leavitt-gap-on-nonzero-matrix-corner`, established, in the sharp
  `m`-ary form `m-1 <= sum_i ||t_is_i - p|| + ||sum_i s_it_i - p||`;
- its §4 unproved extraction hypothesis is verbatim
  `binary-leavitt-atomic-morita-return`, open, down to the same group
  `St_20(L_(F_2)(1,2))`, the same mark `z = x_13(s_1t_1)`, and the same
  prescribed carrier `p_U = (1 - z_round(U))/2`;
- its §4 conditional theorem is the route
  `property-t-free-leavitt-via-atomic-morita-return`, and the normal-generation
  calculation it prints is the established root-saturation step.

Of the eighth dossier, §3's proposed research target

```text
||k(U) - 1|| >= 1  ==>  max_(r in R_0) ||r(U) - 1|| >= eta
```

is `finitely-presented-marked-involution-corona-gap`, established, and as an
*equivalence*: for a finitely presented group and a word whose value is an
involution, corona invisibility of the mark is the same thing as a
dimension-uniform presentation gap on the negative spectral cut.  So the
target is not a conjecture to be formulated but a known reformulation, and
the open part is exactly what the dossier says it is — producing the gap from
an identity or an index obstruction.

The genuinely new content of both dossiers is therefore the counterexample,
and that is what was authored: `mf-group-with-finite-central-compression-defect`
with two independent routes.

## What was verified

**The eighth dossier's solvable witness.**  `D = Z[1/2]`,
`N = D x D x (D/Z)` with `(x,y,z)(x',y',z') = (x+x',y+y',z+z'+xy')`,
`alpha(x,y,z) = (2x,y/2,z)`, `G = N x|_alpha <t>`, `a = (1,0,0)`,
`b = (0,1,0)`, `L = <a>`.  Checked: `alpha` is an automorphism (both sides of
the product rule give `(2x+2x',(y+y')/2,z+z'+xy')`); `a^n = (n,0,0)` so
`L ~= Z`; `tat^(-1) = a^2` with `<a^2>` of index two; `[b,a^n] = (0,0,-n) = 0`
in `D/Z`, so `b` centralizes `L` — and this is the only role of the quotient
by `Z`; `tbt^(-1) = (0,1/2,0)`, so
`[tbt^(-1),a] = (0,0,-1/2) =: k`, which is nonzero, of order two, and central.
`G = <a,b,t>` because conjugation by `t` sweeps out both `D`-axes and their
commutators sweep out `D/Z`.  `G` is solvable, hence elementary amenable,
hence MF by Ozawa--Rordam--Sato.

**The seventh dossier's corona witness.**  With `n` odd, `w = e^(2 pi i/n)`,
`m = (n+1)/2`, `U e_j = w^j e_j`, `X e_j = e_(j+1)`, `T e_j = e_(mj)`.
Checked: `UX = wXU`, `TUT* = U^2` (both sides send `e_k` to `w^(2k)e_k`),
`TXT* = X^m` (both send `e_k` to `e_(k+m)`).  With `A = U (+) U`,
`B = T (+) T`, `C = [[0,X],[X*,0]]`: `C^2 = 1`, `BAB* = A^2`,
`||AC - CA|| = |w-1| -> 0`.  With `V = BCB* = [[0,X^m],[X^(-m),0]]`,
`X^(-1)UX = wU` gives `VAV = diag(w^(-m)U, w^m U)`, so
`[V,A] = diag(w^(-m), w^m)`, and `w^m = -e^(pi i/n) -> -1` since `n` is odd.
So the defect is the scalar `-1` in the corona.  `||A^k - 1|| -> 2` for every
fixed `k != 0`, so `a` has infinite order.

## What the counterexample is worth, and what it is not

It is a sharpening, not a new phenomenon.  The graph already had two MF groups
with a surviving intrinsic compression defect —
`bare-self-copy-mf-calibration` (a torsion-free amalgam, defect word of
infinite order) and `infinite-cyclic-compression-lamp-mf` (integer lamps over
a compressed site space).  What neither of them addressed is the *finite-order*
case, and that is precisely the case the repository's later refinements were
built for: `finite-normal-compression-obstruction` kills a finite normal
subgroup of the defect by averaging, and
`torsion-normal-generator-has-full-support-corona-core` reblocks a corona-visible
finite-order mark into a Hilbert--Schmidt-visible one.  The new witnesses put a
central subgroup of order two in the defect of an MF group, so both refinements
keep their property-(T) hypothesis on `L` for a reason.

The corona witness adds the quantitative end of it: the surviving defect is the
scalar `-1`, displaced by exactly `2` in operator norm *and* in normalized
Hilbert--Schmidt norm.  So there is no vanishing-rank slack for reblocking to
take up, and the transport corollary `cor:defect-hs` — which makes `D_G(L)`
Hilbert--Schmidt-null when `L` has property (T) — fails as badly as it can
without that hypothesis.

Neither witness constrains the live property-(T)-free lane, which does not
transport anything: it runs through the corner inequality and the atomic
Morita return.

## On the K_1 / AH remark

The eighth dossier warns that using the `K_1` classification to prove non-MF
existence would be circular, since the `K_1` route inherits property (T) from
the rank-four theorem.  No route in the graph does this — `cairn check`
reports no dependency cycle, and the recently landed `K_1` nodes
(`agp-purely-infinite-simple-k1-is-unit-abelianization`,
`leavitt-gl-equals-el-via-purely-infinite-k1`) feed the identification
`GL = EL`, not any non-MF claim.  The warning is about an argument not yet
written, and is recorded here rather than as a node, because an obstruction
claim with nothing to invalidate would be inert.

The same dossier's observation that the AH obstruction occurs inside an MF
algebra, so its failure of stabilization cannot by itself give non-MF-ness, is
an assessment of an external paper and is likewise recorded here only.

## Not asserted

No literature priority for either construction; the solvable one is an
elementary explicit group and the corona one is a short matrix calculation.
Nothing here is formalized in Lean.  The MF-ness of the solvable witness is
quoted from Ozawa--Rordam--Sato and was not reproved.  No claim is made that
property (T) is *necessary* for a non-MF construction — only that it cannot be
deleted from the transport step while keeping the rest of that step intact.
