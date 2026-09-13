# Affine-support value gap of the magic-square AND gadget (2026-09-13)

Lane `solve-nh-affine-value-bound`. Target: `non-hyperlinear-group` through gap
(iii-c) of `research/artifacts/ce-only-decoder-floor-map-2026-09-13.md`: a
constant-gap upper bound `s < 1` on the value of affine-support strategies for
an affine-unsafe source, sharpening the qualitative firewall
`matrix-conj-forces-unsafe-support` /
`ce-exact-affine-compilers-force-nonhyperlinear-corners`.

## What is landed

- `affine-safe-value-of-magic-square-and-gadget-below-one`
  (claim) and `magic-square-and-gadget-affine-value-proof` (route):
  the fixed magic-square AND gadget `B_MS^AND` has affine-safe value at most
  `1 - 4/(9 C0 T)` and canonical-corner-pushforward value at most
  `1 - 1/(9 C0 T)`, where `T = 4^5 * 27 * k` is the relator-state modulus of
  the gadget and `C0` is the fixed relation-count of the `(UTC4)`
  anticommutation derivation. Both are fixed positive constants of the single
  gadget.
- `constant-gap-affine-corner-compiler-forces-nonhyperlinear` (claim)
  and `constant-gap-affine-corner-compiler-nonhyperlinear-proof` (route): a
  constant-gap affine corner compiler for `B_tilde = B_0 U B_MS^AND` with
  soundness `s > 1 - 1/(9 C0 T)` on Connes-embeddable models forces a
  nonhyperlinear target.

## Formalizing the affine-support value (directive step 1)

For a synchronous strategy with state `tau`, "affine-safe" is the (LAS1)
condition of `locally-affine-support-bcs-is-exactly-the-lcs-boundary`:
`affineHull(supp(tau_c)) subseteq Allowed_c` in every context. By that node,
affine-safe *perfect* models are exactly binary LCS with perfect tracial
states, i.e. the classical/LCS relaxation. The value version proved here is
that on the fixed AND gadget the affine-safe supremum is a constant below one:
the affine relaxation of the AND graph collapses it (the graph is genuinely
nonlinear, affine hull is the whole cube), so affine-safe strategies see at
most two of its four atoms.

## The mechanism, in one paragraph

The magic-square subgame is rigid: any strategy of value `1-eps` has, in its
synchronous state, `tau(A), tau(B), tau(AB)` all `O(sqrt(T eps))` from zero
(elementary trace-flip from the derived `AE=-EA`, `BD=-DB`,
`AD(AB)DA=-AB`). So the four `(A,B)` atoms are each near `1/4`. But:
- an affine-safe support holds at most two atoms (the AND graph has no affine
  subset of size three), so two near-`1/4` atoms are missing -> loss `>= 4/(9C0T)`;
- a canonical-corner pushforward is uniform on a flat, which either misses an
  atom (same bound) or is the full cube with every atom at `1/8 != 1/4` ->
  loss `>= 1/(9C0T)`.

## Numerics of the constant

`M=3`, `T=4^5*27*k=27648 k`. With a modest constraint count `k` of order a few
dozen and `C0` of order ten, `c* = 1/(9 C0 T)` is roughly `10^-8`: tiny but a
fixed, source- and family-independent constant. The value of the constant is
not optimized; only its constancy matters for (iii-c).

## Residual gap toward the root

The affine regime is now closed at a fixed threshold: no affine (in particular
no affine-safe) decoder can carry an affine-unsafe source above `1 - c*` on
CE models, so no constant-gap affine corner compiler for such a source has a
hyperlinear target. A route to `non-hyperlinear-group` must therefore use a
non-affine or randomized readout (break (2b)/(iii-b) of the ce-only floor
map), which this lane does not address. The linear robust tests (BLR, Pauli
braiding, low individual degree) are affine-readout and so certify only
affine-safe structure, consistent with the gap.

## Checks

- Affine-subset count of the AND graph `{000,010,100,111}`: `000+010+100=110`
  is disallowed, so the set is not a flat and contains no `2`-flat; every two
  points form a `1`-flat; the four points generate `F_2^3`. Hence max affine
  subset size `2`, and any proper flat omits an allowed atom. Verified by hand
  and by an exhaustive enumeration over the 8-point cube.
- Trace-flip identities: `EAE=-A+E(AE+EA)` gives `2 tau(A)=tau(E Delta)`,
  `|tau(A)| <= (1/2)||Delta||_2`; likewise for `B`, `AB`.
- No compute jobs were needed beyond the finite enumeration; no MSI jobs left
  running.

## Trust surface

`matrix-conj-forces-unsafe-support` (gadget, `M_4` uniqueness, `(UTC1)-(UTC5)`)
and `near-perfect-bcs-strategy-gives-synchronous-relator-state` (modulus `T`)
are consumed as stated, not re-derived. Thom's central-corner criterion is
consumed through `ce-exact-affine-compilers-nonhyperlinear-proof`. `C0` is
fixed but not minimized. Nothing here is independently reviewed.
