---
rg: 2
id: finite-clopen-type-stays-finite-in-cantor-crossed-product
kind: claim
title: For minimal topologically free Cantor actions, a clopen set with finite type-semigroup class gives a finite projection in the reduced crossed product
distinct_from:
  cantor-crossed-product-with-finite-type-is-mixed: that asks for one mixed example; this is the general persistence principle that would produce it from any finite clopen class without invariant measures.
  kmp-plain-paradox-groupoid-dichotomy: that is the forward dichotomy under plain paradoxes; this is a converse-type rounding statement with no monoid hypothesis.
---

Let `Gamma` act minimally and topologically freely on the Cantor space `X`,
and let `U` be clopen.  If `[1_U]` is finite in `S(X, Gamma)`, then `1_U` is a
finite projection in `C(X) rtimes_r Gamma`.

## Attempts

* **States cannot reach it.**  With an invariant measure of full support the
  claim is trivial, via the faithful trace `mu o E`.  The relevant case has no
  invariant measure, so `S(X, Gamma)` has no state
  (`kmp-plain-paradox-groupoid-dichotomy`) and the tracial route of KMP
  Theorem B(4) gives nothing.
* **Topological freeness is necessary.**  Boldrini--Prasad (arXiv:2607.01896,
  Theorem 7.4 and its proof, p. 27) let `⊕_N F_infinity` act through the first
  coordinate, `alpha(g_0, g_1, ...)x = alpha'(g_0)x`.  The type semigroup is
  unchanged, but the crossed product is Z-stable and traceless, hence purely
  infinite.
* **Products give no counterexample.**  Z-stabilizing by a topologically free
  product kills the finite class
  (`product-with-divisible-cantor-action-kills-finite-type`).
* **Nuclear cases are excluded anyway.**  Amenable minimal actions of groups
  containing `F_2` have comparison (GGKN, recorded on the target claim).
* **Fractional transport, where a proof must work.**  An isometry `v` with
  `v*v = 1_U`, `vv* < 1_U`, approximated by a finite sum `w`, gives for each
  `x` a kernel `T_x(y, z) = |<pi_x(w) delta_y, delta_z>|^2` on the orbit.  Its
  row sums are `E(w*w)` (close to `1_U`), its column sums are `E(ww*)` (at most
  `1_U + eps`), and the column deficiency is nonzero on an open set.  All data
  are locally constant in `x`.  A proof must round such continuous fractional
  compressions into clopen-piecewise injections.  Obstructions to continuous
  perfect matchings in Cantor systems (Gao--Jackson--Krohne--Seward) show that
  such rounding is not automatic; where it dies is not yet located.

If false, some topologically free minimal Cantor action has a finite clopen
class that becomes infinite analytically.  If true, it gives
`cantor-crossed-product-with-finite-type-is-mixed` via
`cantor-crossed-product-mixed-via-finite-type-persistence`.
