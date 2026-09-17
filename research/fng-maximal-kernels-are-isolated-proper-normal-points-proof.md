---
rg: 2
id: fng-maximal-kernels-are-isolated-proper-normal-points-proof
kind: route
title: Read finite normal generators off a basic Chabauty neighbourhood and use maximality to shrink the neighbourhood to a point
target: fng-maximal-kernels-are-isolated-proper-normal-points
requires: [fp-quotient-iff-kernel-finitely-normally-generated]
---

Throughout, `Gamma` is finitely generated, so it is the normal closure of a
finite set `T`.

**Properness is clopen.**  `{N : N = Gamma} = U(T, empty)` is open, and it
is closed because it is a single point of a Hausdorff space.  So the set
`N_*(Gamma)` of proper normal subgroups is clopen.  When `Gamma = <<s>>`,
`N_*(Gamma) = U(empty, {s})`.

**(1)**  Suppose `N` is isolated, say `U(F, E) cap N(Gamma) = {N}` with
`F subset N` finite and `E cap N = empty`.  Put `N' = <<F>>_Gamma`.  Then
`F subset N'`, and `N' <= N`, so `N' cap E = empty`.  Thus
`N' in U(F, E)`, hence `N' = N`, and `N` is finitely normally generated.

**(2)**  One direction is (1).  Conversely, let `M in Max(Gamma)` with
`M = <<F>>` for a finite set `F`.  Consider the open set
`V = U(F, empty) cap N_*(Gamma)`.  If `N in V`, then `M = <<F>> <= N` and
`N` is proper, so `N = M` by maximality.  Hence `V = {M}` is open and `M`
is isolated.

**(3)**  `Gamma` is countable, so it has countably many finite subsets and
countably many normal closures of finite subsets.  By (1), `Iso(Gamma)` lies
in this countable set.

For the second sentence, the kernel of a surjection onto a nontrivial simple
group is a maximal proper normal subgroup, and conversely.  By
[[fp-quotient-iff-kernel-finitely-normally-generated]], the simple quotient
`Gamma/M` of a finitely presented `Gamma` is finitely presented if and only
if `M` is finitely normally generated.  By (2) this holds if and only if
`M in Iso(Gamma)`.  This is the only use of that node, and only the finitely
presented reading needs it.

**(4)**  Let `M in Max(Gamma)` be finitely normally generated with
`M in supp(mu)`.  By (2), `{M}` is open.  An open set that meets the support
has positive measure, so `mu({M}) > 0`.  Therefore all finitely normally
generated maximal kernels in the support are atoms.  The non-atomic part
`mu_c` vanishes on every singleton.  The set of these kernels is countable
by (3), so `mu_c` vanishes on it.

**(5)**  If `M` is finitely normally generated, then `{M}` is open by (2).
So every sequence converging to `M` is eventually equal to `M`.  This
contradicts the assumption that `N_i != M` for all `i`.  For a subset `K` of
`N(Gamma)` with no isolated points of its own, every `M in K` is a limit of
points of `K \ {M}`.  Because `N(Gamma)` is metrizable, this limit can be
taken along a sequence, so the first sentence applies.

**(6)**  `gNg^{-1} = N` for every `N` normal, so the conjugation action on
`N(Gamma)` is the identity.  Invariance and stationarity are then automatic.
If `mu` is ergodic for the trivial action, every Borel set is invariant and
has measure `0` or `1`.  A `0`--`1` valued Borel probability measure on a
second-countable Hausdorff space is concentrated on one point.  To see this,
intersect the full-measure members of a countable base with the
complements of the null ones.  Conversely, Dirac masses are ergodic.
`∎`
