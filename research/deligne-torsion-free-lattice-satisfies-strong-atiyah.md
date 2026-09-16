---
rg: 2
id: deligne-torsion-free-lattice-satisfies-strong-atiyah
kind: claim
title: The torsion-free level-3 lattice in the universal cover of Sp_2n(R) satisfies Strong Atiyah over the algebraic numbers
distinct_from:
  level15-torsion-free-lattice-satisfies-strong-atiyah: that is a residually finite lattice in SL_3(Z), which lies in the permanence class T; this is a non-residually-finite central extension, and no group of the permanence closure contains it.
  master-host-satisfies-algebraic-strong-atiyah: that is Strong Atiyah for the universal torsion-free host; this is one finitely presented subgroup of it, a necessary test that isolates central Z-extensions of Kazhdan groups.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that records property (T) and non-residual-finiteness of the full preimage of Sp_2n(Z); this asks for Strong Atiyah for its torsion-free level-3 subgroup.
  strong-atiyah-torsion-free: that is the conjecture for every torsion-free group over the complex numbers; this is one explicit torsion-free Kazhdan lattice over the algebraic numbers.
artifacts:
  - research/artifacts/atiyah-permanence-closure-kazhdan-rf-2026-09-16.md
---

**OPEN.**  Let `n >= 2`, `p: G~ -> Sp_2n(R)` the universal cover,
`Gamma' = ker(Sp_2n(Z) -> Sp_2n(Z/3Z))` and `Lambda_n = p^-1(Gamma')`.  For
every `n >= 2` and every finite matrix `A` over `Qbar[Lambda_n]`,
`rk_(N(Lambda_n))(A)` is an integer.

`Lambda_n` is finitely presented, torsion-free, Kazhdan and not residually
finite (item 2 of `atiyah-permanence-closure-kazhdan-subgroups-are-rf`).  It
is a central extension `1 -> Z -> Lambda_n -> Gamma' -> 1`.

**Why it is a useful test.**  It is one necessary test case among several
finitely presented torsion-free non-residually-finite Kazhdan subgroups of the
master host (others: the Titz Mite--Witzel lattices of
`titz-witzel-simple-kazhdan-cat0-lattices-exist`).  Its special feature is that
both pieces of its central extension already satisfy Strong Atiyah.
- It follows from `master-host-satisfies-algebraic-strong-atiyah` through
  `deligne-lattice-atiyah-from-master-host`.  So a single non-integral rank
  over some `Lambda_n` refutes the target.
- No group containing `Lambda_n` lies in the closure of the residually finite
  and T-finite groups under subgroups, directed unions, graphs of groups,
  T-finite-quotient extensions and residual systems
  (`atiyah-permanence-closure-kazhdan-subgroups-are-rf`).  So no recorded
  permanence theorem gives it from those base classes, even through a larger
  group.
- Status: no source found proving it (arXiv search 2026-09-16, incomplete;
  see the artifact, Section 6).
- Both pieces of the extension satisfy Strong Atiyah.  `Gamma'` is a subgroup
  of the torsion-free compact 3-adic analytic group `CS(1,2n,3)`
  (`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`), and the
  kernel is `Z`.  The missing permanence is exactly central `Z`-extensions of
  a Kazhdan group satisfying Strong Atiyah.

## Attempts

- **Permanence from proved classes.**  Dead by
  `atiyah-permanence-closure-kazhdan-subgroups-are-rf`.
- **Approximation by quotients.**  Dead in the residual form.  If `Lambda_n`
  had a residual system of quotients in `T`, it would be in `T` by (C6).  So
  every residual system contains a non-residually-finite Kazhdan quotient.
  Finite quotients do not separate `2Z` in the kernel
  (`deligne-covers-of-sp2g-z-have-finite-residual-2z`, which passes to the
  finite-index subgroup `Lambda_n`).
- **Splittings.**  None.  `Lambda_n` has property FA, and every T-finite
  quotient of it is finite.
- **Central direct integral.**  Open, unchecked reformulation (artifact
  Section 5).  Decomposing over the dual circle of the centre writes
  `rk(A)` as `int_(S^1) rk_t(A_t) dt` over the twisted algebras
  `N(Gamma', t^c)`.  It would suffice to show that these twisted ranks are
  integers and almost everywhere constant in `t`.  The integer cocycle `c`
  is not a coboundary on any finite-index subgroup of `Gamma'`, so passing to
  finite index does not remove the twist for all `t` at once (an individual
  multiplier `t^c`, for instance at `t = 1`, can be trivial).  No twisted
  version of the Farkas--Linnell argument is recorded.
