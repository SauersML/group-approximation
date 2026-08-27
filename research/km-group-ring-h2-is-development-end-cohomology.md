---
rg: 2
id: km-group-ring-h2-is-development-end-cohomology
kind: claim
title: Group-ring second cohomology of a triangle colimit is the degree-one end cohomology of its development
distinct_from:
  triangle-colimit-rational-h2-vanishes: that treats rational and divisible coefficients, where the equivariant group is a finite cokernel of fixed-point spaces; this treats the integral group ring, where the equivariant group is compactly supported cohomology and the kernel condition becomes end cohomology.
  compact-hyperbolic-km-lattices-fail-lp: that is the open LP fork consuming `H^2(Lambda,Z Lambda)!=0` through Ioana--Spaas--Wiersma Corollary D; this identifies that input exactly, replacing the Brown identification that needed a contractible cocompact model.
  titz-witzel-lattices-fail-lp: that has `H^2(Gamma,Z Gamma)=H^2_c(X)` outright because the building is contractible and the action free; here the development may have `H_2(X)!=0`, and exactly the classes of `H^2_c(X)` orthogonal to all 2-cycles survive.
---

**THEOREM (established; proof in
`km-group-ring-h2-is-development-end-cohomology-proof`).**  Let `Lambda`
act cellularly, without inversions, with finite stabilizers and
cocompactly on a simply connected CW complex `X`.  Then

```text
H^2(Lambda; Z Lambda)
  =  ker( H^2_c(X;Z) --> H^2(X;Z) )
  =  H^1_infty(X;Z) := H^1( C^*(X;Z) / C^*_c(X;Z) ),            (GR1)
```

the first cohomology "at infinity" of `X`.  Concretely,
`H^2(Lambda;Z Lambda)` is the group of compactly supported integral
2-cochains on `X` that vanish on every 2-cycle of `X`, modulo
coboundaries of compactly supported 1-cochains; equivalently, the group
of integral 1-cochains with compactly supported coboundary, modulo the
compactly supported ones and the cocycles.

**Sufficient criterion (retract form).**  If there is a subcomplex
`K <= X` with `H_2(K;Z)=0` and `H^2_c(K;Z)!=0` (for instance a properly
embedded plane) together with a proper cellular retraction
`rho : X -> K`, then `H^2(Lambda;Z Lambda)` contains a copy of
`H^2_c(K;Z)` and is nonzero.  Proof: `rho^*` is injective on `H^2_c`
because `i^* rho^* = id`, and for a 2-cycle `z` of `X` one has
`<rho^* u, z> = <u, rho_* z> = 0` since `rho_* z` is a 2-cycle of `K`,
hence a boundary, and `u` is a cocycle.  This is exactly the
apartment-retraction argument of `titz-witzel-lp-failure-proof`, with
contractibility of `X` replaced by `H_2(K)=0` for the retract alone.

**Instance.**  For a developable triangle of finite groups with colimit
`Lambda` and development `X` (simply connected by Bridson--Haefliger
III.C.3.13), in particular for the simple Kazhdan Kac--Moody lattices
of `simple-kazhdan-kac-moody-lattices-exist` with their
Abramenko--Mühlherr Levi triangle, `(GR1)` holds verbatim.  Hence
Ioana--Spaas--Wiersma Corollary D fires at `Lambda_(2,4,6)(q)` exactly
when the development has nonzero degree-one end cohomology; that
statement is isolated as the open claim
`km-development-has-nonzero-end-cohomology-in-degree-one`, consumed by
`km-lp-fails-via-development-end-cohomology`.

**What this changes.**  The attempts of
`compact-hyperbolic-km-lattices-fail-lp` recorded that no model computes
`H^*(Lambda,Z Lambda)` because Brown's criterion needs a proper cocompact
contractible model, which `km-lattices-admit-no-cocompact-npc-model`
closes.  Contractibility is not needed: the proper cocompact simply
connected development already determines `H^2(Lambda,Z Lambda)` as a
purely topological invariant of `X` near infinity.  Nonvanishing of
`H^2_c(X)` alone is NOT enough when `H_2(X)!=0`: a compactly supported
class pairing nontrivially with some 2-cycle is invisible to the group.
