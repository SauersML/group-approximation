---
rg: 2
id: surjunctivity-of-a-local-class-is-reflection-kernel-membership
kind: claim
title: A local approximation class is surjunctive iff every strict datum has a reverse word in the kernel of its reflection
distinct_from:
  surjunctivity-is-axiomatized-by-rectangle-clauses: that is the case of the class of all groups, where the kernel is the normal closure of the forward relators; this is the same membership test for any class closed under subgroups, finite products and local embeddability, with that class's reflection kernel in place of the normal closure.
  strict-reverse-words-lie-in-bounded-width-profinite-closures: that is the instance of the weakly sofic class, with the kernel computed explicitly; this is the general membership test, which needs no explicit kernel.
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

**ESTABLISHED** by `surjunctivity-of-a-local-class-reflection-proof`.

**Statement.** Let `C` be a class of groups closed under subgroups, finite direct products and local embeddability.
For a strict rectangle datum `D`, let `N_C(D)` be the intersection of all normal subgroups `M` of the free group
`F(D)` that contain the forward relators and have `F/M` in `C`. Then:
- `F/N_C(D)` is in `C`;
- every group in `C` is surjunctive iff `W_r(D) ∩ N_C(D)` is nonempty for every strict `D`, where `W_r(D)` is the
  set of reverse words.

**Instances** (artifact, Proposition 2.5). The class of all groups, and the classes LEF, sofic, `F`-linear sofic and
weakly sofic, give nested kernels:

```text
N  ⊆  N_ws  ⊆  N_lin(F)  ⊆  N_sof  ⊆  N_lef  ⊆  cl(N) .
```

The rungs:
- Gottschalk's conjecture asks for a reverse word in `N`.
- `metric-ultraproducts-of-finite-groups-are-surjunctive` asks for one in `N_ws`
  (`weak-sofic-reflection-kernel-is-bounded-width-closure`).
- `linear-sofic-groups-are-surjunctive` over `F_p` asks for one in `N_lin(F_p)`.
- Gromov–Weiss supplies one in `N_sof`.
