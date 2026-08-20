---
rg: 2
id: finite-overgroups-cannot-kill-schur-character-density-gap
kind: claim
title: No finite overgroup can force a nonzero Schur character-density gap to vanish
distinct_from:
  finite-selector-gadget-induction-barrier: that says every compatible selector character survives in a representation of a finite overgroup; this applies it to the explicit character-density difference and rules out the entire finite density-return strategy.
  termwise-finite-reynolds-holonomy-has-zero-rank-gap: that obstructs a termwise conjugacy of adjoint Reynolds averages; this needs no proposed holonomy and constructs an exact counterrepresentation for every finite overgroup.
  schur-predicate-is-character-density-difference: that identifies the gap with the predicate projection; this proves finite extensions cannot make that gap a defining representation law.
---

Let `f` be a nonzero Boolean predicate, let `C_f<=B_f` be its Schur packet
inclusion, and let `K` be any finite group containing `B_f` with the packet's
involution `J` still central and nontrivial. Then `K` has a finite-dimensional
representation `rho` such that

```text
rho(J)=-I,
rho(Z_(C_f)-Z_(B_f)) != 0.                            (FOG1)
```

Equivalently, no finite overgroup can impose `Z_(C_f)=Z_(B_f)` on all of its
negative-sector representations. This remains true after adjoining arbitrary
finite selector translations, radical flips, or additional finite packet
charts.

Therefore the exact local payment identity

```text
tau(P_f)=4D^2||Z_(C_f)-Z_(B_f)||_2^2
```

cannot be closed by one finite group gadget. A viable return must use an
infinite/finitely presented mechanism—such as a one-sided compressor,
recursive computation, or genuinely higher-dimensional holonomy—and its
soundness must be quantitative for approximate finite-dimensional
representations.
