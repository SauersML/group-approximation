---
rg: 2
id: thompson-v-not-mf-via-lifted-thompson-t
kind: route
title: One word in T-bar settles V, so a single hole now feeds both deep inputs of the flagship
target: thompson-v-is-not-mf
requires:
  - lifted-thompson-t-is-not-mf
  - lifted-thompson-t-mf-radical-dichotomy
---

**Not a duplicate.**
- `property-t-free-seed-via-lifted-thompson-t` spends the same hole on the
  torsion-free seed.  This route spends it on Thompson's `V`, and so on the
  binary-Leavitt endpoint through `property-t-free-leavitt-via-thompson-v-not-mf`.
  The two routes share a single requirement, and that is the point.
- `thompson-v-full-mf-radical-from-nonhyperlinearity` reaches `V`'s full
  radical from nonhyperlinearity of `V`, a tracial (Hilbert--Schmidt) hole.
  This route reaches it from an operator-norm statement about a torsion-free
  central extension of `T`, and uses no trace.

**Chain.**
1. `lifted-thompson-t-is-not-mf` gives `z in Rad_MF(T̄)`, where `z(x) = x+1`
   is the central translation.
2. By item 2 of `lifted-thompson-t-mf-radical-dichotomy` (the one-word
   criterion), `z in Rad_MF(T̄)` is equivalent to `T̄` not being MF.
3. By item 3 of the same node (downward transfer), `T̄` not MF gives
   `Rad_MF(V) = V`.  In particular Thompson's `V` is not MF, which is the
   target `thompson-v-is-not-mf`. ∎

Every step is a quotation of an established statement.  Items 2 and 3 of the
dichotomy are proved in `lifted-thompson-t-mf-radical-dichotomy-proof`,
Steps 3 and 4.  Step 4 uses only three facts: `T <= V`, simplicity of `V`,
and heredity of MF to subgroups.  No step uses Property `(T)`, a trace or a
spectral gap.

## What this route changes

The graph already had the implication "`z in Rad(T̄)` gives `Rad(V) = V`".
It was stated in the dichotomy node and in the prose of
`property-t-free-seed-via-lifted-thompson-t`.  But no route edge carried it
into `thompson-v-is-not-mf`, which the checker listed as a hole with no live
routes into it.  So `bin/cairn impact lifted-thompson-t-is-not-mf` stopped at
the torsion-free branch.  This route supplies the missing edge.  With it the
flagship `property-t-free-manuscript-results` has a route whose only open leaf
is `lifted-thompson-t-is-not-mf`:

```text
lifted-thompson-t-is-not-mf
  -> thompson-v-is-not-mf                          (this route)
  -> property-t-free-leavitt-full-mf-radical       (property-t-free-leavitt-via-thompson-v-not-mf;
                                                    its other three inputs are established)
lifted-thompson-t-is-not-mf
  -> property-t-free-torsion-free-fp-non-mf-seed   (property-t-free-seed-via-lifted-thompson-t)
  -> property-t-free-torsion-free-full-mf-radical  (established embedding router)
both
  -> property-t-free-manuscript-from-leavitt-collapse -> property-t-free-manuscript-results
```

**Cost, restated.**  By the same item 3, the hole is at least as strong as
"`T` is not MF".  The companion route
`lifted-thompson-t-not-mf-via-central-eigencorners` shows it is exactly
"`T` is not MF" plus one operator-algebraic statement about the central
unitary `rho(z)`.  So the hole's content splits into a Thompson-`T` part and a
corona-commutant part, and each can fail on its own.
