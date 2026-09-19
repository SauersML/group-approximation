---
rg: 2
id: fp-forces-hnn-edge-into-free-entropy-obstruction
kind: claim
title: The amalgam edge is MF but not finitely presented, and finite presentation forces an HNN edge that reintroduces the free-entropy obstruction
distinct_from:
  gkmp-closes-fp-mf-completeness-modulo-hnn-and-separability: that noted an HNN form of GKMP is needed and left it as plausibly-adaptable; this proves the HNN form faces the free-entropy obstruction that GKMP's amalgam form avoids, so it is not a routine adaptation.
  digit-edge-mf-is-a-free-entropy-model-uniqueness-question: that identified the model-uniqueness content of the digit edge; this pinpoints WHY the amalgam tool does not remove it, namely the tension between finite presentability and the amalgam form.
---

ESTABLISHED (as an analysis of the two edge forms; each clause is proved).

Write the Higman-rope insertion data as: `G` an MF exact group, `L <= G`
separable, `C` residually finite MF, `phi : L -> C` a homomorphism.  Two
groups are in play.

**Amalgam edge.**  `G *_L (L x C)` is MF by
[[gkmp-amalgam-product-mf-permanence]].  In its MF proof no unitary conjugates
two different models of `L`: the copy of `L` is *shared* (amalgamated), and
`C` is attached as a commuting product `L x C`.  This is exactly why GKMP's
selflessness argument goes through and the free-entropy non-uniqueness of
[[digit-edge-mf-is-a-free-entropy-model-uniqueness-question]] does not bite.
But `G *_L (L x C)` is **not finitely presented** when `C` is only recursively
presented (`C = B2(S_e)`), so it cannot be the reduction's output `P_e`.

**HNN edge.**  The finitely presented Higman output is the rope

```text
R = < G x C, s | s (l,1) s^-1 = (l, phi(l)),  l in L >.               (FE1)
```

Its finite presentability is the whole content of the Higman embedding
theorem (the machine makes `C`'s infinitely many relators derivable through
`s`).  In any MF realization `rho` of `G x C` with the regular trace, an `s`
implementing `(FE1)` must satisfy

```text
s rho(l,1) s^* = rho(l, phi(l))     for all l in L,                   (FE2)
```

so `s` is a unitary conjugating the model `l -> rho(l,1)` of `L` to the model
`l -> rho(l, phi(l))`.  Both models carry the regular character of `L`
(`tr(l,1) = tr(l,phi(l)) = delta_{l,1}`), so `s` exists iff the two models are
approximately unitarily equivalent in the matrix ultraproduct.  For `L` free
of rank `>= 2` (the digit case, `L = < t, a_1, ..., a_{2n} >`) this is
precisely the free-entropy model-uniqueness question, which has no soft
answer and can fail.

## The dichotomy

```text
amalgam edge  G *_L (L x C):  MF (proven), but NOT finitely presented;
HNN edge      R of (FE1):     finitely presented, but its MF needs
                              two-model conjugacy of L = the free-entropy
                              obstruction.                            (FE3)
```

The finite-presentation `Pi^0_2`-completeness of MF sits exactly on this
tension.  Closing it requires one of:

1. an HNN form of GKMP's free-independence argument that produces the
   conjugating `s` for the specific rope data despite free-entropy
   non-uniqueness (using that `L` is separable in `G` and `phi` is the
   evaluation map, not a generic pair of models);
2. a different finitely presented compiler whose `INF`-branch output is a
   GKMP amalgam `G' *_{H'} (H' x C)` rather than an HNN, so that no two-model
   conjugacy is needed;
3. a proof that no such compiler exists, i.e. that MF is **not** finite-
   presentation `Pi^0_2`-complete (a negative resolution, still a resolution).

## Why (2) is not immediate

The rope output does not embed in `G *_L (L x C)`: an `s` implementing
`(FE2)` would conjugate `L <= G` to `graph(phi) <= L x C`, subgroups of
different vertex groups of the amalgam, which are not conjugate there.  And
the naive product amalgam `(G x C) *_{L x C} ((L x C) x Z)` shifts whole
copies of `G x C`, not `L x 1` to `graph(phi)` inside one copy.  So option
(2) needs a genuinely new compiler, not a re-bracketing of the rope.

## Status

This refines both the earlier pessimistic reading
([[digit-edge-mf-is-a-free-entropy-model-uniqueness-question]]) and the
subsequent optimistic one
([[gkmp-closes-fp-mf-completeness-modulo-hnn-and-separability]]): the GKMP
theorem is a real and relevant tool, but it does not by itself close the
prize, because its power is exactly in the amalgam form that finite
presentation cannot use.  The problem is genuinely open, and its three
possible resolutions are listed above.
