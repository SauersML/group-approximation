---
rg: 2
id: heterogeneous-britton-row-has-regular-energy-floor
kind: claim
title: A heterogeneous Britton row has a positive canonical regular energy floor
distinct_from:
  hnn-compressed-row-is-unnamed-fixed-carrier: that turns a small compressed row into an approximate fixed carrier; this computes the row itself in the canonical regular representation and shows that making it small already excludes canonical microstates.
  deleting-one-gap-row-has-the-wrong-orientation: that obtains a lower bound from the finite-dimensional BCS gap after deleting a game row; this lower bound is the exact regular HNN norm and uses no game gap.
  finite-graph-packet-compression-wandering-no-go: that constructs exact finite Bass--Serre packet countermodels for representation-independent return identities; this applies to every nonzero group-algebra carrier and identifies the semantic target with non-hyperlinearity itself.
---

**ESTABLISHED.**  Let

```text
Gamma=<B,t | t A t^(-1)=C>
```

be an HNN extension, let `a in B\C`, let `b in B`, and let
`0!=p=p^*=p^2 in C[B]` satisfy `[b,p]=0`.  Put

```text
x=a t p-t p b in C[Gamma].                            (HBR1)
```

Then

```text
||x||_(2,L(Gamma))^2=2 tau_Gamma(p)>0.                (HBR2)
```

Consequently, for every canonical-trace matrix microstate sequence `U_n`
of any fixed finite presentation of `Gamma`,

```text
||a(U_n)t(U_n)p(U_n)-t(U_n)p(U_n)b(U_n)||_2^2
   ->2 tau_Gamma(p).                                  (HBR3)
```

In particular the vanishing row `(FHC1)` in
`fanizza-heterogeneous-compressed-row` cannot hold along even one canonical
microstate sequence.  Subject to the stated noncollapse conditions, proving
that every such sequence satisfies `(FHC1)` is therefore already equivalent
to proving that `Gamma` has no canonical microstates, hence is
non-hyperlinear.  It is not a weaker decoder lemma on the way to that
conclusion.

This also fences finite redundant-check proposals.  No dimension-independent
tracial inequality can derive `(FHC1)` from ordinary defining relators: the
left regular representation satisfies every such relator exactly while its
row energy is `(HBR2)`.  A proof using error-correcting consistency must use
a genuinely finite-matrix-only soundness theorem which fails in the regular
factor.  Establishing that theorem is precisely the missing non-hyperlinear
compiler, not a consequence of adding finitely many syntactic checks.

