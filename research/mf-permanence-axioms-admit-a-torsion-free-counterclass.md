---
rg: 2
id: mf-permanence-axioms-admit-a-torsion-free-counterclass
kind: claim
title: The permanence and finite-presentation properties of MF are satisfied by a class containing every torsion-free group, so they cannot imply a torsion-free transfer
distinct_from:
  mf-universal-horn-obstruction: that exhibits one finite quasi-identity satisfied by every MF group and violated by the marked tuple, a positive tool for proving non-MF; this exhibits a class satisfying the permanence axioms and containing every torsion-free group, a negative result about what those axioms can prove.
  mf-relation-closure: that organizes the MF radical as a closure operator and reads non-MF as a gap between semantic and group-theoretic consequence; this is a statement about a different class entirely and about the deductive strength of an axiom list, not about the MF radical.
  full-mf-radical-groups-form-an-extension-colimit-class: that computes the closure properties of the full-MF-radical class, a fact about MF; this exhibits an unrelated class with the closure properties of MF itself, in order to show what those properties do not entail.
artifacts:
  - research/artifacts/homomorphic-image-transfer-obstruction-2026-09-08.md
---

**ESTABLISHED.**  Let `K` be the finitely presented group of
`full-mf-radical-seed-has-no-torsion-free-quotient` and put

```text
C_K = { L : every homomorphism K -> L is trivial }.                   (CK1)
```

Then `C_K` has all of the following:

1. it contains every MF group and every torsion-free group;
2. it contains every finite group, every residually finite group, and every
   directed union of residually finite groups;
3. it is closed under subgroups, arbitrary direct products, directed unions
   and arbitrary directed colimits;
4. it is closed under extensions: if `1 -> N -> G -> Q -> 1` is exact with
   `N, Q in C_K`, then `G in C_K`;
5. non-membership localizes to a finite presentation: if `L = F/R` is finitely
   generated and `L not in C_K`, then `F/<<R_0>> not in C_K` for some finite
   `R_0 subset R`;
6. `K` itself is a nontrivial finitely presented group **outside** `C_K`, and
   every homomorphism from `K` into a member of `C_K` is trivial.

And there is **no torsion-free group outside `C_K`**, by 1.

**What this rules out.**  Reading "MF" as "`C_K`" satisfies each of the listed
permanence and localization properties, and admits `K` as a strongest-form
negative input, while making the torsion-free transfer statement false: there
is no torsion-free group outside the class at all.  So no derivation of a
torsion-free transfer from those properties alone can be valid.  Any
affirmative transfer theorem must use something specific to norm matrix
models.

**Two things to keep straight.**

- `C_K` satisfies *more* than MF, not less.  MF is closed under neither
  extensions (`mf-extension-nonclosure`) nor quotients
  (`mf-quotient-nonclosure`), while `C_K` is extension-closed.  Extra
  properties do not disqualify a counterclass -- a derivation from a subset of
  the axioms is still a derivation -- so this strengthens the conclusion rather
  than weakening it.  `C_K` is not quotient-closed either: free groups lie in
  it and `K` is a quotient of one.
- This is a statement about which ingredients a proof may use, not an
  impossibility theorem about MF.  It says nothing about whether a torsion-free
  transfer is true, and in particular leaves
  `free-abelianized-cover-reflects-mf` open.
