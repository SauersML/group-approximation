---
rg: 2
id: native-bs-commutator-level-proof
kind: route
title: Iterate the exact fourth-power conjugacy before imposing the level
target: bs14-one-power-level-is-a-native-short-commutator
requires:
  - regular-bs14-cores-admit-dyadic-one-power-shadows
---

Induction on `K` in the exact BS relation gives

```text
r^K s r^(-K)=s^(4^K).                                (NCP1)
```

Indeed the case `K=1` is `(NSC1)`, and conjugating the `K`th identity by
`r` replaces `s^(4^K)` by `(s^4)^(4^K)=s^(4^(K+1))`.
Multiplication by `s^(-1)` proves `(NSC2)`, hence the equivalence in
`(NSC3)`.  The reduced word `r^K s r^(-K)s^(-1)` has `K+1+K+1=2K+2`
letters.

For the dyadic shadow, `(DYS3)` says

```text
(S')^(4^K-1)=1.
```

Its core relation is exact, so `(NSC2)` gives `[R'^K,S']=1` with no
additional error.  Conversely adjoining the commutator row to the exact
Iwahori/BS presentation forces the same power row and therefore defines the
same finite quotient.

For arbitrary unitary pairs, ordinary telescoping gives

```text
||[R^K,S]-[R_0^K,S_0]||_2
 <=2K||R-R_0||_2+2||S-S_0||_2.                       (NCP2)
```

Thus even the native short row has an `O(K)` generic word-Lipschitz loss.
No approximate estimate was used in the induction itself.  If `(NSC1)` has
defect instead of holding exactly, rewriting through the iterated powers may
incur the still worse fourth-power conditioning loss.  These facts are why
the exact identity improves presentation geometry but does not alter the
moving-basin conclusion.
