---
rg: 2
id: fournier-facio-group-contains-simple-wreath-shift
kind: claim
title: The Fournier--Facio group contains the wreath product of its simple factor by the compression shift
distinct_from:
  kun-thom-nonsofic-wreath: That is Kun--Thom's external theorem about lamplighter-type wreath products over coset spaces of infranormal Kazhdan pairs; this is an internal wreath product S wr Z found inside the torsion-free Fournier--Facio group itself.
  fournier-facio-torsion-free-skeleton: That records the published compression data (Gamma, t_1, J); this derives from those data the infinite family of pairwise commuting conjugates J_k, their independence, and the self-similar tail of Gamma.
  conjugate-commuting-perfect-copies-force-exponential-dimension: That is an exact dimension bound for representations containing commuting conjugate copies of a perfect group; this supplies, inside the Fournier--Facio group, an infinite family of such copies.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

**ESTABLISHED.**  Let `G`, `Gamma`, `t=t_1`, `S` and `J=t^-1 pi(S) t` be as
in `fournier-facio-torsion-free-skeleton`, and put

```text
J_k = t^k J t^-k                       (k in Z),  so J_0=J, J_1=pi(S).
```

Then:

```text
(W1)  J_k <= Gamma                               for k >= 1;
(W2)  [J_a,J_b] = 1                              for a != b;
(W3)  J_-k <= C_G(Gamma)                         for k >= 0;
(W4)  the multiplication map (+)_(k in Z) J_k -> G is injective;
(W5)  S wr Z = ((+)_Z S) x| Z embeds in G, the generator of Z going to t;
(W6)  Gamma x (+)_(k<=0) J_k <= G  is an internal direct product;
(W7)  Gamma >= J_1 x J_2 x ... x J_n x t^n Gamma t^-n,
      an internal direct product, for every n >= 1.
```

So the compression letter `t_1` acts on `(+)_Z S` as the shift.  The copies
with index `<=0` centralize the Kazhdan subgroup `Gamma`, the copies with
index `>=1` lie inside it, and each application of `t_1` moves one copy from
the centralizer into `Gamma`.  Clause (W7) is a self-similar tail: `Gamma`
contains one simple slot times a conjugate copy of itself, and iterates.  If
`S` does not have property (T), each inclusion in (W7) is proper, since
equality at `n=1` would make `S` a quotient of the Kazhdan group `Gamma`.

Proof: `fournier-facio-simple-wreath-shift-proof`.  The heredity of (W5) to
every nontrivial quotient is
`fournier-facio-nontrivial-quotients-contain-simple-wreath`.
