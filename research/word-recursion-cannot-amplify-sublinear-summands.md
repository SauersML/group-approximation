---
rg: 2
id: word-recursion-cannot-amplify-sublinear-summands
kind: claim
title: Natural word recursion cannot amplify a reducing sublinear bad summand into macroscopic HS energy
artifacts:
  - research/artifacts/adversarial-error-delocalization-program-2026-08-21.md
distinct_from:
  hs-invisibility-inflation-no-go: that concerns padding a corona or MF witness; this proves a direct-sum naturality obstruction for arbitrary finite recursive word, polynomial, expander, or decoded test packets.
  marked-hs-separation-forces-spectral-density: that starts from a fixed marked-word separation and obtains macroscopic spectral mass; this proves that recursion alone cannot manufacture that mass from a reducing `o(d)` summand.
  sublinear-block-poisons-normalized-torsion: that exploits an unbounded spectral statistic on a tiny corner; this treats bounded normalized-HS test energy and shows why recursive copying still cannot make the corner visible.
---

Fix finitely many generators. At depth `L`, let

```text
D_L={F_(L,1),...,F_(L,N_L)}
```

be any finite packet of uniformly bounded matrix-valued star-polynomial or
word maps. It may contain recursive conjugates, self-similar copies, expander
walks, or decoded checks. Such maps are natural under direct sums:

```text
F(U direct_sum W)=F(U) direct_sum F(W).
```

If `V_n` is a `d_n`-dimensional bulk microstate, `W_n` is an arbitrary
`r_n`-dimensional tuple, `alpha_n=r_n/(d_n+r_n)->0`, and
`Z_n=V_n direct_sum W_n`, then for every fixed `L`,

```text
E_L(Z_n):=sum_j ||F_(L,j)(Z_n)||_2^2
 =(1-alpha_n)E_L(V_n)+alpha_n E_L(W_n).
```

If `||F_(L,j)||<=C_L`, the whole bad-block contribution is at most
`alpha_n N_L C_L^2`, even when the local predicate on `W_n` is maximally
false.

The statement remains true against a depth schedule chosen in advance. For
any finite packets `D_(L_n)`, one can choose increasingly accurate bulk
microstates, amplify each bulk by enough copies, and append one fixed bad block
so that the combined tuples are regular microstates, preserve the bad block
exactly, and have `E_(L_n)->0`.

The invariant reason is that the projection onto the bad block commutes with
every evaluated word. Recursive conjugation and adjoint expansion therefore
cannot move mass across that central reducing projection. A word expander has
spectral gap only relative to its fixed algebra, which already contains the
bad-block projection.

**Surviving positive hypothesis.** Error spreading can be useful only after an
independent mark gives `tau(p)>=beta>0`. A corner decoder inequality

```text
sum_j ||R_j p||_2^2 >= c tau(p)
```

then yields global energy at least `c beta`. Recursion can distribute existing
macroscopic mass; it cannot create it from a localized reducing defect.
