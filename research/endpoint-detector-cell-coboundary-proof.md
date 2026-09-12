---
rg: 2
id: endpoint-detector-cell-coboundary-proof
kind: route
title: Transport the endpoint detector cube and compute its unchanged profile Grams
target: endpoint-detector-cell-retains-coboundary-gauge
requires:
  - five-return-legs-cover-hecke-detectors-not-source-gauge
  - endpoint-whitehead-profile-has-maximal-gram-overlap
---

Write

```text
c_m=s_(0^(m+1))t_(0^m),       d_m=s_(0^m)t_(0^(m+1)),
What_m=x_(r_(m+1),r_m)(c_m)
       x_(r_m,r_(m+1))(d_m)
       x_(r_(m+1),r_m)(c_m).
```

Prefix cancellation gives

```text
c_md_m=e_(m+1),       d_mc_m=e_m,
a_md_m=a_(m+1),       c_mb_m=b_(m+1).                 (1)
```

The ordinary non-opposite Steinberg collection used for the original
prefix Whiteheads therefore gives `(EDC2)`.  The same calculation gives
`What_m^2=1`; on three consecutive endpoint coordinates the two words are
the standard adjacent partial swaps, so they satisfy the Coxeter braid.
All their root factors avoid endpoints `1,3`, hence commute with `z` and
preserve its negative carrier.  Also

```text
[A_m,B_m]=x_13(a_mb_m)=x_13(q)=z.                     (2)
```

For the selected representative the only entry incident to
`Y_3=x_(9,3)(b_3)` is `E_(2,9)`, and elementary collection gives
`[g_3,Y_3]=x_(2,3)(b_3)`.  Start at this exact depth-three return and define
all earlier occurrences by reverse conjugation.  For any group elements
`w,x,y`,

```text
w[x,y]w^(-1)=[wxw^(-1),wyw^(-1)].                    (3)
```

Equations `(2)--(3)` prove `(EDC4)`.  If `Q_3` is the corresponding moved
signed source and `g_3Q_3=lambda_0(g_3)Q_3`, conjugating this equality gives

```text
g_mQ_m=lambda_0(g_3)Q_m.                              (4)
```

Thus no source assertion is discarded; its frame is moved literally.

Now index the six moved frames by `h in S_3`, set
`Q_h=What_hQWhat_h^(-1)`, and compress an adjacent word.  Equation `(EDC5)`
follows immediately.  Its initial and final Grams are respectively `Q_h`
and `Q_(s_i h)`.  At a fixed target both incoming final Grams are therefore
the identical projection, so the cross Gram is a unitary between the two
source spaces and has Hilbert--Schmidt square `tau(Q_h)`.  This is exactly
the maximal-overlap computation in
`endpoint-whitehead-profile-has-maximal-gram-overlap`; inserting `(3)` into
the transported packet does not alter it.

For the sharp gauge fence, take the direct sum of six copies of one exact
seed endpoint-cell space, indexed by `h in S_3`.  Put the `h`-conjugate of
the seed detector, probe, source projection and nested return on the
`h`-block.  Let each adjacent Whitehead permute the blocks by left
multiplication and apply the corresponding fixed adjacent Pauli swap.
Equations `(3)--(4)` show that this block permutation implements every
detector and signed-source covariance exactly.  The two block permutations
are the nontrivial adjacent transpositions in the regular representation of
`S_3`; the induced chart factors are `V_(s_i h)V_h^(-1)`, so every closed
profile word telescopes.  This realizes the complete scoped table with an
unremoved factor-level gauge and proves the claim.
