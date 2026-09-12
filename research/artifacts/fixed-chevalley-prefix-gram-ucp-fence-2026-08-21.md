# Fixed Chevalley prefix Gram matrices: the exact ucp fence

Let `S` be the eight root generators in Kassel's `C2` presentation and let
`U_n(s)` be unitary tuples whose presentation defects tend to zero in
normalized Hilbert--Schmidt norm.  The quarter-turn computation and the
rank-one braid computation now give fixed bounded-area derivations proving
that `z=w_beta^4` centralizes every root generator.  This note records exactly
what those derivations contribute to the ucp-lifting problem.

## 1. Every fixed prefix atlas is already positive

Fix root words `p_1,...,p_m` and put

```text
V_i=U_n(p_i),                 G_n(i,j)=V_i^*V_j.
```

For column vectors `xi_i in C^(d_n)`,

```text
sum_(i,j) <G_n(i,j)xi_j,xi_i>
  = ||sum_i V_i xi_i||^2 >= 0.
```

Thus `G_n` is exactly positive and `G_n(i,i)=I`, without using a single
Chevalley relation.  This is the free-group ucp lift in Gram form.

Suppose two atlas edges `(i,j)` and `(k,l)` have the same label in the
presented group, and a fixed derivation changes
`p_i^(-1)p_j` to `p_k^(-1)p_l` using conjugates of relators
`r_1,...,r_N`.  Telescoping and unitary invariance give

```text
||G_n(i,j)-G_n(k,l)||_2
   <= sum_(q=1)^N ||U_n(r_q)-I||_2.                     (1)
```

The constants are independent of `d_n`.  The explicit quarter-turn and
braid derivations therefore imply (1) for every repeated label in their
fixed prefix atlas.  If `L` denotes the affine subspace imposing diagonal
one and literal equality of repeated labels, then, with the normalized block
Hilbert--Schmidt norm,

```text
G_n >= 0,                    dist_2(G_n,L)=o(1).         (2)
```

Equivalently, if one replaces the repeated entries by any fixed linear
choice of common representatives, the resulting Hermitian matrix has
negative part of normalized `2`-norm `o(1)`: for a positive `G`, the
distance-to-the-positive-cone estimate
`||H_-||_2 <= ||H-G||_2` applies.  This is genuine **tracial positivity**.

## 2. The missing condition is an intersection, not another word identity

A ucp coordinate lift requires a matrix-valued positive-definite function
with literal label consistency.  On this atlas that means a matrix

```text
K_n in M_m(M_(d_n))_+ intersect L                         (3)
```

whose generator-labelled entries are `o(1)` from the prescribed
`U_n(s)`.  Relation defects prove (2), not (3).  The two evident corrections
do not compose:

* orthogonally projecting `G_n` onto `L` makes repeated labels equal but can
  create negative spectrum;
* replacing the projection by its positive part removes that negative
  spectrum but generally changes equal labelled entries independently and
  leaves `L`.

Therefore the required new estimate is a dimension-uniform regularity bound
for this particular noncommutative Chevalley positive cone/affine-space
intersection.  The positive-cycle lemma consumes such a `K_n`; it does not
construct one from (2).

There is also no fixed ordinary Choi matrix hidden here.  For a map from the
finite root-generator operator system into `M_(d_n)`, complete positivity is
tested at matrix levels growing with the target dimension (Smith's criterion
makes `d_n`-positivity sufficient).  A fixed prefix atlas controls only a
fixed matrix level.  Coherence over increasing word sets is the
positive-definite-kernel formulation of the same missing lift.

This can be sharpened.  Let

```text
E=span{1,u_s,u_s^*:s in S} subset A_alpha
```

and define the unital star-linear coordinate map `psi_n:E -> M_(d_n)` from
chosen representatives of `Theta(u_s)`.  For every fixed `k` and every
`X in M_k(E)_+`,

```text
[(id_k tensor psi_n)(X)] = (id_k tensor Theta)(X) >= 0
```

in the tracial quotient.  Hence

```text
||((id_k tensor psi_n)(X))_-||_2 -> 0.                  (4)
```

Because `E` and `k` are fixed, the positive unit ball is norm compact and
the `psi_n` have a uniform linear norm bound determined by the chosen basis.
A finite-net argument makes (4) uniform on that ball.  Thus a hypothetical
Maslov ultraproduct model already satisfies every fixed Choi test in the
only tracial sense available.  If no nearby ucp maps exist, the separating
matrix-positive witnesses must occur at levels `k_n -> infinity` (one may
take `k_n <= d_n` by Smith's criterion).  In particular, adding finitely many
fixed root-word centrality Gram matrices cannot close the liftability seam.

## 3. Averaging over root subgroups is circular at the mixed cell

Each root subgroup is cyclic.  On one such subgroup a chosen unitary gives
an exact star-homomorphism, and its positive kernel may be averaged without
difficulty.  But the eight root subgroups generate `Sp_4(Z)`.  A kernel which
is simultaneously invariant under left translation by every root subgroup
is invariant under the entire group.  Writing

```text
F_n(g)=K_n(e,g)
```

then gives the global matrix-valued positive-definite function, hence by
Stinespring the desired ucp map on the twisted group C-star algebra.

Successive root-subgroup averages need not commute: averaging over a new
noncommuting root can destroy invariance under the previous one.  The mixed
Chevalley conjugation identities describe this failure but do not supply a
common invariant mean or a uniform convergence rate.  Property (T) can
repair an almost-invariant corner only **after** a genuine Stinespring
representation has been obtained; it cannot manufacture (3).

## 4. Exact conclusion

The fixed root-word centrality derivations give all fixed prefix Gram
matrices tracial positivity and bounded label-consistency error.  They do not
imply the honest simultaneous positivity condition (3).  Proving a
dimension-free correction from (2) to (3), coherently as the atlas grows, is
an equivalent concrete form of the remaining Maslov generator-liftability
problem.  No approximate defect gap follows from the present calculation.
