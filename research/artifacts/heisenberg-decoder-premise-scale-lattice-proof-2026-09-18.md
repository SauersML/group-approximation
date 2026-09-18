# Combine the cyclic Leavitt floor with the Schatten collapse, corona lifting and the full-support core

*Attempt artifact (2026-09-18), formerly route `heisenberg-decoder-premise-scale-lattice-proof` into `heisenberg-decoder-premise-scale-lattice-is-two-valued`, requires [coherent-heisenberg-decoder-is-marked-nonhyperlinearity, torsion-normal-generator-has-full-support-corona-core, binary-leavitt-elementary-group-is-simple]. Demoted from the graph at landing because the swarm-0917 referee stage returned no votes for this established result (votes lost), so it has not survived review. Restore it as a route once a full referee pass survives.*

Throughout, `tr` is normalized trace on `M_k`, `||X||_p=(tr|X|^p)^(1/p)`,
and every word evaluated on unitaries satisfies `||w(U)-I||_op<=2`.

## (E) Emptiness principle

Let `P` be a nonzero projection, with contractions `S_i,T_i` on `P`, and
`tau_P=tr(P . P)/tr(P)`.  The established audit
`coherent-heisenberg-decoder-is-marked-nonhyperlinearity` proves

```text
1 <= ||T_0S_0-P||_(2,P)+||T_1S_1-P||_(2,P)+||S_0T_0+S_1T_1-P||_(2,P).   (CHD3)
```

The proof uses only cyclicity and Cauchy--Schwarz on the finite corner.  It
does not use `tr P` or the dimension.  Since `||X||_(2,P)<=||X||_op`, the
same floor bounds operator-norm output defects.  Hence no sequence of corners
satisfies `(CHD1)-(CHD2)`, and `D_z^Pi` has no witness for any member of
`Pi`.  So `D_z^Pi` is true iff `Pi` has no members.

## (L1) Exact scale

A nontrivial finite-dimensional unitary representation of the simple group
`H` (`binary-leavitt-elementary-group-is-simple`) is faithful.  `H` is
finitely generated, because `R` is a finitely generated ring and `n=20>=3`.
So `H` would be a finitely generated linear group, hence residually finite by
Malcev.  An infinite simple group is not residually finite, so
`Pi_exact(H)` is empty and `D_z^exact(H)` is vacuously true.  An exact
representation is an operator-norm asymptotic representation with zero
defect, so `Pi_exact(G) subset Pi_op(G)`.

## (L2) Normalized Schatten scales

Let `||X||_op<=2`.  For `1<=p<=2`, Hoelder for the normalized trace and
`tr|X|^2<=||X||_op^(2-p) tr|X|^p` give

```text
||X||_p <= ||X||_2 <= 2^(1-p/2) ||X||_p^(p/2).
```

For `2<=p<inf`, `tr|X|^p<=||X||_op^(p-2) tr|X|^2` gives

```text
||X||_2 <= ||X||_p <= 2^(1-2/p) ||X||_2^(2/p).
```

Apply this to `X=r(U_n)-I` for relators `r` and to `X=z(U_n)-I`.  Defects
tend to zero in `||.||_p` iff they do in `||.||_2`, and `z` stays separated
in one iff in the other.  So `Pi_(S_p)(G)=Pi_HS(G)` for all `p in [1,inf)`.

`Pi_HS(G)` is empty iff `z` dies in every tracial ultraproduct model, i.e.
`z in Rad_hyp(G)`, i.e. `Rad_hyp(G)=G` by normal generation.  For `H`,
simplicity makes this nonhyperlinearity, as in the established audit.

With the trace profile `tr U_n(g)->delta_e(g)` as an extra premise
constraint, the class is contained in `Pi_HS(H)`.  Conversely, a member of
`Pi_HS(H)` makes `H` hyperlinear by simplicity.  Hyperlinear groups have
`delta_e` microstates (the standard Radulescu--Pestov amplification), and
along those `||z(U_n)-I||_2->sqrt 2`.  So both classes are empty
simultaneously.

## (L3) Operator-norm scale

Let `Pi_op(G)` be the sequences whose relator defects tend to zero in
operator norm, with `liminf_n ||z(U_n)-I||_op>0`.

Given a member of `Pi_op(G)`, the coordinates define a homomorphism
`G->U(prod_n M_(k_n)/directSum_n M_(k_n))` with `z` not in its kernel.
Relators vanish in the corona norm `limsup_n`.

Conversely, a norm-corona homomorphism `rho` with `rho(z)!=1` has unitary
coordinate lifts, because unitaries of the corona lift to unitaries in large
coordinates by polar decomposition.  Its relator defects tend to zero, and
`limsup_n ||z(U_n)-I||_op>0`.  Passing to a coordinate subsequence gives a
member of `Pi_op(G)`.

Thus `Pi_op(G)` is empty iff `z in Rad_MF(G)` iff `Rad_MF(G)=G`, since
`Rad_MF` is normal and `z` normally generates.  For `G=Delta` this is the
literal goal `property-t-free-leavitt-full-mf-radical`.

## (L4) Full-support mixed scale

Let `Pi_(op,HS)(G)` be the sequences with operator-norm relator defects
tending to zero and `liminf_n ||z(U_n)-I||_2>0`.  Operator-norm defects
dominate normalized HS defects, and `||X||_2<=||X||_op`.  Hence

```text
Pi_(op,HS)(G) subset Pi_op(G) intersect Pi_HS(G).
```

Conversely, suppose `Pi_op(G)` is nonempty.  Then `z` survives in a corona
representation.  `torsion-normal-generator-has-full-support-corona-core`
applies with `a=z`, `m=2`: `G` is finitely generated and normally generated
by `z`.  It reblocks the representation to an operator-norm asymptotic
representation `sigma_n` with `A_n=sigma_n(z)` an involution.  The rank of
`p_n=1_(-1)(A_n)` satisfies `rank(p_n)/k_n>=c>0`, so

```text
||A_n-I||_2^2 = 4 rank(p_n)/k_n >= 4c.
```

Thus `sigma_n in Pi_(op,HS)(G)`.  So `Pi_(op,HS)(G)` is empty iff `Pi_op(G)`
is empty iff `Rad_MF(G)=G`.

## (C) The consuming route

In `property-t-free-leavitt-via-full-support-hs-decoder`, the decoder is
applied to the reblocked `sigma_n`, a member of `Pi_(op,HS)`.  By `(E)` and
`(L4)`, the decoder restricted to the inputs the route consumes is
equivalent to `Rad_MF(G)=G`, which is the route's own target.

The stated decoder is `D_z^HS`.  By `(L2)` it is equivalent to
`Rad_hyp(G)=G`.  It implies the goal, because
`Pi_(op,HS) subset Pi_HS`.  For `H`, it is nonhyperlinearity of an explicit
group.

The requirement `tracial-projective-hilbert-hotel-cancellation` only
re-proves the impossibility of the output that `(CHD3)` already gives.
Hence the route contains no step strictly between its hypotheses and its
conclusion.

## Death step

The invariant is the pair (output impossible by `(CHD3)` at every scale,
premise class `Pi`).  `(E)` turns the decoder into "`Pi` is empty".  By
`(L1)-(L4)`, every scale in the lattice gives one of three statements:

```text
vacuous (exact, H)   <=   goal (op, op/HS)   <=   Rad_hyp(G)=G (normalized S_p, delta_e).
```

The only one sufficient for the consumer is the goal itself.  Any
premise-scale shift of a Leavitt-corner decoder dies at this step.  Useful
replacements must change the output to an inhabitable finite-matrix
estimate with a fixed finite relator window and constant.
