---
rg: 2
id: private-label-core-reselection-proof
kind: route
title: Peel private labels and define each pivot by exact composition
target: coherent-reselection-reduces-to-private-label-core
requires:
  - spherical-tight-single-colour-near-perfect-matching
  - spherical-relation-defect-pairs-small-chord
  - partial-schreier-completion-preserves-sofic-loss
  - trace-separation-sphere-distance-concentration
---

Write `r_(g,h,k)=k^(-1)gh` for the relator belonging to
`gh=k`.

## The multiplicity core is canonical

For a subfamily `A subset R_0`, count every literal label occurrence and
write

```text
deg_A(s)=sum_(r in A) occ_s(r).
```

Call `D subset R_0` *two-dense* if every label occurring in `D` has
degree at least two in `D`.

Fix any sequential peeling order and let `A` be its current relation
family.  The following invariant holds:

```text
every two-dense D subset R_0 is contained in A.          (PCR0)
```

It is true initially.  Suppose a relation `r` is deleted because
`deg_A(p)=1`.  If a two-dense `D subset A` contained `r`, then the
single occurrence of `p` in `A` would also be its single occurrence in
`D`, contradicting `deg_D(p)>=2`.  Thus `r notin D`, and deleting
`r` preserves `(PCR0)`.

A terminal family `K` is itself two-dense, since it has no positive
degree-one label.  Invariant `(PCR0)` says every two-dense subfamily is
contained in `K`.  Therefore `K` is the unique largest two-dense
subfamily.  Any two terminal peeling outputs contain one another and are
equal.

This proof uses occurrence multiplicity.  If a label occurs twice in one
relation and nowhere else, its degree is two, not one, so that label does not
make the relation peelable.

## Reverse the peeling order

Record a sequence of deletions which leaves the private-label core.  Reverse
that sequence.  When a deleted relation is restored, its recorded private
label `p` occurs in no relation which has already been restored and in no
core relation.  Hence no permutation has yet been assigned to `p`.

Some other labels of the restored relation may also be unassigned.  Choose
radius-`rho` near-perfect partial matchings for all of them except `p`.
The single-colour matching theorem permits these finitely many choices
simultaneously on the same cloud.  Every assigned map is therefore a partial
bijection with domain and range of size `(1-o(1))N`.

## Solve the restored relation for its private label

Suppose the restored equation is `gh=k`.  Since `p` occurs exactly once,
define its partial permutation on the maximal natural co-large domain by one
of

```text
tau_k = tau_g tau_h                 if p=k,
tau_g = tau_k tau_h^(-1)            if p=g,
tau_h = tau_g^(-1) tau_k            if p=h.             (PCR1)
```

Each expression is a partial bijection on `(1-o(1))N` points.  The restored
relation holds exactly wherever the displayed compositions are defined.
Previously restored relations remain exact because their label maps are never
changed.

Let `e_s` be the current pointwise shadow radius of `tau_s`, and assume

```text
||(U_gU_h-U_k)x_i|| <= zeta                         (PCR2)
```

off a set of density `eta`.  If `p=k`, the triangle inequality gives

```text
||x_(tau_g tau_h(i))-U_k x_i||
 <= e_g+e_h+zeta.                                     (PCR3)
```

If `p=g`, write `y=tau_h(i)`; then
`tau_g(y)=tau_k(i)`, and

```text
||U_g x_y-x_(tau_g(y))||
 <= ||U_g x_y-U_gU_hx_i||
    +||(U_gU_h-U_k)x_i||
    +||U_kx_i-x_(tau_k(i))||
 <= e_h+zeta+e_k.                                      (PCR4)
```

The case `p=h` follows by applying the same comparison through
`tau_g^(-1)`, and gives radius at most `e_g+zeta+e_k`.

Suppose the given core family is shadow-good off a set of density `theta`.
Because every table is finite, iterating these estimates produces a constant
`C_T` such that every restored label has radius at most
`C_T(e+rho+zeta)`.  Each step discards only finitely many preimages or
images of existing exceptional sets, so the total exceptional density is at
most `C_T(theta+eta)+o(1)`.

Labels which occur in no relation may be assigned independent tight
matchings at the end.  Complete every partial bijection arbitrarily.  The
completion changes only `o(N)` values, so every basis relation has Hamming
defect `o(1)` by
[[partial-schreier-completion-preserves-sofic-loss]].

## Restore redundant closing relations

Let `r in R`.  By hypothesis there is a fixed normal-closure expression

```text
r = product_(j=1)^L v_j r_(i_j)^(epsilon_j) v_j^(-1),
epsilon_j in {1,-1},                                  (PCR5)
```

where the `r_(i_j)` belong to `R_0`.  Evaluate `(PCR5)` in the
completed permutation table.  Bi-invariance of normalized Hamming distance
gives

```text
d_Ham(r(tau),1)
 <= sum_(j=1)^L d_Ham(r_(i_j)(tau),1)
 = o(1).                                                (PCR6)
```

Thus all tested relations, including fully old closing equations, hold
asymptotically.

If distinct labels `s,t` have regular-character trace separation, then
`trace-separation-sphere-distance-concentration` gives a fixed lower bound on
`||U_sx_i-U_tx_i||` outside `o(N)` roots.  The two constructed shadow radii
tend to zero, so `tau_s(i)=tau_t(i)` is impossible on every remaining common
domain root.  Arbitrary completion changes only `o(N)` values; hence the
completed permutations are Hamming-separated on `1-o(1)` roots.

Restriction of a full coherent family to the core is immediate, while the
reverse-peeling construction proves extension from the core.  If the core is
empty, start with no assigned maps and obtain the whole coherent family.
This proves the claimed reduction and the empty-core positive subclass.

The subclass is strictly larger than one-overlap forests: after defining
`c=ab`, the relation `ac=d` reuses both `a` and `c` but its private
label `d` is assigned by `tau_d=tau_a tau_c`; no coupled matching is
needed.
