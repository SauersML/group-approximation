---
rg: 2
id: subgroup-exact-outliers-do-not-exist
kind: claim
title: Finite-index-near-exact almost representations of a Kazhdan group are flexibly correctable
distinct_from:
  kazhdan-subgroup-weak-ucp-exactifies-microstates: that starts from weak ucp stability and makes a subgroup restriction exact; this starts with an exact finite-index restriction and corrects the whole ambient tuple by induction.
  close-normalized-characters-do-not-force-equivalence: that refutes correction by comparing normalized characters; the present proof never compares characters or irreducible multiplicities.
  sl3z-regular-microstates-are-congruence-correctable: that asks to correct arbitrary regular microstates of SL3(Z); this removes only the sharply delimited sector already exact on one fixed finite-index subgroup.
---

Let `G` be a finitely presented property-`(T)` group and let `N<=G` have
finite index.  Fix generators and relators for `G`.  Suppose

```text
sigma_j:S_G -> U(H_j)
```

has presentation defect tending to zero, and suppose there are genuine
representations

```text
pi_j:N -> U(H_j)
```

such that `sigma_j|_N` is `o(1)`-close to `pi_j` on one fixed generating
set of `N`.  (Exact agreement is the special case needed by the node's
original formulation.)

Then `sigma_j` is **flexibly Hilbert--Schmidt correctable**: there are exact
finite-dimensional representations

```text
alpha_j:G -> U(K_j),       dim(K_j)/dim(H_j) -> 1,
```

and, after identifying subspaces of codimension `o(dim H_j)` and
`o(dim K_j)`, the matrices `sigma_j(s)` and `alpha_j(s)` are at normalized
Hilbert--Schmidt distance `o(1)` for every fixed generator `s`.

In particular, for `G=SL_3(Z)`, an outlier microstate that stays a fixed
normalized-HS distance from every genuine representation cannot be exact on
any one fixed finite-index subgroup along a subsequence.  This is a habitat
restriction on the outlier branch of
`projective-commutant-transfer-for-arithmetic-pair`; it does not eliminate
microstates whose restrictions remain uniformly far from exact
representations on every fixed finite-index subgroup.

## Proof mechanism

Replace `N` by its normal core; this only changes its finite index.  Put
`m=[G:N]`, choose representatives `T` for `G/N`, and form the exact induced
representation

```text
Pi_j=Ind_N^G(pi_j)  on  L_j = direct_sum_(t in T) H_j.       (SE1)
```

With the convention

```text
g t=t' n(g,t),       n(g,t) in N,
```

define the isometry

```text
W_j:H_j -> L_j,
W_j xi=m^(-1/2) sum_(t in T) delta_t tensor sigma_j(t)^* xi. (SE2)
```

If `sigma_j` were exact, the identity

```text
sigma_j(t')^* sigma_j(g)
 =pi_j(n(g,t)) sigma_j(t)^*                              (SE3)
```

would give `Pi_j(g)W_j=W_j sigma_j(g)`.  Only finitely many multiplication
words occur in `(SE3)` for `g` in the fixed generator packet and `t in T`.
Van Kampen telescoping, together with the `o(1)` subgroup correction on the
finitely many elements `n(g,t)`, therefore gives one
presentation-dependent constant `C_0` and an error `xi_j->0` such that

```text
max_(g in S_G)||Pi_j(g)W_j-W_j sigma_j(g)||_(2,H_j)
 <= C_0(delta_j+xi_j).                                   (SE4)
```

Let `P_j=W_jW_j^*`.  Projection telescoping turns `(SE4)` into

```text
max_(g in S_G)||Pi_j(g)P_jPi_j(g)^*-P_j||_(2,L_j)
 <= C_1(delta_j+xi_j).                                   (SE5)
```

Here all norms are normalized on their displayed spaces; `m` is fixed, so
the change of normalization costs only a fixed factor.

Apply a Kazhdan pair for `G` to the exact conjugation representation
`Ad(Pi_j)` on the Hilbert--Schmidt space of `L_j`.  If `E_j` is the
trace-preserving conditional expectation onto `Pi_j(G)'`, then

```text
||P_j-E_j(P_j)||_(2,L_j) <= C_2(delta_j+xi_j).           (SE6)
```

Since `E_j(P_j)` is a positive contraction, functional calculus at `1/2`
gives a projection

```text
Q_j=1_[1/2,infinity)(E_j(P_j)) in Pi_j(G)'
```

with

```text
||P_j-Q_j||_(2,L_j) <= 2 C_2(delta_j+xi_j).              (SE7)
```

Thus `rank(Q_j)=dim(H_j)+o(dim H_j)`.  The range of `Q_j` carries the exact
representation `alpha_j=Pi_j|_(Q_j L_j)`.  The standard two-projection
polar-decomposition lemma supplies a partial isometry between `P_jL_j` and
`Q_jL_j` after deleting their rank discrepancy, with complement of
normalized dimension `o(1)` and with `L2` distance from the identity
controlled by `||P_j-Q_j||_2`.  Transporting `(SE4)` across that partial
isometry proves the asserted flexible generatorwise correction.

The argument uses neither equivalence of close normalized characters nor a
`U(C)`-valued cocycle vanishing theorem.  Those were exactly the two gaps in
the invalidated earlier route.
