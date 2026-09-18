---
rg: 2
id: abelianized-cover-df-forces-cofinite-congruence-df-proof
kind: route
title: Use purity of the Lyndon embedding to make the congruence tower residual, then apply residual MF implies MF
target: abelianized-cover-df-forces-cofinite-congruence-df
requires:
  - mf-radical-product-and-restricted-sum-formulas
---

The notation is that of the target.  `Rad_MF(Gamma)` is the intersection of
the kernels of all homomorphisms from `Gamma` to unitary groups of norm matrix
coronas `Q = prod M_(k_n) / (+) M_(k_n)`.  A group is MF when some such
homomorphism is injective.

## Cited inputs

- **(C1) Lyndon relation sequence.**  For `F` free on `n` generators and
  `G = F/R`, there is an exact sequence of left `ZG`-modules
  ```text
  0 -> R/[R,R] -> ZG (x)_(ZF) I_F = ZG^n -> I_G -> 0,
  ```
  where `I_G` is the augmentation ideal of `ZG`.  The middle map is given by
  Fox derivatives.  This is standard: K. S. Brown, *Cohomology of Groups*,
  Section II.5, on the relation module.  The same embedding is used in the
  "Known structure" of `full-mf-radical-abelianized-cover-is-not-mf`.
- **(C2) Residual MF and products.**  From
  `mf-radical-product-and-restricted-sum-formulas`, verbatim: "In particular
  finite products and countable restricted sums of MF groups are MF.  More
  generally, every countable group which is residually MF is MF."
- **(C3) Subgroups.**  A subgroup of an MF group is MF.  Restrict the
  injective corona homomorphism.

## Step 1: purity

Let `N >= 1`, and suppose `m in M` and `m = N y` with `y in ZG^n`.

- Let `ybar` be the image of `y` in `I_G`.  Then `N ybar` is the image of
  `m`, which is `0` by exactness of (C1).
- `I_G` is a subgroup of the free abelian group `ZG`, so it is torsion-free.
  Hence `ybar = 0`.
- By exactness, `y` lies in `M`, so `m` lies in `NM`.

So `M cap N ZG^n = NM`.  The inclusion `NM <= M cap N ZG^n` is clear.  The
induced map `M/NM -> ZG^n / N ZG^n = (Z/N)[G]^n` is therefore injective.

For `m != 0` in `M <= ZG^n`, `m` lies in `N ZG^n` exactly when `N` divides
every integer coefficient of `m`, that is, when `N` divides `c(m)`.  So
`m in NM` if and only if `N | c(m)`.  This is item 1.

## Step 2: the gate

**Rad bound.**  Let `N` be in `calN`.  Choose an injective homomorphism
`pi : H_N -> U(Q)`, and let `q_N : E -> H_N` be the quotient map.  Then
`pi o q_N` is a corona homomorphism of `E` with kernel exactly `NM`.  By the
definition of `Rad_MF`, `Rad_MF(E) <= NM`.

**Zero intersection.**  Suppose `calN` is infinite, and let `m != 0` lie in
`NM` for every `N` in `calN`.  By Step 1, every `N` in `calN` divides
`c(m) >= 1`.  But a positive integer has only finitely many divisors, which
is a contradiction.  So the intersection of `NM` over `N` in `calN` is `0`.

**Residual MF.**  Suppose `calN` is infinite, and let `e != 1` in `E`.
- If `e` is not in `M`, then `e` is not in `NM` for any `N`.
- If `e` is in `M`, then by the zero intersection there is some `N` in `calN`
  with `e` not in `NM`.

In either case `q_N(e) != 1` in the MF group `H_N`.  So `E` is residually MF.
`E` is countable, so it is MF by (C2).  This is item 2.

## Step 3: the lattice structure

Let `N, N'` be in `calN`, and set `L = lcm(N, N')`.

- In the free abelian group `ZG^n`, `N ZG^n cap N' ZG^n = L ZG^n`, because
  this holds coordinatewise in `Z`.
- By Step 1,
  ```text
  NM cap N'M = M cap N ZG^n cap N' ZG^n = M cap L ZG^n = LM.
  ```
- So the map `E -> H_N x H_N'` has kernel `LM`, and `H_L` embeds in
  `H_N x H_N'`.
- The product is MF by (C2), so `H_L` is MF by (C3).  Hence `L` is in
  `calN`.

Finally, `H_1 = E/M = G`.  So `1` is in `calN` exactly when `G` is MF.  This
is item 3.

## Step 4: DF forces cofinite congruence DF

Assume `G != 1`, `Rad_MF(G) = G`, and that `E` is not MF.

- **`calN` is finite.**  This is the contrapositive of item 2.
- **`Rad_MF(E) != 1`.**  If `Rad_MF(E) = 1`, then every `e != 1` survives in
  the image of some corona homomorphism.  That image is a subgroup of a
  corona unitary group, so it is MF.  Hence `E` would be residually MF, and
  so MF by (C2).  This contradicts the assumption.
- **The case `calN` nonempty.**  Pick `N_0` in `calN`.  By Step 2,
  `Rad_MF(E) <= N_0 M <= M`.
  - `Rad_MF(E)` is a characteristic subgroup of `E`, so it is normal.  Being
    contained in `M`, it is a `G`-submodule of `M`, and it is nonzero.
  - For every `N` in `calN` and every `m != 0` in `Rad_MF(E)`, Step 2 gives
    `m in NM`, and Step 1 gives `N | c(m)`.  So `N` divides `c_E`.
  - Take `c = c_E`.
- **The case `calN` empty.**  Take `c = 1`.
- **Conclusion.**  In both cases, if `N` does not divide `c`, then `N` is not
  in `calN`, so `H_N` is not MF.
  - A prime `p` divides `c` for only finitely many `p`.
  - For a fixed prime `p`, `p^k` does not divide `c` once `k > v_p(c)`.

This is item 4.

## Remark: what is special about the torsion quotients

This remark is recorded for later users and is not part of the claim.  In any
homomorphism `rho : H_N -> U(Q)`, `B = C*(rho(M/NM))` is `C(X)`.  Here `X` is
a closed subset of the dual of `M/NM`, which is profinite, so `X` is totally
disconnected.

- Hence the linear span of the projections in `B` is dense in `B`.  Ranks of lifted projections are exact
  corona invariants: two lifts of the same projection eventually differ in
  norm by less than `1`, and so they have equal rank.
- This is the invariant whose analogue for the torsion-free `E` died in an
  earlier live attempt on DF, the ratio-trace invariant measure, because
  there the renormalized trace is not a corona invariant.
- The invariant still does not obstruct.  Every nonempty `G`-invariant clopen
  subset of `X` carries a `G`-invariant probability measure by rank ratios.
  By Step 1, however, the dual action is a factor of the full shift
  `((Z/N)^n)^G`, which carries Bernoulli measures.  So no contradiction
  follows from measures alone.
