---
rg: 2
id: dummy-abelianized-cover-df-split-proof
kind: route
title: Average witnesses into one character, Diracize it, and let the self-centralizing kernel kill the scalar kernel
target: dummy-abelianized-cover-df-splits-regular-trace-and-shadow
requires:
  - abelianized-cover-kernel-is-self-centralizing
  - character-diracization-limit
---

The notation is that of the target: `E_z`, `M_z`, `T_op`, `S`.  All norms on
`M_d` are the operator norm unless marked `2`, where
`||x||_2 = tr_d(x^*x)^(1/2)` uses the normalized trace.

## Step 0: closure properties of `T_op(Gamma)`

Let `Gamma` be countable.

- **(T0) Every element is a character.**  Suppose `phi` has operator-norm
  defect at most `delta` on a finite set.
  - From `phi(e)^2 ~ phi(e)` with `phi(e)` unitary we get
    `||phi(e)-1|| <= delta`.
  - It follows that `||phi(g^-1)-phi(g)^*|| <= 2 delta`.
  - Hence
    ```text
    sum_(i,j) c_i conj(c_j) tr phi(g_j^-1 g_i) = tr(Y^*Y) + O(delta),   where Y = sum_i c_i phi(g_i),
    ```
  - Also `tr phi(h g h^-1) = tr phi(g) + O(delta)`.

  In the limit, every `tau in T_op` is a normalized, central,
  positive-definite function, so `character-diracization-limit` applies to
  it.
- **(T1) Products and conjugates.**  If `phi`, `psi` witness `tau` and
  `sigma`, then:
  - `phi (x) psi` witnesses `tau sigma`, with defect at most the sum of the
    two defects, since `||u(x)v - u'(x)v'|| <= ||u-u'|| + ||v-v'||` for
    contractions;
  - `conj(phi)` witnesses `conj(tau)`.
- **(T2) Convex combinations.**  Let `phi_i : Gamma -> U(d_i)` witness
  `tau_i`, and let `p/q` be rational.  Then
  ```text
  phi = (phi_1 (x) 1_(p d_2))  (+)  (phi_2 (x) 1_((q-p) d_1))
  ```
  witnesses `(p/q) tau_1 + (1-p/q) tau_2`, with defect the larger of the two.
- **(T3) Closedness.**  `T_op` is closed under pointwise limits by
  definition, since each condition involves one finite set and one `delta`.
  With (T2), `T_op` is therefore convex, and it is closed under countable
  convex combinations `sum_i w_i tau_i`, because the partial sums converge
  uniformly.
- **(T4) Units and corona traces.**
  - The constant `1` lies in `T_op`, witnessed by the trivial representation.
  - Let `rho : Gamma -> U(prod M_(k_n) / (+) M_(k_n))` be a homomorphism with
    unitary lifts `rho_n`.  Its defects tend to zero in operator norm, so
    every cluster point of `g |-> tr rho_n(g)` lies in `T_op`.
- **(T5) Conversely, every element of `T_op` is a corona limit trace.**
  Enumerate `Gamma = {g_1, g_2, ...}`.  For each `j`, choose a witness `phi_j`
  on `S_j = {g_1, ..., g_j}` with `delta_j = 1/j`.  Tensoring with `1_r`
  changes neither the trace nor the defect, so we may take
  `d_j >= j`.  Then `(phi_j)` defines a corona homomorphism whose traces
  converge to `tau`.

## Step 1: `S(Gamma)` is a normal subgroup containing `Rad_MF(Gamma)`

For a character `tau` with GNS unitaries `u_g`,

```text
||u_g - 1||_2^2 = 2 - 2 Re tau(g).
```

So `tau(g) = 1` iff `u_g = 1`.  The set `{g : tau(g) = 1}` is the kernel of
the GNS representation, hence a normal subgroup, and `S(Gamma)` is the
intersection of these kernels over `tau in T_op`.

Now let `g in Rad_MF(Gamma)` and `tau in T_op`.  By (T5), `tau` is the limit
trace of a corona homomorphism with lifts `phi_j`.  The class of `g` is
trivial in that corona, so `||phi_j(g) - 1||_op -> 0`, and therefore
`tau(g) = lim tr phi_j(g) = 1`.  So `Rad_MF <= S`.

## Step 2: nontrivial normal subgroups of `E_z` meet `M_z` (item 1)

Let `N` be normal in `E_z` with `N cap M_z = 1`.  Both subgroups are normal,
so

```text
[N, M_z] <= N cap M_z = 1,
```

and `N <= C_(E_z)(M_z)`.  This centralizer equals `M_z` by `(SC1)` of
`abelianized-cover-kernel-is-self-centralizing`.  Its hypothesis is exactly
that a dummy generator `z` with `q(z) = 1` has been adjoined.  Hence
`N <= M_z`, so `N = N cap M_z = 1`.

Apply this to the normal subgroups `N = Rad_MF(E_z)` and `N = S(E_z)`
(Step 1).

## Step 3: the regular-trace criterion (item 2)

**(a) implies (b).**  We have `delta_e(g) = 0 != 1` for every `g != e`.

**(b) implies (c).**  This is immediate from the definition of `S`.

**(c) implies (d).**  Enumerate `M_z \ {0} = {m_1, m_2, ...}`.  For each `i`,
choose `tau_i in T_op` with `tau_i(m_i) != 1`, and set

```text
tau = 1/2 + sum_(i>=1) 2^(-i-1) tau_i.
```

By (T3) and (T4), `tau` lies in `T_op`.  Each `tau_i(m)` lies in the closed
unit disk.  So `|tau(m)| = 1` forces every term to equal one common unimodular
number, and the constant term makes that number `1`.  In particular
`tau_i(m_i) = 1`, which is false.  Hence `|tau(m_i)| < 1` for every `i`.

**(d) implies (a).**  Let `tau` be as in (d), and let
`K = {g : |tau(g)| = 1}`.
- By `character-diracization-limit` and (T0), `K` is a normal subgroup of
  `E_z`.
- By (d), `K cap M_z = 0`.
- By Step 2, `K = 1`.
- By (T1), `|tau|^(2k) = (tau conj(tau))^k` lies in `T_op`.
- By the same limit lemma, `|tau|^(2k)` converges pointwise to
  `1_K = delta_e`.
- By (T3), `delta_e` lies in `T_op`.

**MF conclusion.**  (T5) realizes `delta_e` by a corona homomorphism `W` with
lifts `W_j`.  For `g != e`,

```text
||W_j(g) - 1||_op >= ||W_j(g) - 1||_2 = (2 - 2 Re tr W_j(g))^(1/2) -> sqrt 2,
```

so `W` is injective and `E_z` is MF.

## Step 4: structure of a regular model (item 3)

**The spectrum is the whole dual.**  `M_z` is abelian and `W` is a
homomorphism, so `D = C*(W(M_z))` is a commutative quotient of
`C*(M_z) = C(hat M_z)`.  Hence `D = C(X)` for a closed `X` in `hat M_z`.

The limit trace restricts to a state on `C(X)`.  This state is a
probability measure `mu` on `X`, and its Fourier coefficients are
`mu^(m) = delta_e(m)`.  So `mu` is Haar measure on `hat M_z`, which has full
support, and therefore `X = hat M_z`.

**The action.**  Conjugation by `W(e)` induces the dual of the module action.
It is trace-preserving, and it fixes the trivial character.

**Mixing.**  `M_z` embeds `G`-equivariantly in `Z[G]^n`, by the Lyndon
sequence.  Suppose `v != 0` and `g v = v`.  Then `g` permutes the finite
support of `v`, so `Stab(v)` is finite.  Hence, for nonzero `m, m'`, the set
`{g : g m = m'}` is either empty or a coset of a finite group.  Since
`<chi_(gm), chi_(m')>_Haar = [gm = m']`, the dual action is mixing.

**Essential freeness.**  Let `g != 1`.
- `Fix(g)` is the annihilator of `(g-1) M_z`.
- `(g-1) M_z` is nonzero, because `G` acts faithfully by `(SC2)`.
- `(g-1) M_z` is infinite, because `M_z` is torsion-free.
- So `Fix(g)` is a closed subgroup of infinite index, and it is Haar-null.

`G` is countable, so the action is essentially free.

## Step 5: the decomposition (item 4)

**DF implies (REG) and (SH).**  By Step 1,
`Rad_MF(E_z) != 1` gives `S(E_z) != 1`.  By item 2, that is `(REG)`.
`(SH)` then holds because its conclusion is true.

**(REG) and (SH) imply DF.**  By item 2, `(REG)` gives `S(E_z) != 1`, and
`(SH)` then gives `Rad_MF(E_z) != 1`.

**The two readings of (REG) agree.**  By items 1 and 2, `(REG)` is the same
as `S(E_z) cap M_z != 0`.  That is the parenthetical form of `(REG)` in the
target.

## Step 6: the retraction

Let `pi : F_z -> F(X)` be the map with `z |-> 1`.  It satisfies
`q o pi = q`, so `pi(R_z) <= R`.  The inclusion `iota : F(X) -> F_z` sends
`R` into `R_z`.  Both maps preserve commutators of kernels, so they induce
maps `E -> E_z -> E` whose composite is the identity.

So `E` is a subgroup of `E_z`, and a subgroup of an MF group is MF.
Therefore `E` not MF implies `E_z` not MF, which is DF for `E` implying DF
for `E_z`.  QED

## Where the ratio-trace variant dies

The claimed intent also included a renormalized trace.  Fix
`c = [e,m]` with `rho(c) != 1`, set `a_n = |rho_n(c) - 1|^2`, and put

```text
Tr(y) = lim tr(y_n) / tr(a_n),
```

hoping for a `G`-invariant Radon measure on the moved locus of the spectrum.
This is not well defined on the norm corona when `tr(a_n) -> 0`, which is the
tracially blind case, for example `rho (+) 1_(N_n)`.  There are two failures.

- Changing a lift by an element of `(+) M_(k_n)` alters `tr(y_n)` by `o(1)`,
  not by `o(tr(a_n))`.
- `rho_n(g) a_n rho_n(g)^*` and the lift of `alpha_g(a)` differ by the
  operator-norm defect.  That defect is `o(1)`, not `o(tr(a_n))`.

So neither invariance nor independence of the lift survives, and the
construction gives nothing beyond the ordinary limit traces used above.
Handling blind models is exactly `(SH)`.
