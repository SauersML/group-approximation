---
rg: 2
id: internal-mf-reflection-subgroup-lattice
kind: claim
title: Internal MF reflections contain complete actor subgroup lattices
root: true
artifacts:
  - research/internal-mf-reflection-lattice-correspondence-proof.md
---

For `1<=i<=m`, let `Q_i` be countable virtually free and form the internal
product reflection

```text
P=B semidirectProduct R<=U,
R=product_i Q_i,
B=product_i U^(Q_i),
pi:P->>R.                                                 (ILC1)
```

Then

```text
S |-> K_S=pi^(-1)(S)=B semidirectProduct S                (ILC2)
```

is an isomorphism from the complete subgroup lattice of `R` onto the closed
interval

```text
{K<=P:B<=K}                                               (ILC3)
```

in the subgroup lattice of `P`, and hence in that of the binary Leavitt unit
group `U`.  It preserves arbitrary meets and joins.  For `S<=T<=R`,

```text
[K_T:K_S]=[T:S],
core_(K_T)(K_S)=K_(core_T(S)),
N_(K_T)(K_S)=K_(N_T(S)).                                 (ILC4)
```

Moreover,

```text
K_S normal K_T  iff  S normal T,
K_T/K_S~=T/S                                              (ILC5)
```

whenever these equivalent conditions hold.

Every `S<=R` is residually finite and therefore MF.  Each group in the
interval has exact reflection

```text
Rad_MF(K_S)=B,                    R_MF(K_S)~=S,            (ILC6)
Hom(S,M)~=Hom(K_S,M),                                    (ILC7)
cl_MF^(K_S)(N)=pi^(-1)(cl_MF^S(pi(N)))                    (ILC8)
```

for every MF target `M` and every normal subgroup `N` of `K_S`.  The same
factorization holds for finite, compact, finite-dimensional unitary, and
finite-dimensional linear targets over every field.  Thus the finite,
compact, unitary, and all-field linear residuals of `K_S` are all `B`, and
its profinite and Bohr completions are canonically those of `S`.

Consequently the interval `(ILC3)` simultaneously records the exact ordinary
subgroup calculus of `R` and the complete target-visible calculus of every
one of its subgroups; quotienting by the common lower endpoint `B` recovers
both structures without loss.
