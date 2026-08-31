---
rg: 2
id: lin-perfect-face-forces-qutrit-offdiagonal-three-corner-row
kind: claim
title: The Lin perfect face forces a positive three-corner row, and ONE3 makes it a 27-word qutrit coefficient
artifacts:
  - research/lin-perfect-face-qutrit-three-corner-proof.md
distinct_from:
  lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass: that proves a uniform third positive outcome; this proves uniform cross-context noncommutativity and identifies its off-diagonal three-corner coefficient.
  lin-loss-is-a-three-corner-full-c-fourier-coefficient: those losing coefficients vanish in a perfect Lin trace and become positive under finite-dimensional soundness; the coefficients here are positive inside every perfect trace because an abelian perfect trace would be classical.
  fixed-qutrit-test-is-either-finite-rigid-or-morita-neutral: that proves diagonal occurrence conditioning cannot fill the qutrit head; this exhibits the finite source-side off-diagonal row which every perfect realization must carry.
  common-naimark-context-transport-is-an-inner-full-c-gauge: that rules out the canonical inner context transport as raw holonomy; this coefficient exists before any raw Jacobson return is chosen.
---

**ESTABLISHED SOURCE-SIDE NONABELIAN COEFFICIENT; NO GROUP RELATOR.**

Let `I` be the fixed independent-set game obtained from Lin's explicit
infinite-loop separation, and let `p_(x,a)` be its canonical PVM atoms.
Thus

```text
omega_co(I)=1,                         omega_*(I)<1.      (LQ1)
```

Put `N=|{(x,a)}|` and, for a trace `tau` on the perfect game algebra,

```text
K_I(tau)=N^(-2) sum_(x,a,y,b) ||[p_(x,a),p_(y,b)]||_(2,tau)^2. (LQ2)
```

The perfect trace space is nonempty and compact. There is a constant
`kappa_I>0`, depending only on the fixed game, such that

```text
K_I(tau)>=kappa_I                         for every perfect tau. (LQ3)
```

In particular every perfect Lin strategy is genuinely nonabelian. If every
question has `m` answers, form the fixed row

```text
C_(x,a;y,b;a')=p_(x,a) p_(y,b) p_(x,a')       (a'!=a).  (LQ4)
```

With the uniform probability measure on this finite row,

```text
Average ||C_(x,a;y,b;a')||_2^2
   =K_I(tau)/(2(m-1))
   >=kappa_I/(2(m-1)).                                 (LQ5)
```

Hence some entry has a positive initial spectral corner below the literal
Lin atom `p_(x,a')`. The row is fixed; the selected entry may depend on
the trace.

Now apply the already audited fixed-language reduction to the Lin-derived
SynchBCS and choose its finite positive-ONE3 output `B_13`. In a perfect
trace write its clause atoms as

```text
p_(c,0)+p_(c,1)+p_(c,2)=1,              c in Clauses(B_13). (LQ6)
```

Repeated occurrences of one Boolean variable are the same projection.
The algebra has a perfect trace and no perfect Connes-embeddable trace.
Let `N_13=3|Clauses(B_13)|` and define the normalized occurrence
commutator energy `K_13` as in `(LQ2)`. Compactness gives

```text
kappa_13=min_(perfect tau) K_13(tau)>0.                 (LQ7)
```

For `omega=exp(2 pi i/3)`, put

```text
u_c=sum_(a=0)^2 omega^a p_(c,a),
p_(c,a)=(1/3)sum_(r=0)^2 omega^(-ar) u_c^r.             (LQ8)
```

The fixed qutrit row has `2N_13^2` entries

```text
D_(c,a;d,b;a')=p_(c,a)p_(d,b)p_(c,a'),        a'!=a.    (LQ9)
```

Its normalized row energy is exactly

```text
(1/(2N_13^2)) sum_(c,a,d,b,a'!=a) ||D_(c,a;d,b;a')||_2^2
    =K_13(tau)/4
    >=kappa_13/4.                                      (LQ10)
```

Every row entry is the following at-most-27-word full-complex coefficient:

```text
D_(c,a;d,b;a')
 =(1/27) sum_(r,s,t=0)^2
   omega^(-ar-bs-a't) u_c^r u_d^s u_c^t.               (LQ11)
```

It has exact off-diagonal bi-Fourier type

```text
u_c D=omega^a D,                    D u_c=omega^(a') D,  a'!=a. (LQ12)
```

Thus some coefficient satisfies `tau(D^*D)>=gamma_13`, where
`gamma_13=kappa_13/4`. In the tracial GNS von Neumann algebra,

```text
R=1_[gamma_13/2,1](D^*D)
```

obeys

```text
R<=p_(c,a'),
tau(R)>=gamma_13/(2-gamma_13),
D^*D R>=(gamma_13/2)R.                                 (LQ13)
```

This remains a uniform obstruction near the exact face. For any fixed
finite relation-defect menu with positive weights `alpha_l`, first normalize
by `W=sum_l alpha_l`. Compactness gives `epsilon_13>0` such that

```text
Def/W <=epsilon_13   =>   K_13>=kappa_13/2
                         and normalized row energy >=kappa_13/8. (LQ14)
```

Therefore a zero-noise compiler whose decoded qutrit clause atoms all lie
in one abelian packet, one diagonal multiplicity algebra, or any family
with commutator energy tending to zero cannot preserve the Lin perfect
face. A surviving compiler must retain a genuinely noncommuting
cross-context router, and `(LQ11)` is the exact bounded full-complex
coefficient it must expose.

This does not prove a nonhyperlinear group. The selected entry and spectral
projection are trace-dependent, `(LQ11)` is a linear combination rather
than one ordinary relator, and no bounded raw `S/T` return is proved to
authenticate it against finite approximations.

Primary-source interfaces used:

- Junqiao Lin, *MIPco=coRE*, Definition 6.14, Theorem 6.15, and the
  explicit infinite-loop paragraph after it: https://arxiv.org/abs/2510.07162
- Laura Mancinska, Pieter Spaas, Taro Spirig, and Matthijs Vernooij,
  *Gap-preserving reductions and RE-completeness of independent set games*,
  Theorem 3.1 and Remark 3.2: https://arxiv.org/abs/2505.05253
- Eric Culf and Kieran Mastel, *RE-completeness of entangled constraint
  satisfaction problems*, Lemma 3.10, Example 4.13, and Theorem 4.14:
  https://arxiv.org/abs/2410.21223

DERIVATION
lin-perfect-face-qutrit-three-corner-proof
