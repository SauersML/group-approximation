# Audit: Chern obstruction with vanishing uniform 2-norm and unbounded commutator width

## Verdict

Green. The construction combines two features whose simultaneous scaling is
load-bearing for the trace-problem counterexample:

1. the trace-zero witness has operator norm one and uniform normalized
   `2`-norm tending to zero; and
2. for every fixed finite number of self-commutators, all sufficiently large
   blocks remain operator-norm distance at least one from every such sum.

For `s>=1`, set

```text
X_s = CP^(s^2),
L_s -> X_s the tautological complex line bundle,
F_s = L_s^(+s),
E_s = 1 + F_s,
D_s = Gamma(End(E_s)).
```

Let `p_s` be the bundle projection onto the trivial line and `q_s` the
projection onto the first displayed copy of `L_s` inside `F_s`, and put
`h_s=p_s-q_s`. They are orthogonal rank-one projections in every fibre, so

```text
||h_s||=1,
tau(h_s)=0,
||h_s||_(2,T(D_s))=sqrt(2/(s+1)) -> 0.                  (A1)
```

Fix `ell<=s` and write an arbitrary `z_j in D_s`, relative to
`E_s=1+F_s`, as

```text
z_j = [ a_j  b_j ]
      [ c_j  d_j ].
```

Each `c_j` is a section of `F_s`, so `(c_1,...,c_ell)` is a section of
`L_s^(+s ell)`. If `u=c_1(L_s)`, then because `s ell<=s^2`,

```text
c_(s ell)(L_s^(+s ell))=u^(s ell)!=0
    in H^(2 s ell)(CP^(s^2);Z).                         (A2)
```

Hence the tuple has a common zero `x`. At `x`, compressing to the trivial
line gives

```text
p_s(z_j^*z_j-z_jz_j^*)p_s
 = c_j^*c_j-b_jb_j^* = -b_jb_j^* <= 0.                 (A3)
```

Since `p_s h_s p_s=p_s`,

```text
||h_s-sum_(j=1)^ell[z_j^*,z_j]||>=1.                   (A4)
```

The order of quantifiers is crucial: for every fixed `ell`, (A4) holds for
every `s>=ell` and every choice of the `ell` operators. Combined with (A1),
a fixed finite commutator budget cannot follow a sequence which becomes
arbitrarily small for every normalized trace.

Pedersen--Petersen type homogeneous examples and their commutator
obstructions are classical. Bice--Farah, *Traces, Ultrapowers and the
Pedersen-Petersen C*-Algebras* (arXiv:1307.0111), use such obstructions to
produce nonstandard ultrapower traces and arbitrarily large finite
self-commutator width. The new use here is the simultaneous normalized-`2`
estimate (A1) with the uniform tail obstruction (A4), allowing the
obstruction to live in a uniform tracial completion while surviving a norm
corona.

Hostile checks: `q_s` is a genuine global bundle projection; the top Chern
class is in nonzero degree; no continuous choice of common zeros is used;
and the estimate is in operator norm with no bound assumed on the `z_j`.
