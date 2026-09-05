---
rg: 2
id: bcjm-rounding-preserves-the-cyclic-parity-proof
kind: route
title: Track the external covariance through amenable lamp classicalization
target: amenable-lamp-rounding-preserves-the-kt-named-return-wall
requires:
  - amenable-hyperlinear-rounds-to-sofic
  - kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence
---

# 1. Diagonalize the amenable rounding

Write

~~~text
A=direct_sum_(G/Gamma) C_2.
~~~

For every finite `E subset A` and every positive tolerance, Theorem 1.1
of Burton--Chaudkhari--Juschenko--Muliarchyk gives, from a sufficiently good
restriction of `theta_n`, a permutation-valued approximation on the same
Hilbert space which is close to `theta_n` on `E`.

Apply the theorem along an exhaustion of `A`, with tolerances tending to
zero, and pass to the usual diagonal subsequence. Denote the output by
`beta_n`. For each fixed `a in A`, put

~~~text
epsilon_n(a)=||beta_n(a)-theta_n(a)||_2.
~~~

Then

~~~text
epsilon_n(a)->0.                                          (BPR1)
~~~

Because `theta_n` is asymptotically multiplicative, `beta_n` is also
asymptotically multiplicative on every fixed lamp table. Its traces are
canonical: if `a!=1`, then

~~~text
|tr(beta_n(a))|
 <=|tr(theta_n(a))|+epsilon_n(a) ->0.                     (BPR2)
~~~

Nothing in this step uses or changes the actor matrices. Express them in
the single basis selected by the amenable theorem and write

~~~text
U_(g,n)=theta_n(g).
~~~

# 2. Covariance survives automatically

For fixed `g in G` and `a in A`, define the original covariance defect

~~~text
c_n(g,a)=
 ||U_(g,n) theta_n(a) U_(g,n)^*
       -theta_n(gag^(-1))||_2.
~~~

The group microstate multiplication rows imply `c_n(g,a)->0`. Indeed,
`theta_n(g)^*` is asymptotic to `theta_n(g^(-1))`, and two applications
of multiplicativity give the displayed conjugation row.

Unitary invariance and the triangle inequality now give the exact estimate

~~~text
||U_(g,n) beta_n(a) U_(g,n)^*
       -beta_n(gag^(-1))||_2
 <=epsilon_n(a)+c_n(g,a)+epsilon_n(gag^(-1)).             (BPR3)
~~~

Thus the amenable theorem need not be equivariant in its construction:
equivariance on every prescribed row is inherited from closeness in the
same dimension. What is not inherited is that `U_(g,n)` is a permutation,
or even close to one modulo a coherently chosen commutant gauge.

# 3. The two lamp words retain their regular table

Put

~~~text
V_n=beta_n(v),             W_n=beta_n(w),
p_n=(1+V_n)/2,             r_n=(1+W_n)/2.
~~~

Since `v^2=w^2=1` and `beta_n` is asymptotically multiplicative,

~~~text
||V_n^2-1||_2+||W_n^2-1||_2 ->0.                         (BPR4)
~~~

For a unitary `V_n`,

~~~text
||V_n^*-V_n||_2=||1-V_n^2||_2.
~~~

Consequently `(p_n)` and `(r_n)` define self-adjoint projections in the
tracial matrix ultraproduct.

The elements `v` and `w` are distinct nonzero elements of the Boolean
lamp group, so `vw!=1`. Asymptotic multiplicativity and `(BPR4)` give

~~~text
||V_n^*W_n-beta_n(vw)||_2 ->0.                           (BPR5)
~~~

Using `(BPR2)` for `vw`,

~~~text
||p_n-r_n||_2^2
 =1/4 ||V_n-W_n||_2^2
 =1/2-(1/2) Re tr(V_n^*W_n)
 ->1/2.                                                  (BPR6)
~~~

This calculation uses only the canonical two-lamp character. It is
independent of how the probabilistic rounding chooses its basis.

# 4. The stabilizer rows and the named return

Every `s in Gamma` fixes the three-site parity, so `svs^(-1)=v`.
Apply `(BPR3)` with `a=v`. Since

~~~text
||[p_n,U_(s,n)]||_2
 =1/2 ||U_(s,n)V_nU_(s,n)^*-V_n||_2,
~~~

we obtain

~~~text
||[p_n,U_(s,n)]||_2
 <=epsilon_n(v)+(1/2)c_n(s,v) ->0.                       (BPR7)
~~~

For the named return `h=e_12(x_2/x_1)`, one has
`hvh^(-1)=w`. Again by `(BPR3)`,

~~~text
||U_(h,n)p_nU_(h,n)^*-r_n||_2
 <=(1/2)(epsilon_n(v)+c_n(h,v)+epsilon_n(w))
 ->0.                                                    (BPR8)
~~~

Right multiplication by `U_(h,n)^*` preserves normalized Hilbert--Schmidt
norm, hence

~~~text
||[p_n,U_(h,n)]||_2
 =||p_n-U_(h,n)p_nU_(h,n)^*||_2.
~~~

The reverse triangle inequality, `(BPR6)`, and `(BPR8)` now prove

~~~text
||[p_n,U_(h,n)]||_2 ->1/sqrt(2).                         (BPR9)
~~~

This is the same pointed wall as in the exact quasi-regular correspondence,
now carried by the permutation-valued output of amenable classicalization.

# 5. Optional exact repair on the fixed Boolean table

For completeness, the approximate projections can be made literal without
changing any limit. Restrict `beta_n` to

~~~text
B_0=<v,w> isomorphic_to C_2^2.
~~~

Call a point `x` of its permutation basis good if `beta_n(1)x=x`, every
one of the finitely many rows
`beta_n(a)beta_n(b)x=beta_n(ab)x`, for `a,b in B_0`, holds at `x`,
and the map `a |-> beta_n(a)x` is injective. These are finite local
checks; goodness is not defined by an unbounded orbit of approximate
generators.

There are only finitely many multiplication rows, so their failure set is
`o(d_n)` by asymptotic multiplicativity and the identity

~~~text
||P-Q||_2^2=2 d_H(P,Q)
~~~

for permutation matrices. The collision set is also `o(d_n)`: for
`a!=b`, a collision is, up to an `o(d_n)` multiplication error, a fixed
point of `beta_n(b^(-1)a)`, and `(BPR2)` says that the latter fixed-point
proportion tends to zero.

The identity failure set is also `o(d_n)`, because `beta_n(1)` is
asymptotic to the identity. For a good point `x`, the set
`O_x={beta_n(a)x:a in B_0}` has four elements and is closed under each
`beta_n(b)` by the local multiplication checks. Moreover, at a point
`beta_n(c)x` in that set, associativity in `B_0` and the same checks at
`x` give

~~~text
beta_n(a)beta_n(b)beta_n(c)x
 =beta_n(a)beta_n(bc)x
 =beta_n(abc)x
 =beta_n(ab)beta_n(c)x.
~~~

Thus the good points form `1-o(1)` of the basis and split into genuine
free four-point `B_0`-orbits. Keep that
action there and put any exact action, for example the trivial action, on
the complement. This gives a genuine permutation representation
`sigma_n:B_0->Sym(d_n)` with

~~~text
||sigma_n(a)-beta_n(a)||_2 ->0       for every a in B_0. (BPR10)
~~~

Replacing `V_n,W_n` by `sigma_n(v),sigma_n(w)` makes `p_n,r_n`
literal commuting projections of asymptotic normalized trace `1/2` and
preserves `(BPR6)--(BPR9)`. They need not be diagonal in the original
permutation basis. Simultaneously diagonalizing this exact Boolean table
makes these two projections diagonal; conjugate all actor matrices by the
same unitary, which preserves every displayed estimate. This last basis
change is not claimed to preserve the permutation form of all other lamps.

# 6. Exact scope of the result

The amenable theorem has therefore done everything it can do locally. It
has produced a classical lamp carrier, retained every named covariance row,
and retained the canonical displacement `1/sqrt(2)`. It does not turn the
external approximate actor into a genuine finite-dimensional
representation. Without that step, finite-image compression does not put
`h` in the image of `Gamma`, and `(BPR7)` does not contradict
`(BPR9)`.

Equivalently, the probabilistic basis is not missing a pairwise equivariance
estimate. The missing datum is simultaneous actor/multiplicity coherence
strong enough to classicalize or exactify the return itself. The global
Kun--Thom route remains open.
