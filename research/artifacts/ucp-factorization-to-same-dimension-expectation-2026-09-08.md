# UCP factorizations round to expectations in the original matrix dimension

2026-09-08. Written finite-dimensional proof. No computation, build,
job, or new Lean verification. The factorization theorem below is
proved directly; the completely bounded corollary has one explicit
primary-source input in Section 8.

## 1. Statement and normalization

Let `P:M_d(C)->M_d(C)` be UCP, trace preserving, and self-adjoint
for normalized Hilbert--Schmidt inner product. Suppose `B` is a
finite-dimensional unital C*-algebra and

```text
Delta:B->M_d,       Upsilon:M_d->B
```

are UCP. Define

```text
r=||Upsilon Delta-id_B||_(infinity->infinity),
s=||Delta Upsilon-P||_(infinity->2),       eta=2r+s.     (1)
```

**Theorem.** A unital algebra `A subset M_d` exists with

```text
||P-E_A||_(infinity->2) <= min(2,44 eta^(1/4)).          (2)
```

Here `E_A` preserves normalized matrix trace. Completely bounded
upper bounds can be substituted for `r,s`. No bound on dimensions,
central block counts, or multiplicities is assumed.

It suffices to prove (2) for `0<eta<=1/8`. At `eta=0` the proof
below gives an exact expectation. For `eta>1/8`, any conditional
expectation has distance at most two from `P`, and
`44 eta^(1/4)>2`. The bound by two is always available separately.

## 2. The factorization makes source unitaries almost unitary in trace

Fix `u in U(B)` and set `D=Delta(u)*Delta(u)`. It is a positive
contraction. Since `||Upsilon Delta(u)-u||<=r`, Schwarz gives

```text
Upsilon(D) >= Upsilon Delta(u)* Upsilon Delta(u)
             >= (1-r)^2 I >= (1-2r)I.
```

Apply the unital positive map `Delta` and normalized matrix trace.
The error `s` in (1), tested on `D`, and trace preservation of `P`
give

```text
1-2r <= tau(Delta Upsilon(D)) <= tau(D)+s.
```

Consequently

```text
sup_(u in U(B)) tau(1-Delta(u)*Delta(u)) <= eta.       (3)
```

The argument uses `r<1`, which follows in the range now considered.

## 3. Repair the Stinespring support

Take a finite-dimensional Stinespring representation
`Delta(b)=V* pi(b)V`, with `V:C^d->K` an isometry, and put
`p=VV*`. Identify the original `M_d` with `p B(K)p`. All norms
on this dilation use `Tr/d`; thus `p` has trace one, while the
identity of `B(K)` need not have trace one.

For each source unitary, direct expansion gives

```text
||[pi(u),p]||_(2,Tr/d)^2
 =2 tau_d(1-Delta(u)*Delta(u)) <=2eta.                 (4)
```

Average `p` over the compact group `pi(U(B))`, obtaining
`a=E_(pi(B)')(p)`. The Haar commutator identity gives
`||p-a||_2^2<=eta`. Let `q=1_[1/2,1](a)`. It is a projection
in `pi(B)'`. Spectral rounding is a nearest-projection operation
in Hilbert--Schmidt norm, so `||a-q||_2<=||a-p||_2`. Orthogonality
of conditional expectation gives

```text
||p-q||_2^2=||p-a||_2^2+||a-q||_2^2<=2eta,
|rank(q)/d-1|<=||p-q||_2^2<=2eta.                    (5)
```

The rank inequality follows from
`Tr((p-q)^2)>=|Tr(p)-Tr(q)|`. In particular `q!=0`.
For every `b in B_1`,

```text
||Delta(b)-q pi(b)q||_2<=2||p-q||_2<=2sqrt(2eta).    (6)
```

The range `q pi(B)q` is an exact algebra with identity `q`.
Its whole unit ball is the image of `B_1`: the representation
is a quotient onto a finite-dimensional C*-algebra, and unit-ball
elements lift with no norm increase by its direct-summand structure.
No word-length or generator-only approximation is used here.

## 4. Align the repaired support with the original corner

For finite projections `p,q`, there is a unitary `U` such that
`q'=UqU*` and `p` are nested, with

```text
||U-I||_2<=sqrt(2)||p-q||_2.                          (7)
```

For completeness, use the principal-angle decomposition of their
ranges. On a two-dimensional angle plane with angle `theta`, rotate
the `q` line onto the `p` line. The squared Frobenius norm of the
rotation minus identity is `4(1-cos(theta))`, at most
`4 sin(theta)^2`; the contribution of `p-q` is `2 sin(theta)^2`.
Pair unmatched orthogonal lines as angle-`pi/2` planes. Leave any
remaining excess lines in the larger projection unchanged, and act
as identity on all other subspaces. This makes the smaller support
a subprojection of the larger and proves (7), with any common trace
normalization.

Set

```text
A=U(q pi(B)q)U*,       rho(b)=Uq pi(b)qU*,
t=(2sqrt(2)+4)sqrt(eta),       N=rank(q').             (8)
```

Equations (5)--(7) and two-factor telescoping give

```text
sup_(b in B_1)||Delta(b)-rho(b)||_2<=t,
|N/d-1|<=2eta.                                       (9)
```

The map `rho` takes `B_1` onto `A_1`. The algebra `A` has
identity `q'`, which need not yet equal `p`.

## 5. Two-sided ball control gives a compressed expectation

Extend the original map to the dilation by
`P_p(x)=P(pxp)`, with its output in `p B(K)p`. It is
self-adjoint and contracts operator norm and `L^2(Tr/d)`.
It is not asserted to be unital on the entire dilation.
Let `E_A` mean the trace-preserving expectation on the `q'` corner,
preceded by compression to `q'`, and extended by zero elsewhere.
It is the Hilbert projection onto `L^2(A)` and contracts operator
norm. These statements are unchanged when the trace is scaled.

For `x in (p B(K)p)_1`, `Upsilon(x)` is in `B_1`; (1) and (9)
therefore show

```text
||(I-E_A)P_p(x)||_2<=s+t.                            (10)
```

Also

```text
||P_p Delta(b)-Delta(b)||_2<=s+r       (b in B_1),
alpha:=sup_(a in A_1)||P_p(a)-a||_2<=2t+r+s.         (11)
```

The first line follows by comparing `P Delta` with
`Delta Upsilon Delta`, then using `||Upsilon Delta-id||<=r`.
The second uses the two occurrences of the error in (9).

There is a useful pointwise estimate that avoids interchanging
mixed norms under adjoints. For a contraction `x` in the original
`p` corner, put `y=E_A(P_p-I)x`. Then `y in A`, `||y||<=2`,
and `||x||_(2,Tr/d)<=1`. Since `P_p` is self-adjoint,

```text
||y||_2^2
 = <(P_p-I)x,y>
 = <x,(P_p-I)y>
 <= ||x||_2 ||(P_p-I)y||_2 <=2alpha.                 (12)
```

Use absolute values in the Cauchy--Schwarz step; the left-hand
side is real and nonnegative. Splitting into the two Hilbert
components and then compressing to `p` proves

```text
||P-C_p E_A C_p||_(infinity->2,p)
 <= mu:=s+t+sqrt(4t+2(r+s)).                         (13)
```

The input norm and output norm in (13) use the original normalized
`p` corner. No bound on the trace of the identity of the dilation
is needed in (12).

## 6. A compressed exact expectation can be rounded in its corner

We include the required dimension-repair lemma. Let `D subset M_m`
be a unital algebra, and let `f` have rank `n`, with
`a_0=(m-n)/m<=1/2`. There is a unital algebra `F subset fM_mf`
such that

```text
||C_f E_D C_f-E_F||_(infinity->2,f)<=25 a_0^(1/4).    (14)
```

At `a_0=0` this is immediate. Otherwise put `h=m-n>=1` and
write `D=direct_sum_i(M_(a_i) tensor I_(b_i))`.
Delete whole represented blocks until the remaining desired deficit
fits in the next block. In that block remove coordinates in its
larger tensor factor, rounding the deficit upward to a multiple
of `min(a_i,b_i)<=sqrt(m)`. Retain every later block. The
resulting projection `f_0` has product form on each block and

```text
h<=h_0:=m-rank(f_0)<=h+sqrt(m),
beta:=h_0/m<=a_0+sqrt(a_0).                          (15)
```

The last inequality uses `h>=1`. Product form ensures that
`f_0 D f_0` is an algebra. Set
`D_0=f_0 D f_0 + C(1-f_0)`, omitting a zero summand. We claim

```text
||E_D-E_(D_0)||_(infinity->2,m)<=(sqrt(2)+2)sqrt(beta). (16)
```

For a contraction `x`, the remainder `x-f_0xf_0` has squared
normalized HS norm at most `2beta`. Its images under `E_D` and
`E_(D_0)` have norms at most `sqrt(2beta)` and `sqrt(beta)`;
the latter image is scalar on `1-f_0` and zero on `f_0`.
On a retained block write `f_0=P tensor Q`, of ranks `a',b'`,
inside `M_a tensor I_b`. If the corner expectation of the
compressed input is `y tensor Q`, the full-block expectation is
`theta y tensor I_b`, where `theta=b'/b` and `||y||<=1`.
The squared difference, normalized by `m`, is at most

```text
a'b'(1-theta)/m <= (ab-a'b')/m.                      (17)
```

Here `y` is supported on the retained `a'` coordinates. Summing
(17) and using the remainder bounds proves (16). In particular,
the multiplicity normalization `theta` has not been discarded.

There is a unitary `W`, supported on a subspace of dimension at
most `2h`, with `g=Wf_0W*<=f`. Indeed the intersection of the
two ranges has codimension at most `h` in the range of `f_0`;
choose equally many replacement directions in the range of `f`
and extend the resulting subspace isometry on their span.
Thus `||W-I||_(2,m)<=2sqrt(2a_0)`. Telescoping the input and
output conjugations of an expectation bounds its change by
`4||W-I||_2`, so this rotation costs at most `8sqrt(2a_0)`.

Define

```text
F=W(f_0 D f_0)W* + C(f-g).
```

The compressed expectation onto `WD_0W*` and `E_F` differ
only in scalar normalization on `f-g`. Their squared difference
on a contraction, in ambient normalized trace, is at most

```text
(h/h_0)^2 (h_0-h)/m <= a_0.                          (18)
```

The formula also covers `f=g`, when that contribution is zero.
Combining (15)--(18) and renormalizing the `f` corner gives

```text
||C_f E_D C_f-E_F||_(infinity->2,f)
 <= [(sqrt(2)+2)sqrt(a_0+sqrt(a_0))
        +(8sqrt(2)+1)sqrt(a_0)]/sqrt(1-a_0)
 <=25 a_0^(1/4).                                    (19)
```

For the last bound, after division by `a_0^(1/4)`, use
`sqrt(1+sqrt(a_0))<=sqrt(2)`, `a_0^(1/4)<=1`, and
`1/sqrt(1-a_0)<=sqrt(2)`. The resulting constant is at most
`20+3sqrt(2)<25`. This proves (14) without treating arbitrary
compression of an expectation as an exact expectation.

## 7. Finish the factorization theorem

The aligned projections `p,q'` are nested. If `N>=d`, then
`p<=q'`; apply (14) within the `q'` corner, whose discarded
fraction is

```text
a_0=(N-d)/N<=2eta<=1/4.
```

Equations (13)--(14) give an algebra in the original corner with
distance at most `mu+25(2eta)^(1/4)`.

If `N<=d`, then `q'<=p`. Extend `A` by the scalar algebra on
`p-q'`. Its expectation differs from `C_p E_A C_p` by at most
`sqrt((d-N)/d)<=sqrt(2eta)`. Thus the distance is at most
`mu+sqrt(2eta)` in this case.

Let `c_0=2sqrt(2)+4<7`, so `t=c_0 sqrt(eta)`. Since
`r+s<=eta`, `s<=eta`, and `0<eta<=1`,

```text
mu<=eta+c_0 sqrt(eta)+sqrt(4c_0 sqrt(eta)+2eta)
   <=(1+7+sqrt(30)) eta^(1/4)<(27/2)eta^(1/4).
```

Also `25*2^(1/4)<30`. Both rank cases therefore have error
less than `44eta^(1/4)`, proving (2).

If `eta=0`, (5) gives `q=p`, and the exact representation in
(6) identifies `Delta(B)` with a represented algebra. The equalities
`Delta Upsilon=P` and `Upsilon Delta=id` make `P` an idempotent
with this range. Its self-adjointness makes it the orthogonal
trace-preserving expectation. This handles the omitted endpoint.

## 8. Completely bounded near-idempotence: a corollary and its limit

Kitaev's
[Theorem 12.3, arXiv:2405.02434v2](https://arxiv.org/html/2405.02434v2#S12.SS2)
states that a finite-dimensional UCP map with completely bounded
idempotence defect `epsilon` admits UCP maps through a finite-dimensional
C*-algebra, with both factorization errors `O(epsilon)` in completely
bounded norm. The estimate for `Upsilon Delta-id` follows by taking
one multiplicative input equal to the identity in that theorem.
The constants are universal. This primary source was checked on
2026-09-08.

For self-adjoint bistochastic `P`, these completely bounded estimates
dominate the norms in (1), so `eta=O(epsilon)`. The theorem above
therefore proves same-dimension conditional-expectation rounding in
`infinity->2` norm with error `O(epsilon^(1/4))`. This is a
consequence for that specialized class and that output norm; no
completely bounded closeness to the final expectation is asserted.

The additional source algebra is now enough, including the return
from its repaired Stinespring dimension. Uniform approximate closure
of `P`'s operator-unit-ball image under bounded products does not
itself construct such a source or the maps in (1). In particular,
the native Kazhdan heat estimates only make
`||P^2-P||_(infinity->2)` small. They neither make the completely
bounded defect small nor supply (1). Thus this result does not
establish the native heat-rounding premise or nonhyperlinearity.
No claim of bibliographic priority is made.
