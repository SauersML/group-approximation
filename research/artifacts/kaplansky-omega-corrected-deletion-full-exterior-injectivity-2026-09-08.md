# The omega correction passes the complete exterior-square boundary test

Date: 2026-09-08. Exact proof; no computation is used.

The actual chart candidate `T_omega` defined below is injective
on the entire exterior-square source `im f_0` in the natural free
binary-boundary representation. This is a representation
test, not a group-ring splitting theorem. No element `L`
satisfying `L T_omega=f_0` is constructed or asserted.

## Setup and the previously proved support reduction

Work over `F_4`, where `omega^2=omega+1`; all tail vectors
have finite support on actual infinite binary sequences.
The operators `s_i` prepend digit `i`, and `t_i` delete
that digit when it matches, giving zero otherwise.

Put

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
g=diag(a,b),              H=a+m_omega^-1 b m_omega,

ell=diag(1,omega^-1),
n=[[0,omega^-1],[1,0]],
T_omega=P_0[ell][g][n]f_0.
```

Use the complete source parametrization by `(X,Y)` from
[the scalar-conjugate artifact](kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md).
Its invertible source and target changes identify the
projected action of `T_omega` with the complete exterior
map `F_omega` of the auxiliary operator `diag(H,b)`:

```
E_omega T_omega (tau D_omega)=F_omega.
```

[The periodic reduction](kaplansky-exterior-kernels-reduce-to-pure-periodic-tails-2026-09-08.md)
proved that every possible kernel source is supported on
purely periodic tails, eliminated both constant cores and
all their cross components, and reduced the remaining
source to mixed periodic cores. It also established the
following exact outside-core equations and reconstruction.

Set

```
U=X+omega Y,       V=omega X+Y,
X=omega^2U+V,      Y=U+omega^2V.
```

On a finite union of mixed periodic cores, let `P` be the
span of tails with preceding bit zero. Source columns
outside `P` vanish. The scalar tensor `W=V|_(P tensor P)`
satisfies

```
tau W=(I tensor K)W,
(L tensor K)W=(I tensor (L+K+I))W,
W=(K tensor K)W.                                  (1)
```

Here, writing `N` for the complementary core projection,

```
R=t_0|P,       T=P s_0|P,       A=N s_0|P,
L=(I+R)^-1T,
J=I+s_0t_0 R L+s_1A,
G=L+s_0t_0 R L+t_1R L+s_1A+A,
K=P J.
```

The full source is recovered by

```
U=(G tensor I)tau W,
V=(J tensor I)tau W.                              (2)
```

The previous endpoint argument places both factors of `W`
in the stable endpoint space of `K` and excludes the last
endpoint of every zero run of length at least three. On the
remaining endpoint support, `L^2=L`: for a length-two run,
with first and last endpoints `f,l`,

```
L f=0,       L l=f+l,
```

and `L` is zero on every other retained endpoint.

On all endpoints, `K=I+B`, where the bridge `B` takes a
first endpoint to the last endpoint of the preceding zero
run exactly when the intervening one run has length one.
It kills the other endpoints. This is a partial permutation.
Its only possible cycle is the primitive `(01)^infinity`
core; there `K=0`, so that component has no stable image
and cannot occur in `W`. On all remaining endpoints `B`
is nilpotent and `K` is invertible.

## The endpoint equations remove every bridge and every asymmetry

Let `mathcal U` be the finite vector contraction image of
`W`. The first equation of (1), with `K` invertible on the
stable space, shows that the contraction images in its two
factors coincide and

```
K mathcal U=mathcal U.
```

The second equation shows `L mathcal U` is contained in
`mathcal U`. As a matrix on this space, `W` is invertible:
it identifies `mathcal U^*` with `mathcal U`.

For calculations on the ambient endpoint space, extend `L`
to an idempotent `Lhat` by setting

```
Lhat(first)=0,
Lhat(last)=first+last
```

on every zero run of length at least two, and setting it
to zero on singleton runs. This extension agrees with `L`
on `mathcal U`, because the last endpoints of longer runs
were excluded already. Put `Pi=I+Lhat`. Its image is the
span of first endpoints, and its restriction to the span
of last endpoints is injective.

In matrix form, (1) gives

```
W^T=W K^T,
L W K^T=W(L+K+I)^T.
```

Consequently

```
W^-1 L W=[K^-1(L+K+I)]^T.
```

The operator on the right is similar to the idempotent
`L`, so `K^-1(L+K+I)=I+K^-1Pi` is idempotent on
`mathcal U`. Equivalently,

```
Pi K^-1 Pi=Pi  on mathcal U.                       (3)
```

Here is the endpoint meaning of (3). On the first-endpoint
space, let `Q` take a first endpoint to the preceding first
endpoint whenever their intervening one run has length one.
Let `S` project onto singleton zero runs. The only possible
cycle of `S Q` is the already removed primitive `01` core,
so `S Q` is nilpotent. For every positive integer `j`,

```
Pi B^j|first=Q(S Q)^(j-1).
```

Indeed, a bridge can continue past its new last endpoint
only when that zero run is a singleton. The finite series
for `K^-1` therefore gives

```
Pi(K^-1+I)|first=Q(I+S Q)^-1.                     (4)
```

The right side has kernel exactly `ker Q`: if it kills
`v`, put `w=(I+S Q)^-1v`; then `Qw=0`, so `v=w`.
Since `Pi` is injective on bridge images, `ker Q` equals
`ker B` on the first-endpoint space. Applying (3)--(4)
to `mathcal U_0=ker(L|mathcal U)` proves

```
B mathcal U_0=0.
```

It remains to eliminate the bridge on
`mathcal U_1=im(L|mathcal U)`. The second equation of (1)
can also be written as symmetry of
`(I tensor (I+L))W`. In the decomposition
`mathcal U=mathcal U_0 direct_sum mathcal U_1`, this means

```
W=[[A,C],[0,D]],       A=A^T,
```

with `A,D` invertible. Since `K` fixes `mathcal U_0`
pointwise, write

```
K=[[I,E],[0,F]].
```

The upper-right block of `W^T=W K^T` gives `C F^T=0`,
so `C=0`. Its lower-left block then gives `D E^T=0`,
so `E=0`. Thus `K` preserves `mathcal U_1`. The bridge
image `B mathcal U_1` lies in this space and is therefore
killed by `Pi`; it also lies in the span of last endpoints,
where `Pi` is injective. Hence `B mathcal U_1=0` as well.

We have proved

```
B mathcal U=0,       K|mathcal U=I,       tau W=W,
(L tensor I)W=(I tensor L)W.                      (5)
```

This conclusion does not assume symmetry of the original
complete source tensors `X,Y`.

## Two symmetric families and a full target equation

Call a zero run active if its preceding one run has length
at least two. Because the bridge is a partial permutation,
(5) allows only active runs. Let `E` be their first-endpoint
space and `E_2` the subspace for zero runs of length exactly
two. The `L=0` eigenspace uses those first endpoints. The
`L=1` eigenspace uses `f+l` for active length-two runs.
Thus (5) has the unique form

```
W=W_0+(j tensor j)Z,
tau W_0=W_0,       tau Z=Z,
W_0 in E tensor E, Z in E_2 tensor E_2,
j f=f+t_0f.
```

No cross terms between these two eigenspaces remain.

We use a single exact linear combination of the two full
target coordinates. Write `p=s_0,q=s_1,r=t_0,s=t_1`.
Then `F_1=F_omega,+ +omega F_omega,-` is

```
alt([I tensor (p+s)
       +q tensor (I+q)
       +s tensor (I+r)]U
    +[I tensor (I+q)
       +s tensor (q+r)
       +q tensor (I+p+q+s)]V).                    (6)
```

This is an operator identity over arbitrary `F_4` tensor
coefficients. For example, expanding the plus map gives
`F_omega,+=F_0+omega F_1`, while the minus map gives
`F_omega,-=omega^2F_0+omega F_1`; their displayed
combination isolates `F_1` without conjugating any source
coefficient.

For a first endpoint `f`, abbreviate the linear run maps

```
a=s_0f,       c=s_1a,       d=s_1c,
r_f=t_0f,     s_f=t_1f.
```

The contribution of `W_0` to the full reconstructed source
on a diagonal tensor `f tensor f` is

```
U_0=(a+c) tensor f,
V_0=(f+c) tensor f.
```

Substitution into (6) gives

```
a wedge (f+c+d)+(a+c+d+r_f) wedge s_f.             (7)
```

For a length-two run, set additionally

```
l=t_0f,       h=t_1l,       k=t_1h,
w=f+l.
```

The contribution of `Z` on `f tensor f` is

```
U_1=(w+a+c+h) tensor w,
V_1=(w+c) tensor w.
```

Its value under (6) is

```
(c+d) wedge (a+f+h)+(h+a+k) wedge f.               (8)
```

All maps in these identities are linear in `f`. Symmetric
tensors are spanned by tensors `v tensor v`, including
the off-diagonal combinations obtained from
`(v+w) tensor (v+w)+v tensor v+w tensor w`.
Thus (7)--(8), valid for arbitrary run vectors, prove the
corresponding operator identities on the entire symmetric
spaces over `F_4`, including diagonal terms in characteristic
two.

## The active-start projection matches the two families

Project (6) to wedges between active zero-run starts `a`
and their last preceding ones `c`. These are disjoint sets
of actual tails, and both maps from the run labels are
injective. In (7), besides `a wedge c`, the only additional
term in that projection is `a wedge s_f` when the zero run
is a singleton and its following one run has length two.
In that case `s_f` is the last preceding one of the next
active zero run. Define `T_2` on `E` by this move; it is
zero on the other run labels. The projection of (8) is
exactly `a wedge c`.

For completeness, a deletion output beginning a subsequent
zero run after a single one belongs to an inactive run, so
it does not enter this projection. Other deletion outputs
and interior zero tails also do not belong to either of
the two specified active-tail sets.

Since the wedge map on these disjoint sets is injective,
the projected equation is exactly

```
(I tensor (I+T_2))W_0+Z=0,                        (9)
```

where `Z` is embedded in `E tensor E` through `E_2`.
The partial permutation `T_2` has a directed cycle only
when every zero run is a singleton and every one run has
length two. This is the unique actual primitive `011`
core. Therefore

```
ker(I+T_2) is contained in span{eta},
eta=(110)^infinity.
```

Every row of `W_0` indexed outside `E_2` lies in this
kernel, by (9). Symmetry kills cross entries with `E_2`
and all other outside rows. Since `T_2` kills `E_2`,
there is a symmetric tensor `W_2` on `E_2` with

```
W_0=W_2+lambda eta tensor eta,
Z=W_2.                                           (10)
```

The isolated `011` term is already nonzero under the full
equation (6). For it, `d=eta`, `r_f=0`, and
`s_f=c=(101)^infinity`, so (7) equals `eta wedge c`,
which is nonzero. All terms from `W_2` belong to other
tail-equivalence classes, since the `011` core has no
length-two zero run. They cannot cancel it. Thus
`lambda=0`.

## Two more projections leave only one core, which also fails

The two symmetric families now have the same coefficient
tensor `W_2`. Adding (7) and (8) for a length-two run
cancels all `a` terms and gives

```
F_1|W_2=alt((C+D) tensor (I+H)
                 +(H+H_2) tensor I)W_2,          (11)

C f=c,       D f=d,
H f=h=t_1t_0f,
H_2f=k=t_1^2t_0f.
```

Equivalently, on a diagonal run tensor its value is

```
(c+d) wedge (f+h)+(h+k) wedge f.
```

The three label sets here are pairwise disjoint: `f` begins
with `01`, `c` with `100`, and `d` with `1100`.
Neither `h` nor `k` can be an `f` label, because a nonzero
deletion of a leading one has preceding bit one, whereas
`f` has preceding bit zero.

Let `R_m` take a length-two zero run to the next length-two
zero run exactly when the intervening one run has length
`m`, and give zero otherwise. For `m=2,3,4` the target
run is automatically active. Projection of (11) to
`c wedge f` gives

```
((I+R_2+R_3) tensor I)W_2=0.                      (12)
```

the extra `c` contributions come from `h` after two ones
and from `k` after three ones. Projection to `d wedge f`
similarly gives

```
((I+R_3+R_4) tensor I)W_2=0.                      (13)
```

The maps `R_2` and `R_4` have disjoint images, since a
given zero run has a unique preceding one-run length.
Adding (12)--(13) therefore kills each of their tensor
contributions separately. It follows that

```
(R_3 tensor I)W_2=W_2.
```

Symmetry gives the same equality in the other factor.
A finite vector fixed by the partial permutation `R_3`
is supported on directed cycles. Such a cycle requires
every zero run to have length two and every one run to
have length three. Its only actual primitive core is
`(00111)^infinity`, with a single first-endpoint label.
Consequently `W_2` is a scalar multiple of `f tensor f`
on that core.

On this last possibility, `h=d` and `k=c`. Equation (11)
is therefore

```
(c+d) wedge (f+d)+(d+c) wedge f=c wedge d != 0.
```

The distinct prefixes `100` and `1100` certify the final
inequality. Thus `W_2=0`, and (10) gives `W=0`.
Reconstruction (2) now forces `U=V=0`, hence `X=Y=0`.

## Exact conclusion and the remaining group-ring gap

The complete map `F_omega` is injective on the full
natural-boundary exterior-square source. By the established
invertible source and target changes, the same is true of
the actual chart candidate `T_omega` on `im f_0`.
This statement covers every finitely supported exterior
source, not a chosen collection of periodic windows.

It does not imply a group-ring identity `L T_omega=f_0`.
Other representations, higher exterior powers, quotient
obstructions, or the exact coefficient equations may still
exclude such an identity. The previously proved period-four
kernel for the omega-square correction remains a separate
negative control. No headline conjecture is resolved by
passing this representation test.
