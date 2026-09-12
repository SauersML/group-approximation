# Exterior kernels for prefix creation-deletion pairs and triangular changes

Date: 2026-09-08. Exact four-term binary source certificate.
The kernel was found by a bounded MSI probe that completed in
0.411 seconds. The proof below consists of explicit algebraic
identities and requires no computation. No Kaplansky counterexample
or group-ring split is constructed. The same certificate excludes
the whole family obtained from any two nonempty incomparable
binary prefix words. It also survives every shared left binary
change, including arbitrary upper off-diagonal mixing with the
same invertible diagonal blocks, as proved below.

Use the binary root encoding of `K=GL_2(F_4)` and the reduced
projectors `f_0,P_0` from
[the first-field-coordinate artifact](kaplansky-first-field-coordinate-transporter-kernel-2026-09-08.md).
Roots `1,2` encode the first field coordinate and roots `3,4` the
second, in the basis `1,omega`, with `omega^2=omega+1`.

## The actors and their inverses

In the binary Leavitt algebra, define

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
g=diag(a,b),
Z=P_0[g]f_0.
```

These are genuine units. For either `i=0,1`, the exact inverse is

```
[[1,s_i],[t_i,0]]^-1
  =[[1+s_i t_i,s_i],[t_i,1]].
```

Multiplication in both orders gives identity using `t_i s_i=1`.
Thus `g^-1` is the block diagonal matrix of the two displayed
inverses.

This pair uses both creation and deletion coefficients. Its
coefficient algebra contains all `s_0,s_1,t_0,t_1`, so the
creator-to-zero algebra map used for
[the earlier positive-shear control](kaplansky-complete-exterior-injective-positive-shear-control-2026-09-08.md)
does not extend to it: setting `s_i=0` contradicts `t_i s_i=1`.
This observation concerns that particular algebra specialization,
not every possible finite representation of the generated group.

## The four-term source vector

Let the actual binary tails be

```
zeta=(01)(01)(01)...,
eta =(10)(10)(10)...,
chi =0 zeta.
```

Then `zeta=0 eta` and `eta=1 zeta`; all three displayed tails are
distinct. Put

```
a_i=e_i zeta,       b_i=e_i eta,       c_i=e_i chi,
```

where `e_i` selects binary root coordinate `i`. Define

```
w=(a_1+a_3) wedge b_1+(a_2+a_4) wedge b_2.            (1)
```

This is a four-term vector over `F_2`. In particular its
`a_1 wedge b_1` coefficient is one, so it is nonzero.

For the source condition, recall

```
u_+(xi)=(e_1+omega e_2)xi,
v_+(xi)=(e_3+omega e_4)xi,
u_-(xi)=(e_1+omega^2 e_2)xi,
v_-(xi)=(e_3+omega^2 e_4)xi,
k_+(xi,nu)=(u_+(xi)+v_+(xi)) wedge u_+(nu),
k_-(xi,nu)=(u_-(xi)+v_-(xi)) wedge u_-(nu).
```

Both `k` forms are fixed by `f_0`. Direct expansion gives

```
w=omega^2 k_+(zeta,eta)+omega k_-(zeta,eta).          (2)
```

The two cross coefficients are `omega^3+omega^3=0`, and the
remaining coefficients are `omega^2+omega=1`. Consequently
`f_0w=w!=0`.

## Exact image and target cancellation

The literal prefix and deletion actions give

```
g(a_1+a_3)=a_1+b_2+a_3,       g b_1=b_1,
g(a_2+a_4)=c_1+b_3,           g b_2=a_1.
```

For example `t_0 zeta=eta`, `t_1 zeta=0`,
`t_0 eta=0`, `s_1 zeta=eta`, and `s_0 eta=zeta`.
Substitution in (1) yields

```
g w=a_1 wedge b_1+a_3 wedge b_1+b_2 wedge b_1
    +c_1 wedge a_1+b_3 wedge a_1.                    (3)
```

The projector `P_0` kills every wedge entirely inside the first
field-coordinate space, consisting of binary roots `1,2`. On each
pure character sector this is the identity
`P_0(u_+(xi) wedge u_+(nu))=0` and its Frobenius conjugate;
mixed-character wedges have trivial central character and are
annihilated by the reduced projector. This removes the first,
third, and fourth terms of (3).

For the remaining terms define the symmetric alternating forms

```
J_+(xi,nu)=P_0(v_+(xi) wedge u_+(nu)),
J_-(xi,nu)=P_0(v_-(xi) wedge u_-(nu)).
```

Using `e_1=omega^2 u_+ + omega u_-` in the first field coordinate
and `e_3=omega^2 v_+ + omega v_-` in the second gives

```
P_0(a_3 wedge b_1)
  =omega J_+(zeta,eta)+omega^2 J_-(zeta,eta),

P_0(b_3 wedge a_1)
  =omega J_+(eta,zeta)+omega^2 J_-(eta,zeta).
```

Symmetry of both `J` forms makes their sum zero in characteristic
two. Therefore

```
P_0[g]f_0w=0,       f_0w=w!=0.                       (4)
```

This is an exact source kernel in the genuine boundary exterior
representation, using the two distinct periodic tails without
identifying them or replacing them by a quotient model.

## Arbitrary incomparable prefix words

Let `alpha,beta` be any two nonempty binary words such that neither
is a prefix of the other. Write `s_alpha` for prepending the whole
word `alpha`, and `t_alpha` for deleting that word when it matches,
with zero on the other prefix cylinders; define `s_beta,t_beta`
in the same way. Replace the two blocks by

```
a_alpha=[[1,s_alpha],[t_alpha,0]],
b_beta =[[1,s_beta ],[t_beta ,0]],
g_alpha,beta=diag(a_alpha,b_beta).
```

They are invertible by the same displayed inverse formula, since
`t_alpha s_alpha=t_beta s_beta=1`. Set

```
zeta=(alpha beta)(alpha beta)...,
eta =(beta alpha)(beta alpha)...,
chi =alpha zeta.
```

The two prefix cylinders are disjoint, so `zeta!=eta`, and

```
zeta=s_alpha eta,       eta=s_beta zeta,
t_alpha zeta=eta,       t_beta zeta=0,
t_alpha eta=0.
```

Also `chi!=eta` by the disjoint prefix cylinders. If `chi=zeta`,
then `s_alpha zeta=zeta=s_alpha eta`, contradicting injectivity of
`s_alpha` and `zeta!=eta`; hence all three tails are distinct.

With these tails, the same four-term vector (1) is nonzero and
fixed by `f_0`. The four actor identities preceding (3) hold
literally with `g_alpha,beta`, so the five-term expansion (3) and
its `P_0` cancellation are unchanged. Thus (4) holds for every
such pair, independently of the two word lengths.

Each pair still forbids a creator-to-zero algebra specialization,
because `t_alpha s_alpha=t_beta s_beta=1`. For longer words this
does not assert that the displayed coefficients generate the
entire binary Leavitt algebra.

## Relation to the existing two-sector criterion

The word-pair certificate is a concrete instance of
[the relative-character kernel theorem](kaplansky-full-two-sector-relative-transporter-obstruction-2026-09-08.md).
Write `p=s_alpha`, `q=s_beta`, `r=t_alpha`, `s=t_beta`.
Incomparability gives `s p=0`, so

```
c=b_beta^-1 a_alpha=[[1+q(s+r),p],[s+r,0]].
```

On the tail `eta`, one has `r eta=0`, `s eta=zeta`,
`q zeta=eta`, and `p eta=zeta`. Therefore

```
c u_+(eta)=(omega zeta,zeta)=u_-(omega zeta).
```

If `R,T` are the relative plus-to-plus and plus-to-minus blocks,
this says `R eta=0` and `T eta=omega zeta`. The theorem's
two-sector source is exactly
`omega^2 k_+(zeta,eta)+omega k_-(zeta,eta)=w`.
Replacing `(a_alpha,b_beta)` by `(h a_alpha,h b_beta)` leaves
`c` unchanged, so the shared-left case below also follows from
that existing criterion. The additional upper off-diagonal
mixing is covered by the direct invariant-subspace proof below.

## Shared left changes with arbitrary upper triangular mixing

Let `B` be the free binary boundary module, and write

```
V=U direct_sum j(U),       U=B direct_sum B,
```

where `U` consists of binary roots `1,2`, and `j` copies these
coordinates to roots `3,4`. Define `N` inside `Lambda^2 V` by
the generators

```
Lambda^2 U,
j(p) wedge q+j(q) wedge p       (p,q in U),
j(p) wedge p                   (p in U).
```

The diagonal generators are explicitly included: in
characteristic two, diagonal tensors belong to the kernel of
alternation, and need not be sums of off-diagonal symmetric
tensors. The projector satisfies `P_0 N=0`.

To verify this last claim, extend scalars to `F_4` and write
`p=u_+(p_+)+u_-(p_-)`, and similarly for `q`. The first-field
wedges and all mixed-character wedges are killed as before.
The remaining image of a symmetric cross generator is

```
J_+(p_+,q_+)+J_+(q_+,p_+)
  +J_-(p_-,q_-)+J_-(q_-,p_-)=0.
```

The diagonal generator maps to
`J_+(p_+,p_+)+J_-(p_-,p_-)=0`. This proves the claim over `F_4`
and hence over `F_2`.

Let `h:U->U` be any invertible binary-linear operator and
`k:U->U` any binary-linear operator. Set

```
M=[[h,k],[0,h]],
M(p)=h p,       M(j(p))=k p+j(h p).
```

Then `M N` is contained in `N`. First-field wedges stay in the
first field coordinate. A symmetric cross generator maps to

```
k p wedge h q+k q wedge h p
  +j(h p) wedge h q+j(h q) wedge h p,
```

and a diagonal generator maps to
`k p wedge h p+j(h p) wedge h p`. Both expressions belong to
`N`. No preservation of the two `F_4` character sectors by `h`
or `k` is assumed.

Equation (3) places `g_alpha,beta w` in `N`: three terms are
first-field wedges, and the other two are
`j(a_1) wedge b_1+j(b_1) wedge a_1`. Consequently the same source
certificate gives

```
P_0[M g_alpha,beta]f_0 w=0,       f_0 w=w!=0.         (5)
```

This holds for every `h,k` above, not only a collection of tested
vectors or coefficient choices. If `h,k` have binary Leavitt
entries and `h` is invertible over that algebra, then `M` is a
genuine ambient unit with

```
M^-1=[[h^-1,h^-1 k h^-1],[0,h^-1]].
```

Thus (5) excludes every shared left binary repair `diag(h,h)`
and also the larger four-by-four family with an arbitrary upper
off-diagonal block `k`. It uses no coefficient-augmentation
hypothesis.

## Consequence and scope

Let `g'` be any genuine unit actor covered by (4) or (5), and set
`H=〈K,g'〉`. The boundary action and its exterior square are
representations of `H`. The displayed source kernel contradicts
`L P_0[g']f_0=f_0` in `F_2[H]`. If `L` is allowed in a larger
ambient group algebra, conditional expectation onto `F_2[H]`
preserves that proposed identity and gives the same contradiction.

Thus none of these incomparable-prefix creation-deletion pairs
can solve the projective comparison. Passing other finite probe
domains supplies no general injectivity conclusion, and the
calculation does not cover unequal diagonal left changes, a
nonzero lower off-diagonal block, or arbitrary four-by-four
transporters. It does not identify `N` with the entire kernel of
`P_0`, or assert a kernel for arbitrary group-ring coefficients
inserted between the projectors and the actor.
