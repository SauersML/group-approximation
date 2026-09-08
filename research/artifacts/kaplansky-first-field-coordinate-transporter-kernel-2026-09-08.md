# An exterior kernel for every transporter confined to the first field coordinate

Date: 2026-09-08. Exact obstruction, with an explicit binary certificate.
No computation is used. No Kaplansky counterexample is constructed.

## 1. Whole-family statement

Use the chart `K=GL_2(F_4)` and reduced projectors `f_0,P_0` from
[the half-corner artifact](kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md),
Sections 7–8. Encode the first `F_4` coordinate by binary roots `1,2`
and the second by binary roots `3,4`, in the field basis `1,omega` with
`omega^2=omega+1`.

Let `B` be the free `F_2` vector space on binary infinite tails, and
let `V=B^4` be the binary boundary module. Suppose `g` acts on `V` as

```
g=diag(a,I_(B^2)),       a∈GL_(F_2)(B^2).
```

Thus `g` can be any invertible binary-linear operator on the first
field coordinate, and fixes the second field coordinate pointwise.
In particular `a` may be an arbitrary invertible matrix over the
binary Leavitt algebra, not just a prefix permutation.

**Theorem.** The element `Z=P_0[g]f_0` has a nonzero source kernel on
the scalar-extended exterior square `F_4⊗_(F_2) Lambda^2 V`. Therefore
there is no identity `LZ=f_0` in the group algebra of `〈K,g〉`, or in
the group algebra of any ambient group containing that subgroup.

The theorem concerns the literal transporter `P_0[g]f_0`. It does not
claim the corresponding obstruction for arbitrary chart coefficients
inserted on either side of `g`, or for arbitrary units mixing the
two field-coordinate subspaces.

## 2. Exact source and target forms

Write `B_4=F_4⊗_(F_2)B`. In the scalar extension of `V`, define

```
u_+(xi)=(e_1+omega e_2)xi,
v_+(xi)=(e_3+omega e_4)xi,
u_-(xi)=(e_1+omega^2 e_2)xi,
v_-(xi)=(e_3+omega^2 e_4)xi.
```

The plus pair is the natural `F_4` representation of `K`; the minus
pair is its Frobenius twist. The central element `z=omega I` acts
by `omega` on the plus sector and by `omega^2` on the minus sector.

For `xi,eta∈B_4` put

```
k_+(xi,eta)=(u_+(xi)+v_+(xi)) wedge u_+(eta),
J_+(xi,eta)=P_0(v_+(xi) wedge u_+(eta)).
```

The projector formulas give

```
f_0 k_+(xi,eta)=k_+(xi,eta),
J_+(xi,eta)=J_+(eta,xi),       J_+(xi,xi)=0.             (1)
```

Also `k_+(xi,eta)!=0` whenever both arguments are nonzero: its
component in `v_+(B_4) wedge u_+(B_4)` is the nonzero tensor
`xi⊗eta`.

For completeness, the finite two-tail tensor calculation underlying
these facts has basis `A=11,B=12,C=21,D=22` and satisfies

```
im f_0=span{B+C,A+C},
P_0 A=0,       P_0 B=P_0 C=P_0 D=B+C+D.
```

The same-tail determinant line has `f_0=1`, `P_0=0`. These identities
give (1) first on basis tails, then by bilinearity for arbitrary
vectors. They also imply

```
P_0(u_+(xi) wedge u_+(eta))=0,
P_0(u_-(xi) wedge u_-(eta))=0.                          (2)
```

The second equality is the Frobenius-conjugate calculation. Finally,
every wedge of a plus vector with a minus vector has trivial central
character. Since `P_0` lies entirely in the nontrivial central block,
it annihilates all such mixed wedges.

## 3. Kernel for an arbitrary first-coordinate operator

Scalar extension and the eigenspace decomposition write the action of
`g` on the first plus sector uniquely as

```
g u_+(eta)=u_+(R eta)+u_-(T eta),
```

for `F_4`-linear maps `R,T:B_4 -> B_4`. Since `g` fixes the other field
coordinate, `g v_+(xi)=v_+(xi)`. Expanding `g k_+(xi,eta)`, all wedges
between two first-coordinate vectors vanish after `P_0` by (2) and
the mixed-central-character observation. The term involving
`v_+(xi)` and `u_-(T eta)` vanishes for the same central reason.
Exactly one term remains:

```
P_0[g] k_+(xi,eta)=J_+(xi,R eta).                       (3)
```

If `R` is nonzero, choose `eta` with `R eta!=0` and set `xi=R eta`.
Equations (1) and (3) then give

```
w=k_+(R eta,eta)!=0,       f_0 w=w,       Zw=0.
```

If `R=0`, choose any nonzero `xi,eta`; (3) kills the same nonzero
source vector. This exhausts all possible `R` and proves the kernel
assertion.

The natural boundary action gives a representation of `〈K,g〉` and
of its exterior square. Hence an identity `LZ=f_0` in that subgroup
algebra would give `0=w`. For an unrestricted proposed `L` in a larger
ambient group algebra, conditional expectation onto the subgroup
algebra preserves `LZ=f_0`, because `Z,f_0` are already in it. This
proves the unrestricted group-algebra obstruction.

## 4. Explicit kernel for the bit-level prefix actor

The actor from
[the finite-submodule control](kaplansky-bit-level-transporter-without-finite-boundary-modules-2026-09-08.md)
has binary prefix table

```
1->10,       20->11,       21->2,       3->3,       4->4,
```

and first-coordinate matrix

```
a=[[s_0,s_1 t_0],[0,t_1]].
```

Using `e_1=omega^2 u_+ + omega u_-` and `e_2=u_++u_-` in that
coordinate gives its plus-to-plus tail block

```
R=omega^2 s_0+s_1 t_0+omega t_1.
```

Take `eta=000...`, `theta=1000...=s_1 eta`. Then

```
xi=R eta=omega^2 eta+theta!=0,
w=k_+(xi,eta)
```

is the concrete kernel from Section 3.

One can extract a certificate over `F_2` itself. Write `a_i=e_i eta`
and `b_i=e_i theta` for the eight binary boundary vectors. The
coefficient of `1` in `w` relative to the scalar basis `1,omega` is

```
w_0 = a_1 wedge a_3 + a_1 wedge a_4 + a_2 wedge a_3
    + a_1 wedge b_1 + a_1 wedge b_3
    + a_2 wedge b_2 + a_2 wedge b_4.
```

It is nonzero, for instance by its `a_1 wedge b_1` coefficient.
All group-algebra coefficients are binary, so taking scalar
coefficients in `f_0w=w` and `Zw=0` proves

```
f_0 w_0=w_0!=0,       P_0[g]f_0 w_0=0.
```

The previously proved absence of finite-dimensional invariant
submodules for the two conjugate charts remains valid. The displayed
vector is not asserted to lie in a finite-dimensional submodule
invariant under those charts. An explicit finite-support kernel
vector does not require such an invariant submodule. The two results
are therefore compatible: the finite-submodule method fails here,
while the direct exterior calculation excludes the transporter and
the whole first-field-coordinate family.

## 5. Block-diagonal extension: both coordinates must mix field characters

There is a further precise obstruction for `g=diag(a,b)`, where `a,b`
are arbitrary invertible binary-linear operators on the first and
second field-coordinate spaces, respectively. Write

```
g u_+(eta)=u_+(A eta)+u_-(B eta),
g v_+(xi)=v_+(C xi)+v_-(D xi).
```

Define the symmetric alternating form in the other sector by

```
J_-(xi,eta)=P_0(v_-(xi) wedge u_-(eta)).
```

The same expansion used in Section 3 gives the exact formula

```
P_0[g] k_+(xi,eta)
  =J_+(C xi,A eta)+J_-(D xi,B eta).                     (4)
```

The two terms belong to distinct nontrivial central-character
sectors. First-coordinate wedges and mixed-character terms have
already vanished as before.

If either coordinate operator preserves or reverses the field
characters, (4) has a nonzero source kernel. More explicitly, a
character-preserving first block has `B=0` and `A` bijective; a
character-reversing first block has `A=0` and `B` bijective. The
corresponding alternatives for the second block are `D=0` with `C`
bijective, or `C=0` with `D` bijective. The bijectivity conclusions
also follow automatically from the invertibility of the binary
operator: Frobenius conjugation determines its action on the other
character sector, so it is respectively a diagonal or an
off-diagonal invertible two-sector operator.

For example, if `D=0` and `C` is bijective, choose `eta` with
`A eta!=0` and put `xi=C^-1 A eta`. Both arguments of the surviving
`J_+` then coincide. If `A=0`, every `k_+(xi,eta)` is already killed.
If instead `B=0` and `A` is bijective, choose `xi` with `C xi!=0`
and put `eta=A^-1 C xi`; if `C=0`, again every source vector is
killed. The two character-reversing alternatives use the same
arguments with `J_-`, `D`, and `B`.

This proves that a possible split for a literal block-diagonal
transporter requires **both** coordinate operators to mix the two
field characters: all four blocks `A,B,C,D` must be nonzero. That
condition is necessary only. The argument does not establish a
kernel or an inverse for arbitrary actors when both coordinate
operators mix characters. The following section gives an explicit
fully mixed failure. Arbitrary chart coefficients surrounding the
transporter are not covered.

## 6. Opposite bit-level prefix actors fail even with all four blocks nonzero

The necessary condition from Section 5 is not sufficient. Take

```
a=[[s_0,s_1 t_0],[0,t_1]],
b=a^-1=[[t_0,0],[s_0 t_1,s_1]],
g=diag(a,b).
```

All four character blocks are nonzero. Their exact formulas are

```
A=omega^2 s_0+s_1 t_0+omega t_1,
B=omega s_0+omega^2 s_1 t_0+omega t_1,
C=omega^2 t_0+s_0 t_1+omega s_1,
D=omega t_0+s_0 t_1+omega s_1.
```

For `eta=000...` and `theta=1000...`, their images of `eta` are,
respectively,

```
omega^2 eta+theta,       omega eta+omega^2 theta,
omega^2 eta+omega theta, omega eta+omega theta.
```

Since `eta,theta` are distinct basis tails, none of these vectors
vanishes.

Nevertheless there is a two-term binary source kernel. Set
`a_i=e_i eta`, `b_i=e_i theta` and put

```
w=a_1 wedge a_3+a_2 wedge a_4.
```

To verify its source condition, define the two determinant vectors

```
d_+(eta)=u_+(eta) wedge v_+(eta),
d_-(eta)=u_-(eta) wedge v_-(eta).
```

Both are fixed by `f_0`, and expansion in the binary basis gives

```
w=omega^2 d_+(eta)+omega d_-(eta).
```

The two mixed-root coefficients cancel, and both remaining
coefficients are `omega^2+omega=1`. Thus `f_0w=w!=0`.

The literal prefix action is

```
g a_1=a_1,       g a_2=b_1,
g a_3=a_3,       g a_4=b_4,
```

so

```
g w=a_1 wedge a_3+b_1 wedge b_4.
```

For any one tail `tau`, let `W_tau` be its four-dimensional binary
root module. After scalar extension,

```
Lambda^2 W_tau
  =det(V_+) direct-sum (V_+ tensor V_-) direct-sum det(V_-).
```

The two determinant lines have `P_0=0`; the middle summand has
trivial central character and is likewise killed by `P_0`.
Consequently `P_0` annihilates the entire exterior square of each
single-tail module. The two displayed terms of `gw` belong to
`Lambda^2 W_eta` and `Lambda^2 W_theta`, respectively. Hence

```
P_0[g]f_0w=0,       f_0w=w!=0.
```

Conditional expectation again excludes an unrestricted proposed
left inverse. This resolves the specific pair of opposite prefix
actors; it does not exclude every block-diagonal transporter whose
two coordinate operators both mix field characters.
