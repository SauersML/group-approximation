# The omega-square simultaneous correction has a period-four kernel

Date: 2026-09-08. Exact exterior certificate and binary descent.
This excludes one concrete simultaneous chart correction. It
does not settle Kaplansky's direct-finiteness conjecture or
exclude the remaining omega correction.

Subsequent status: the [contragredient period-two certificate](kaplansky-contragredient-period-two-kernel-excludes-omega-split-2026-09-08.md)
excludes the omega correction too. The inverse-adjoint
automorphism and the two certificates exclude all four
literal parameter/orientation choices.

Use the operators and source parametrization from
[the simultaneous-candidate artifact](kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md)
and the support reduction from
[the periodic-kernel artifact](kaplansky-exterior-kernels-reduce-to-pure-periodic-tails-2026-09-08.md).
All tails below are actual infinite binary sequences.

## The candidate and the full map

Let `omega^2=omega+1` in `F_4`, with coefficient conjugation
`sigma`. Write

```
a_0=[[1,s_0],[t_0,0]],
b_0=[[1,s_1],[t_1,0]],
g=diag(a_0,b_0),
H_z=a_0+m_z^-1 b_0 m_z.
```

The actual group-ring chart candidate is

```
T_z=P_0[ell_z][g][n_z]f_0,
ell_z=diag(1,z^-1),
n_z=[[0,z^-1],[1,0]] in GL_2(F_4).
```

Here `diag(1,z^-1)` and `n_z` are matrices on the two
`F_4` field coordinates; the binary root representation is
understood. We use `z=omega^2` throughout this certificate.

On the full exterior source `(X,Y)`, the invertible source
change `S_z=tau D_z` and target change `E_z` give

```
E_z T_z S_z=F_z,
F_z=Phi_g+E_(z^-1) Psi_b D_z.
```

The complete map `F_z` is the projected exterior map of the
auxiliary natural operator `diag(H_z,b_0)`. No invertibility
of `H_z` as a group actor is being assumed.

Define its character blocks by

```
A=omega^2+s_0+t_0,       B=omega+omega^2s_0+t_0,
C=omega^2+s_1+t_1,       D=omega+omega^2s_1+t_1,
A_z=A+C,
B_z=B+z^2D.
```

For `z=omega^2`, these reduce to

```
A_z=s_0+s_1+t_0+t_1,
B_z=1+omega^2s_0+s_1+t_0+omega t_1,
B_z^sigma=1+omega s_0+s_1+t_0+omega^2t_1.
```

The two complete target coordinates are

```
F_z,+(X,Y)=alt((C tensor A_z)X
                  +(D^sigma tensor B_z^sigma)Y),
F_z,-(X,Y)=alt((D tensor B_z)X
                  +(C^sigma tensor A_z^sigma)Y).
```

## Six source terms and literal cancellation

Put

```
alpha=(0011)^infinity,
beta =(0110)^infinity,
gamma=(1001)^infinity,
delta=(1100)^infinity,
epsilon=1beta.
```

The four periodic tails are distinct. The additional tail
`epsilon` is outside that periodic core. The needed prefix
identities are

```
s_0 beta=alpha,      s_1 beta=epsilon,
t_0 beta=delta,      t_1 beta=0,
s_1 alpha=gamma,     t_1 alpha=0,
s_1 gamma=delta,     t_1 gamma=alpha.
```

Take

```
x=alpha+omega(beta+gamma),
y=omega alpha+beta+gamma,
X=x tensor beta,
Y=y tensor beta.                                    (1)
```

This source is nonzero. To check both full target coordinates,
abbreviate

```
t=alpha+delta+epsilon,
e=alpha+omega beta,
e'=alpha+omega^2 beta.
```

Direct application of the displayed prefix identities gives

```
A_z beta=t,
B_z^sigma beta=t+omega^2e,
C x=omega t+omega^2e,
D^sigma y=omega(t+e).
```

Consequently the plus target is

```
(omega t+omega^2e) wedge t
  +omega(t+e) wedge (t+omega^2e)=0.
```

For the minus target, the same identities give

```
B_z beta=t+omega e',
D x=t+e',
C^sigma y=t+omega^2e'.
```

Thus its value is

```
(t+e') wedge (t+omega e')
  +(t+omega^2e') wedge t=0.
```

Both cancellations use the alternating exterior product in
characteristic two: `v wedge v=0` and
`v wedge w=w wedge v`. They verify the whole two-sector
map on (1), including its off-core output terms.

## Binary descent and a witness for the actual chart

The tensors in (1) obey `Y=omega X^sigma`. Multiplying
both by `omega` therefore gives a Frobenius-fixed source
pair `(X',Y')`, with `Y'=X'^sigma`. This is a nonzero
source over `F_2`.

Apply the actual-candidate source change `S_z=tau D_z`
to this scaled source. Since `z=omega^2`, the resulting
pair is

```
X_T=beta tensor (alpha+omega(beta+gamma)),
Y_T=beta tensor (alpha+omega^2(beta+gamma))=X_T^sigma.
```

It lies in the kernel of `T_z`, since `E_z` is invertible.
Here is the same source as an explicit binary exterior vector.
For a tail `xi`, write

```
P xi=(e_1+e_3)xi,       Q xi=(e_2+e_4)xi,
R xi=e_1xi,             S xi=e_2xi,
d=beta+gamma.
```

Then

```
w_T=P beta wedge (S alpha+(R+S)d)
       +Q beta wedge ((R+S)alpha+R d).               (2)
```

Expanding `k_+(beta,alpha)+k_-(beta,alpha)` gives the
`alpha` terms in (2). Expanding
`omega k_+(beta,d)+omega^2 k_-(beta,d)` gives its
`d` terms. Hence (2) is exactly the pair `(X_T,Y_T)` in
the standard source parametrization.

The source parametrization is injective and has image
`im f_0`. Since `X_T` is nonzero,

```
f_0 w_T=w_T != 0,       T_z w_T=0.                   (3)
```

Therefore no group-ring element `L` can satisfy
`L T_z=f_0`: applying such an identity to `w_T` would
contradict (3). The boundary representation is available for
the ambient Leavitt unit group; equivalently one may restrict
a proposed identity to the subgroup containing its displayed
chart factors by the usual group-algebra conditional
expectation. This conclusion concerns this actual factored
left-and-right chart correction, not merely the auxiliary
natural map.

## Discovery, structural origin, and remaining scope

The analytic periodic-support reduction made a finite core
the relevant search domain. The outside-core contraction
equations for `z=omega^2` leave a scalar tensor on the
preceding-zero tails; the core `(0011)^infinity` was an
explicit next seed from those equations.

One capped, single-core MSI probe completed normally in
1.049 seconds. It found (1) on that core and recovered the
same witness on the union with the `(011)^infinity` and
`(0101011)^infinity` cores. No job remained running. The
proof is the explicit algebra above and does not depend on
the finite rank computation.

The `z=omega` candidate subsequently received a complete
ordinary exterior-square injectivity proof and was then
excluded by the [contragredient certificate](kaplansky-contragredient-period-two-kernel-excludes-omega-split-2026-09-08.md).
The earlier natural injectivity of both `H_z` remains valid;
this certificate shows why natural injectivity does not
imply injectivity of the full projected exterior map.
No Kaplansky conjecture resolution is claimed.
