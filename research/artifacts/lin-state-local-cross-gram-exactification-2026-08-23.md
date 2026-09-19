# Lin state-local exactification and positive-cross-Gram rounding

Source: Junqiao Lin, *Tracially embeddable strategies: Lifting MIP* tricks
to MIPco*, arXiv:2304.01940v3, especially Theorem 5.1, Lemma A.2, and
Proposition A.8. The identities below are direct consequences of the
displayed constructions in the source; the cross-Gram estimates are
self-contained matrix calculations.

Throughout, `tau` is normalized trace and `||.||_2` is normalized
Hilbert--Schmidt norm.

## 1. The displayed Gowers--Hatami map is a state-local intertwiner

Let `K` be finite, let `phi:K->U(A)`, and let `xi` be the vector defining
the state-dependent seminorm. Lin uses

```text
V xi_0=|K|^(-1/2) direct_sum_(g in K) phi(g^(-1))xi_0,
Phi(a)=I tensor L_a.
```

Reading the coordinates before compressing gives

```text
||(Phi(a)V-Vphi(a))xi||^2
 =E_g||(phi(g^(-1)a)-phi(g^(-1))phi(a))xi||^2,         (SLG1)

E_a||(Phi(a)V-Vphi(a))xi||^2
 =E_(g,a)||(phi(g)phi(a)-phi(ga))xi||^2.               (SLG2)
```

For every `U in A` the same coordinate calculation gives

```text
||((U tensor I)V-VU)xi||^2=E_g||[U,phi(g)]xi||^2.      (SLG3)
```

Lin's exact locality identity is

```text
VB=(B tensor I)V                 for every B in A'.   (SLG4)
```

Thus if a reference packet `psi(a) in A'` satisfies
`E_a||(phi(a)-psi(a))xi||^2<=eta`, then

```text
E_a||(Phi(a)-psi(a) tensor I)Vxi||^2
 <=2 D_mult+2 eta,                                     (SLG5)
```

where `D_mult` is the right side of `(SLG2)`. This is stronger than a
compression-close statement: exactification retains the original
state-dependent multiplication error as an intertwining error and leaves
the complete opposite algebra fixed.

It does not protect an unrelated *left* carrier. Equation `(SLG3)` says
precisely that such protection costs its commutator energy with the packet.

## 2. Two transports make their cross-Gram covariant

Let `A_s,B_s` be unitaries and `T_1,T_2` contractions, and put

```text
eta_(i,s)=||A_sT_i-T_iB_s||_2,
G=T_1^*T_2,
H=G^*G,
m=tau(H)=||G||_2^2.
```

The exact telescoping

```text
B_s^*T_1^*T_2B_s-T_1^*T_2
 =(B_s^*T_1^*-T_1^*A_s^*)T_2B_s
  +T_1^*A_s^*(T_2B_s-A_sT_2)
```

and contractivity give

```text
||B_s^*GB_s-G||_2<=eta_(1,s)+eta_(2,s),
||B_s^*HB_s-H||_2<=2(eta_(1,s)+eta_(2,s)).             (CG1)
```

No product of the two errors occurs.

## 3. Positive mass gives a fixed-density reducing cut

Put `P_lambda=1_[sqrt(lambda),infinity)(H)`. Connes'
joint-distribution estimate, applied to `H` and `B_s^*HB_s`, together with
`(CG1)`, yields

```text
integral ||[B_s,P_lambda]||_2^2 d lambda
 <=4 sqrt(m)(eta_(1,s)+eta_(2,s)).                     (CG2)
```

Because `0<=H<=I` and `tau(H)=m`, every
`lambda in [m^2/16,m^2/4]` satisfies

```text
tau(P_lambda)>=m/(2-m)>=m/2,
HP_lambda>=(m/4)P_lambda.                              (CG3)
```

The interval has length `3m^2/16`. Hence for arbitrary finite weights
`w_s>=0`, one cut `P` in that interval obeys

```text
tau(P)>=m/2,
HP>=(m/4)P,
sum_s w_s||[B_s,P]||_2^2
 <=(64/3)m^(-3/2)sum_s w_s(eta_(1,s)+eta_(2,s)).       (CG4)
```

Thus fixed positive cross-Gram mass plus vanishing same-packet transport
error gives a fixed-density, dimension-free approximately reducing corner.
Near-full overlap is unnecessary.

For the unweighted finite packet, reparameterizing the cut directly by the
threshold `t in [m/4,m/2]` sharpens the last bound. If
`D=sum_s(eta_(1,s)+eta_(2,s))`, the coarea calculation in
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner` gives

```text
sum_s||[P,B_s]||_2^2<=8D/m.                            (CG5)
```

This sharper form is the one wired into the Iwahori lane. It also records
the necessary fourth-root loss when the input is stated as squared
transport energy and no spectral gap for `H` is available.

## 4. The Gram state rounds to one PVM packet

Let `(P_a^x)_a` and `(Q_a^x)_a` be PVMs, let `G` be a contraction, and put

```text
m=||G||_2^2>0,
E=E_x sum_a||P_a^xG-GQ_a^x||_2^2.                     (PVM1)
```

Write `G=sigma U`, extend the polar part to a unitary, set
`s=sigma/sqrt(m)`, and put `Qtilde_a^x=UQ_a^xU^*`. The associated
standard-form strategy is exactly

```text
delta=E/(2m)                                           (PVM2)
```

synchronous. Lin's symmetrization and Proposition A.8, applied to this
Gram state, give a cut `R` and one PVM packet `(C_a^x)` on `R` such that,
for every fixed `m>=m_0>0`,

```text
tau(R)>=m_0/2,
E_x sum_a||(P_a^x-C_a^x)R||_2^2
 +E_x sum_a||(Qtilde_a^x-C_a^x)R||_2^2
 <=O_(m_0)((E/m)^(1/4)).                              (PVM3)
```

The unsquared Hilbert--Schmidt error is
`O_(m_0)((E/m)^(1/8))`. The polar-gauged second-packet estimate uses the
lower spectral bound on `sR` and the decomposition

```text
(P_a-Qtilde_a)R
 =(P_as-sQtilde_a)s^(-1)R
  +(sQtilde_a-Qtilde_as)s^(-1)R.                       (PVM4)
```

## 5. One labelled block contraction removes branch synchronization

For orthogonal labelled source and target PVMs `(E_i)` and `(F_i)`, with
branch contractions `T_i` having the corresponding source/range support,
put

```text
G=sum_i F_iT_iE_i.                                    (BLK1)
```

Orthogonality makes `G` a contraction and gives, identically,

```text
F_iG=GE_i.                                            (BLK2)
```

Label synchronization therefore costs zero. A multi-branch construction
now needs only (a) fixed mass in this same `G`, and (b) covariance of the
genuinely mixed/root/return words on this same `G`. Sections 1--4 then
produce a positive common packet corner and exactify a finite packet
locally.

## 6. Exact Cairn boundary

This package does not create the required mixed relation. It also does not
make the spectral cut or polar unitary an ordinary group word, force
holonomy from cross-Gram mass alone, kill an anonymous tensor spectator, or
promote one chosen state-dependent trace to the canonical group trace.

The remaining certificate in every application is therefore the same
finite-coordinate statement:

```text
||G||_2^2>=m_0,
E_(s in F)||L_sG-GR_s||_2^2
 <=omega(delta)||G||_2^2,                              (MG)
```

for one word-controlled `G` and one fixed packet `F`, with all genuinely
mixed rows evaluated on that same operator. The package proves the whole
analytic implication after `(MG)`.

## 7. Cairn wiring

The package is split into the established nodes

```text
lin-state-local-gh-is-an-intertwining-exactifier,
two-transport-cross-gram-has-a-fixed-mass-reducing-corner,
labelled-pvm-branch-gram-gives-lin-corner,
positive-cross-gram-state-rounds-to-common-pvm.
```

`lin-cross-gram-localizes-authenticated-iwahori-overlap` records the exact
Iwahori scope: authenticated positive overlap is now localizable, while raw
UGO supplies neither the two transports nor an energy-paid complement.
`capacity-gated-s3-endpoint-common-source-cell` uses the labelled block
identity to delete its separate source-commutator row. If the original two
endpoint covariance rows are retained, `one-s3-row-rounds-joint-source-pvm`
constructs the joint source PVM with explicit linear loss, and the fully
labelled downstream endpoint reduces to the same-reservoir mass floor
`(SEC8)`. In the hypothesis-minimal one-bit formulation, the honest endpoint
is instead `(SEC12)`: fixed mass plus the unanchored endpoint, transitive-role,
and return covariance on the **same** `G_X`. The static BCS compiler and Atlas
mixed-carrier node now explicitly stop only before their same-Gram mixed-word
certificates, not before analytic corner extraction.
