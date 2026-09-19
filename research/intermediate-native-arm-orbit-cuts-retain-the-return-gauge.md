---
rg: 2
id: intermediate-native-arm-orbit-cuts-retain-the-return-gauge
kind: claim
title: Intermediate native-arm orbit cuts either lose the opposite arm or retain the independent return gauge
artifacts:
  - experiments/intermediate_orbit_spectral_cut_fence.py
  - research/intermediate-native-arm-orbit-cut-fence-proof.md
distinct_from:
  reverse-return-has-native-arm-leavitt-diamond: that attaches each constant reverse return to both literal non-Boolean arms and leaves one intermediate reducing cut as the next target; this audits exactly that smallest cut.
  native-inverse-pair-seven-orbits-retain-external-gauge: that proves the two odd seven-orbit norm relations and gives a moving-chart gauge model; this classifies the hard spectral cuts of one complete orbit and explains why adjoining the opposite orbit still does not read the gauge.
  fixed-packet-correction-retains-multiplicity-gauge: that is the general Schur-form packet fence; this is the concrete three-bit Pauli--Singer instance forced by the literal intermediate inverse pair.
---

**ESTABLISHED MINIMAL INTERMEDIATE-CUT FENCE.**  In row one put

```text
p=C_1=x_97(t_0),       q=D_1=x_76(s_0),
n=[p,q]=x_96(1),       T=J_1B_2A_1,
p_k=T^k p T^(-k),      q_k=T^k q T^(-k).              (ICF1)
```

On the marked `n=-1` sector, the exact cross-commutator table `(NIO7)` has
rank three over `F_2`.  Thus the seven `p_k` generate the three-qubit
translation row and the seven `q_k` generate its full dual modulation row.
In particular

```text
C^*(p_0,...,p_6,q_0,...,q_6)|_(n=-1)=M_8(C).          (ICF2)
```

There are nonzero hard cuts for one intermediate orbit, but they do not
solve the occurrence problem.  The commuting algebra

```text
A_p=C^*(p_0,...,p_6)|_(n=-1) ~= C^(F_2^3)             (ICF3)
```

has exactly two nonzero proper `T`-invariant spectral projections: the
Fourier zero-character atom `r_0` and its seven-character complement
`r_*`.  Their relative label ranks are `1/8` and `7/8`.  The opposite arm
`q=q_0` translates Fourier labels by a nonzero character, so

```text
q r_0 q^* != r_0,                q r_* q^* != r_*.    (ICF4)
```

Consequently neither proper orbit cut reduces the opposite factor.  The
compressed commutator cannot be read there as the returned involution on
one matrix carrier.  The same statement holds with the two arms exchanged.

Adjoining both orbit rows does not produce a finer native cut: `(ICF2)`
says that every **group-algebra** projection reducing both rows is scalar
on the three-bit label.  It therefore has the form

```text
I_8 tensor I_M                                             (ICF5)
```

on the fixed packet carrier and cannot inspect a multiplicity reflection.
An arbitrary projection in the commutant could cut `M`, but that is exactly
the unauthenticated analytic cut excluded by the occurrence problem.

The obstruction is exact, not merely a failure of this argument.  There is
a `32`-dimensional signed-permutation model of the minimal diamond/head
menu in which

```text
C=[U,A],       [C,q]=n,       JCJ=C',       JqJ=q',
[C',q']=n,     q'=[B,V],      T=JBA,        T^7=1,     (ICF6)
```

all seven forward orbit products of `C` and `q` are one, and `n` is a
nontrivial central marked reflection.  The native chart reflection `D`
and the returned reflection `n` act on different tensor factors:

```text
D != n,                    Dn != 1.                   (ICF7)
```

Every spectral projection built from the intermediate orbit rows and the
returned mark is amplified by the identity on the `D` factor.  Hence the
proper one-arm cuts in `(ICF4)` lose the other arm, while the full two-arm
cut in `(ICF5)` retains the independent gauge.  Fixed signed-Hecke or
native label projections do not change this conclusion: after packet
exactification they act on the finite label factor and are likewise blind
to `D`.

Row two is the prefix/index relabeling

```text
(p,q,n,T)=(x_28(t_00),x_87(s_00),x_27(1),J_2B_3A_2),
```

so it has the identical cut table.  A successful continuation must add a
second literal occurrence which crosses the one-arm Fourier split while
charging the multiplicity factor; neither a hard cut from one intermediate
orbit nor the fixed group algebra of both orbits supplies that charge.

No Property `(T)`, Kazhdan input, stability theorem, trace profile,
literature input, local computation, or Lean compilation is used.

DERIVATION
intermediate-native-arm-orbit-cut-fence-proof
