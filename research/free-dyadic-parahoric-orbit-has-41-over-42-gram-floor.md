---
rg: 2
id: free-dyadic-parahoric-orbit-has-41-over-42-gram-floor
kind: claim
title: A free dyadic lamp orbit has a forty-one-over-forty-two parahoric Gram floor
invalidates:
  - sl3-dyadic-tower-exclusion-from-spectral-orbit-chart-pvm
distinct_from:
  free-hnn-outlier-has-dyadic-a2-pvm-tower: that constructs the coherent all-depth coset-indexed tower; this computes what happens when its spectral atoms are used to make the required index-forty-two chart.
  kesten-chart-carriers-have-25-over-42-gram-floor: that studies nonlinear Kesten cuts in overlapping free subgroups and obtains a twenty-five-over-forty-two lower bound; this treats every projection in one diffuse coset-lamp algebra and gives the exact forty-one-over-forty-two value.
  finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift: that identifies an arbitrary fundamental projection as an equivariant nonlinear embedding and leaves its unstabilized existence open; this proves that the spectral-orbit construction from the extracted dyadic tower is not such an embedding.
  raw-incidence-and-one-hot-pvms-tensor-separate: that begins with complete chart PVMs on independent tensor coordinates; this shows that the most direct orbit of the free dyadic tower does not even form one chart PVM.
---

Put

```text
C=SL_3(Z),       h=diag(2,1,1/2),
D=C cap hCh^(-1),       Omega=C/D,       |Omega|=42.   (FDO1)
```

In the free-HNN enemy of
`free-hnn-outlier-has-dyadic-a2-pvm-tower`, let `D_x` be the diffuse
abelian lamp algebra at `x in A/C`.  Choose coset representatives `g_i` for
`C/D` and put

```text
x_i=g_i hC.                                             (FDO2)
```

Every projection `E in D_(hC)` is fixed by `D`, because `D` fixes the coset
`hC` and the actor covariance fixes its lamp generator.  Hence

```text
E_i=pi(g_i) E pi(g_i)^*                                (FDO3)
```

is well defined and is an exactly `C`-covariant family indexed by `Omega`.
If `p=tau(E)`, then the distinct cosets in `(FDO2)` and free independence of
their lamp algebras give

```text
tau(E_i)=p,              tau(E_i E_j)=p^2   (i!=j).     (FDO4)
```

The standard free-projection meet formula also gives

```text
tau(E_i meet E_j)=max(2p-1,0).                          (FDO5)
```

Thus, at every `p<=1/2`, no nonzero literal carrier is subordinate to two
different orbit atoms.

This exhausts every **coset-local spectral decoder**: if a `C`-covariant
candidate chart has its atom at `g_iD` inside `D_(g_i hC)`, covariance makes
all its atoms translates of the base atom, so it has exactly the form
`(FDO3)`.

In particular, no finite dyadic atom can even have the chart rank: its
trace is `2^(-r)`, whereas a complete forty-two-atom chart requires trace
`1/42`.  Passing to the whole all-depth algebra removes that elementary
divisibility issue but not the carrier obstruction.  Since `D_(hC)` is
diffuse, choose `E` with `tau(E)=1/42`.  Then

```text
sum_i tau(E_i)=1,
sum_(i!=j) tau(E_i E_j)=42*41/42^2=41/42,              (FDO6)
```

and therefore

```text
||sum_i E_i-I||_2^2=41/42.                             (FDO7)
```

Thus the all-depth same-physical lamp tower does **not**, by taking a
spectral atom and its native parahoric orbit, yield even one decoded
forty-two-atom chart PVM.  Repeating the construction in the other five
Weyl charts gives the same obstruction separately in every chart, before
the common-carrier or native-triangle question is reached.

The scope is exact.  This does not prove that the ambient factor contains
no unrelated `D`-fundamental projection.  Such a projection would have to
mix several free coset algebras nonlinearly and solve the analogue of the
unstabilized equivariant-embedding problem `(FST1)` of
`finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift`.  Even after
that lift, denominator first-exit authentication is still needed before
`native-parahoric-triangle-kills-all-corrector-gauges` applies.  Hence the
dyadic tower and the common-carrier endpoint are separated by a genuine
nonlinear projection-multiplication gate; all-depth nesting alone does not
bridge them.

DERIVATION
free-dyadic-parahoric-orbit-gram-proof
