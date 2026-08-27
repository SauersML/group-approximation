# One parahoric packet has an exact trace-zero spectator gauge

Put

```text
C=SL_3(Z),
D=C intersect h C h^(-1),
D'=h^(-1) D h,
h=diag(2,1,1/2).
```

The index is `[C:D]=42`.  A finite-dimensional one-edge Hecke packet is a
representation `pi:C->U(H)` together with a unitary `H_0` satisfying

```text
H_0 pi(d') H_0^* = pi(h d' h^(-1))       (d' in D').    (PMG1)
```

For the arithmetic double there are two such transports `H_0,H_1` over the
same `C` representation.  Fix any such packet and any `m>=2`.  On
`H tensor C^m` define

```text
pi'(c)=pi(c) tensor I_m,
H'_0=H_0 tensor I_m,
H'_1=H_1 tensor V,                                      (PMG2)
```

where `V in U(m)` is arbitrary.  Since the whole `C` action is trivial on
the second factor, both transports satisfy exactly the same parahoric
equations.  Every `C`-type multiplicity and every source Hecke incidence
number is merely multiplied by `m`; normalized multiplicity flow is
unchanged.  But

```text
tr(H'_0 (H'_1)^*)
 =tr(H_0 H_1^*) tr_m(V^*).                              (PMG3)
```

Taking `V` to be the cyclic shift makes the local fold coefficient zero.
This works even from the trivial seed `pi=H_0=H_1=1`.

The obstruction is not poor expansion of the forty-two coset graph.  For
any finite `S subset C`, the conjugation Dirichlet form

```text
E_S(X)=sum_(s in S)||[X,pi'(s)]||_2^2                   (PMG4)
```

vanishes on every `X=I_H tensor V`, including trace-zero unitaries a fixed
distance from the scalars.  Thus source/coset expansion has an exact
spectator algebra in its kernel.

The one-edge packet must be replaced by a loop with nonzero corrector
holonomy.  The repository already contains the endpoint:
`native-parahoric-triangle-kills-all-corrector-gauges` kills an arbitrary
common-carrier gauge with a dimension-free normalized-HS bound.  The
remaining projective-double task is therefore

```text
joint canonical matrix coordinates + six parahoric transports
  ==> one common positive-density multiplicity carrier
      on which the rank-two triangle relations hold.          (PMG5)
```

The phrase common carrier is load-bearing.  This is a local no-go only;
global `A` relations may kill the spectator gauge, as they do in exact
finite-dimensional representations of the whole double.
