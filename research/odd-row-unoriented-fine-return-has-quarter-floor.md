---
rg: 2
id: odd-row-unoriented-fine-return-has-quarter-floor
kind: claim
title: An odd row plus an unoriented fine return has a quarter-type Hilbert--Schmidt floor
distinct_from:
  odd-selector-row-balances-or-kills-outer-action: that shows the odd row alone admits a balanced exact model; this identifies the strictly weaker extra incidence which eliminates that model.
  primitive-clifford-type-fixes-orientation-not-return: that cuts one pure controller type and observes the coarse/fine rank mismatch; this allows the return to use both controller orientations and proves the odd row pays the wrong one.
  phase-tagged-row-defect-reduces-to-within-type-selector-mismatch: that splits a general tagged return into off-type and within-type errors; this gives the exact two-orientation identity for the controlled Clifford packet.
---

**ESTABLISHED.**  Work in an exactified representation of the controlled
two-qubit Pauli group.  Let `z_+,z_-` be its two marked primitive spin-type
projections, let

```text
Q=z_++z_-,              t z_+= C z_+,       t z_-=-C z_-,
C=1-2f,                 e=(1-r)/2,          r in P,    (OUF1)
```

where `e` is a coarse Pauli half-atom and `f` is the fine rank-one Pauli
atom.  Thus

```text
tau(ez_+)=tau(z_+)/2,          tau(fz_+)=tau(z_+)/4.    (OUF2)
```

For every unitary `W`, put

```text
A=||(1-fQ)W e z_+||_2^2,
D=||t-WrW^*||_2.                                      (OUF3)
```

Then the exact dimension-free inequality is

```text
boxed:  tau(z_+)/4 <= A+D^2/4.                         (OUF4)
```

Indeed, since `re=-e`,

```text
(t-WrW^*)W e z_+=(1+t)W e z_+.                        (OUF5)
```

On the `z_+` output type, `(1+t)/2=1-f`; on the `z_-`
output type, `(1+t)/2=f`.  Hence `D^2/4` dominates the
two orthogonal pieces

```text
||(z_+-fz_+)W e z_+||_2^2+||fz_-W e z_+||_2^2.        (OUF6)
```

The term `A` contains every output piece outside the unoriented fine carrier
`fQ`: the unmarked part, `(z_+-f)`, and `(z_--f)`.  Together `(OUF3)` and
`(OUF6)` therefore cover every part of `W e z_+` except `fz_+`.  That last
part has trace capacity at most `tau(fz_+)=tau(z_+)/4`, while
`||Wez_+||_2^2=tau(ez_+)=tau(z_+)/2`.  Subtraction proves `(OUF4)`.

This is robust with no dimension loss.  If finite-group exactification
changes `e,f,z_+,z_-` by total normalized `2`-norm at most `kappa`, then a
fixed contraction telescope gives

```text
tau(zhat_+)/4
 <=||(1-fhat Qhat)W ehat zhat_+||_2^2
   +(1/4)||t-WrW^*||_2^2+O(kappa).                    (OUF7)
```

For the fixed finite packet, flexible HS stability has
`kappa=O(sqrt(E_packet))`.  In canonical microstates
`tau(zhat_+)=1/4+o(1)`, so the two displayed row energies have the fixed
ambient floor `1/16-o(1)`.

The key relaxation is that the first term does **not** ask `W` to return the
source into the pure `z_+` reservoir.  It asks only for the unoriented union
`f(z_++z_-)`.  The two fine orientation pieces together have canonical
trace `1/8`, exactly equal to the source trace `tau(ez_+)=1/8`.  Thus this
incidence is compatible with the rectangular/balanced finite model.  The
ordinary odd word `t=WrW^*` then charges precisely the fine mass which lands
in the wrong orientation.

Consequently a fixed-depth proof no longer needs to suppress arbitrary
off-type leakage directly.  It is enough to prove the single typed-support
estimate

```text
||(1-fQ)W e z_+||_2^2
 <= C_N (mixed affine-Leavitt/Steinberg energy+trace error). (OUF8)
```

for the signed Whitehead word.  The odd row supplies the second term of
`(OUF4)` as an ordinary relator.  Establishing `(OUF8)` from the actual
coefficient occurrences remains the matrix-only gate.

