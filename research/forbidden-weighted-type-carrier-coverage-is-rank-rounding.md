---
rg: 2
id: forbidden-weighted-type-carrier-coverage-is-rank-rounding
kind: claim
title: Exhaustive marked types cover all forbidden mass after only constant-rank four-divisibility trimming
distinct_from:
  global-marked-type-cycle-selector-decoder: that assumes the global coverage estimate GTC5 and combines it with cyclic row domination; this proves GTC5 automatically for analytic type-compressed carriers
  exhaustive-marked-type-energy-summation: that packs already available relator-energy estimates over orthogonal type domains; this constructs rank-divisible coarse/fine carrier supports inside the forbidden type pieces before any row estimate is available
  common-partial-isometry-swap-game-compiler: that asks only for forbidden-weighted saturation of one common Gram source; this gives exact finite-rank saturation over an exhaustive type menu but does not authenticate the resulting transport rows
  algebraic-exhaustive-marked-type-detectors-violate-induction: that rules out operator estimates valid on induced infinite representations; the trimming here is a noncanonical finite-rank choice and asserts no group-algebra identity
---

**ESTABLISHED.**  Work after exactifying the finitely many context packets in
a matrix algebra `M_d(C)`.  For each context `c`, let `F_c` be its aggregate
forbidden joint-spectral projection and let

```text
Q_c=sum_(lambda in Irr_-(H_c))Q_(c,lambda)             (FWC1)
```

be its marked isotypic projection.  Assume only

```text
[F_c,Q_(c,lambda)]=0                                   (FWC2)
```

for every marked type.  Put

```text
R_(c,lambda)=F_c Q_(c,lambda).                         (FWC3)
```

These are projections, orthogonal as `lambda` varies inside one context, and

```text
sum_(c,lambda) tr_d(R_(c,lambda))
 =sum_c tr_d(F_cQ_c)=:E_forbid^mark.                   (FWC4)
```

For every `(c,lambda)`, choose a subprojection
`P_(c,lambda)<=R_(c,lambda)` whose rank is the largest multiple of four not
exceeding `rank(R_(c,lambda))`.  Then

```text
sum_(c,lambda) tr_d(P_(c,lambda))
 >=E_forbid^mark-3|Omega|/d,                           (FWC5)
```

where `Omega` is the fixed finite marked context-type menu.  Each nonzero
`P_(c,lambda)` admits exact analytic `M_2` and `M_4` matrix-unit systems with
common identity `P_(c,lambda)`.  In particular one can choose selectors

```text
e_(c,lambda),f_(c,lambda)<=P_(c,lambda),
tr(e)=tr(P)/2,                 tr(f)=tr(P)/4.           (FWC6)
```

Thus `(GTC5)` of `global-marked-type-cycle-selector-decoder` is automatic
with `alpha=1` and `zeta(delta)=o(1)` whenever its `E_forbid` is the marked
forbidden mass `(FWC4)`.  Fixed finite-group exactification and context
rounding add only their existing dimension-independent vanishing modulus to
the explicit `3|Omega|/d` loss.

No single context or type is selected.  A forbidden piece of rank below four
may be discarded completely, but the total discarded rank is bounded by a
constant because the menu is fixed.  Hence positive global forbidden mass
cannot disappear into many tiny types as dimension grows.

## Reducing-carrier qualification

The projections in `(FWC5)` are analytic subspaces of the isotypic blocks;
they need not reduce the full context packet.  If the stronger commutation

```text
F_cQ_(c,lambda) in pi(H_c)'Q_(c,lambda)                (FWC7)
```

holds, write the type block as
`V_lambda tensor C^(m_lambda)` and
`R_(c,lambda)=I_(V_lambda) tensor R_lambda`.  Trimming the multiplicity rank
to a multiple of four gives an `H_c`-reducing `P_(c,lambda)` and loses less
than

```text
4 dim(V_lambda)/d                                     (FWC8)
```

in normalized trace.  Summed over the fixed menu this is still `o(1)`.

Without `(FWC7)`, reducing coverage is false even at positive density.  On
one isotypic block `V_lambda tensor C^m` with `dim(V_lambda)>1`, choose a unit
vector `v in V_lambda` and put

```text
F=|v><v| tensor I_m.                                   (FWC9)
```

It commutes with the central type projection and has normalized trace
`1/dim(V_lambda)`, but contains no nonzero `H_c`-reducing projection.  Every
such reducing projection has the form `I_(V_lambda) tensor P_0`, whose range
cannot lie in `Cv tensor C^m` unless `P_0=0`.

Therefore `(GTC5)` is solved **for the marked forbidden mass**
`E_forbid^mark` of `(FWC4)`: it holds with `alpha = 1` whenever the
`E_forbid` of `global-marked-type-cycle-selector-decoder` -- the forbidden
mass of the original shared BCS tuple, before its context occurrences are
separated -- is concentrated on the marked type menu, and in general only
with `alpha = E_forbid^mark / E_forbid`.  That concentration is a separate
input which this node does not prove (qualifier restored 2026-08-22).  The
other surviving issue is GTC4:
authenticate transports on these noncanonical forbidden-weighted subspaces,
or prove the extra packet covariance `(FWC7)` with a finite-matrix modulus.
Replacing the analytic carriers by packet-reducing ones silently reintroduces
the source-alignment problem.
