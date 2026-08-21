---
rg: 2
id: rcc-carrier-character-face-compression-proof
kind: route
title: HNN universality, one Cauchy-Schwarz equality, central cutting and Krein-Milman
target: rcc-carrier-character-face-compression
requires: []
---

**Setup.**  `T(H)` is the weak*-compact Choquet simplex of traces
(normalized conjugation-invariant positive definite functions) of `H`;
its extreme points are exactly the factorial characters (E. Thoma,
Math. Ann. 153 (1964); Sakai, C*-algebras and W*-algebras, 3.1.18).  A
trace is hyperlinear (Connes-embeddable) when its GNS von Neumann
algebra embeds trace-preservingly into a tracial matrix ultraproduct;
separable subalgebras of `R^omega` and of `prod_U M_(d_n)` interchange
by the standard diagonal argument, so the two receptacles define the
same class.

**Hyperlinear traces form a weak*-closed face of `T(H)`.**  Convexity:
the GNS algebra of `a tau_1 + (1-a) tau_2` embeds into the direct sum
of the two GNS algebras, and a direct sum of embeddable tracial
algebras is embeddable (amplify to a common ultraproduct and cut by
diagonal projections of matching trace).  Face: the GNS algebra of
each `tau_i` is a corner of the GNS algebra of the combination by a
central projection, and corners of embeddable algebras are embeddable.
Closedness: a weak*-limit of hyperlinear traces has all its finite
marginals approximated by matrix microstates, and a diagonal choice
over an increasing exhaustion realizes the limit trace in one matrix
ultraproduct (this is the standard closedness of the microstate
condition; see N. Ozawa, *About the Connes embedding conjecture*,
Jpn. J. Math. 8 (2013), §2).

**`delta_chi` is an extreme trace of `Gamma`.**  Since `Gamma/Z` is
ICC and `Z` is finite, the FC-center of `Gamma` is `Z` (a finite
conjugacy class maps to a finite class of `Gamma/Z`, hence to the
identity).  So the center of `L(Gamma)` is `span pi(Z)`, whose minimal
projections are the `p_chi = (1/|Z|) sum_z conj(chi(z)) pi(z)`; the GNS
algebra of `delta_chi` is the factor `L(Gamma) p_chi`.  Factorial
traces are extreme.

**Each `E_chi` is a closed face with factorial extreme points (part
2).**  `{tau : tau|_Gamma = delta_chi}` is weak*-closed and convex;
it is a face because restriction to `Gamma` is affine and `delta_chi`
is extreme in `T(Gamma)`.  Intersecting with the closed face of
hyperlinear traces keeps it a closed face.  For any face `F` of a
compact convex set, `ext F = F cap ext T(H)`; extreme traces of `H`
are factorial characters.

**Part 1, direction (RCC implies CF1).**  Let `tau in E_chi` and
suppose first `chi` is such that a full family is available; the
general case reduces to `tau|_Gamma = delta_e` as follows.  For each
character `chi'` of `Z`, the trace `delta_chi' compose q` of `H`
(where `q : H -> Gamma` kills `t`) is hyperlinear because `Gamma` is,
and restricts to `delta_chi'` on `Gamma`.  Then

```text
tau~ = (1/|Z|) ( tau + sum_(chi' != chi) delta_chi' compose q )
```

is hyperlinear (convexity) with `tau~|_Gamma = delta_e`.  Its GNS
algebra `N` embeds trace-preservingly in a matrix ultraproduct `M`;
`pi := pi_tau~|_Gamma` is then a trace-preserving regular-trace
representation of `Gamma` into `M`, and `k := pi_tau~(t)` is a unitary
of `pi(Lambda)' cap M` (the relations `[t, lambda] = 1` hold in `H`,
so the commutation is exact).  `(RCC)` gives `k in pi(Gamma)' cap M`,
so for every `gamma`,
`tau~(t^(-1) gamma^(-1) t gamma) = tau(k^* pi(gamma)^* k pi(gamma))
= 1`.  Since `tau~(w)` is the average of `|Z|` complex numbers of
modulus at most `1`, one of which is `tau(w)` and the rest equal to
`(delta_chi' compose q)(w) = delta_chi'(gamma^(-1) gamma) = 1` for the
commutator words `w = t^(-1) gamma^(-1) t gamma`, the average being
`1` forces `tau(w) = 1`.  That is `(CF1)` for `tau`.

**Part 1, direction (CF1 implies RCC).**  Let `M` be a tracial matrix
ultraproduct, `pi` a trace-preserving regular-trace representation of
`Gamma`, and `k in pi(Lambda)' cap M` a unitary.  By the universal
property of the presentation of `H`, `gamma |-> pi(gamma)`,
`t |-> k` defines a unitary representation `pi~` of `H` in `M`
(the relations `[t, lambda] = 1` are satisfied exactly).  Then
`tau_H := tau compose pi~` is a trace of `H`, hyperlinear because
`W*(pi~(H)) subseteq M`, with `tau_H|_Gamma = delta_e`.  Cut by the
minimal spectral projections `p_chi` of the central subgroup
`pi~(Z) subseteq Z(pi~(H)'')` (`Z` is central in `H`: it is central in
`Gamma` and `t` commutes with `Z subseteq Lambda`): whenever
`tau_H(p_chi) != 0` the normalized corner trace `tau_chi` is
hyperlinear with `tau_chi|_Gamma = delta_chi` (a direct computation
from `tau_H|_Gamma = delta_e`, as `tau_H(p_chi gamma) =
(1/|Z|) chi(gamma) 1_Z(gamma)`), so `tau_chi in E_chi` and `(CF1)`
gives `tau_chi(t^(-1) gamma^(-1) t gamma) = 1`; averaging back,
`tau_H(t^(-1) gamma^(-1) t gamma) = 1` for every `gamma`.  Now the
Cauchy--Schwarz equality: `tau(k^* pi(gamma)^* k pi(gamma)) = 1` is
the inner product in `L^2(M)` of the unit vectors `k pi(gamma)` and
`pi(gamma) k`, so they are equal, and faithfulness of the trace gives
`k pi(gamma) = pi(gamma) k`.  Hence `k in pi(Gamma)' cap M`; since a
von Neumann algebra is spanned by its unitaries,
`pi(Lambda)' cap M subseteq pi(Gamma)' cap M`, and the reverse
inclusion is automatic.  This is `(RCC)`.

**Part 3.**  Fix `chi`.  The set `F = {tau in E_chi : tau satisfies
(CF1)}` is weak*-closed (each condition `tau(w) = 1` is closed) and
convex (an average of values of modulus at most one equals `1` only if
all equal `1` -- and conversely trivially).  If `F` contains
`ext E_chi` then, by Krein--Milman applied to the compact convex
`E_chi`, `E_chi = closed conv hull ext E_chi subseteq F`.  Combined
with parts 1 and 2 this is the factorial reduction.
