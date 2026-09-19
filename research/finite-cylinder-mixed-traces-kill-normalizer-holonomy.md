---
rg: 2
id: finite-cylinder-mixed-traces-kill-normalizer-holonomy
kind: claim
title: Cylinder-resolved canonical traces kill every exact finite normalizer holonomy
distinct_from:
  exact-bernoulli-lamp-trace-forces-actor-residual-finiteness: that starts with exact representations of the whole infinite wreath product and extracts finite character actions; this is the finite transformation-groupoid calculation which removes the remaining stabilizer-unitary gauge once a coherent finite actor action has already been obtained.
  finite-subgroup-near-regular-has-large-regular-core: that extracts a regular core from the scalar character of one finite subgroup; this uses mixed atom-actor traces to regularize every point-stabilizer representation compatibly with the PVM and hence permutationizes the whole finite transformation groupoid.
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that exhibits arbitrary unitary fibers from covariance alone; this proves that the mixed canonical traces, resolved on every cylinder atom, force those fibers to be regular stabilizer representations and hence permutationizable.
  scalar-trace-of-diagonal-normalizer-is-permutation-blind: that gives a one-normalizer phase obstruction under scalar trace information; this gives both the stronger hypothesis which defeats the obstruction and an exact two-atom witness showing that scalar actor traces still do not suffice.
---

**ESTABLISHED.**  Let a finite group `H` act on a finite set `Omega`.  On a
finite-dimensional Hilbert space `V`, let

```text
{P_omega : omega in Omega}
```

be a PVM and let `U:H->U(V)` be an exact representation satisfying

```text
U_h P_omega U_h^* = P_(h omega).                       (FCM1)
```

Write `tr` for the trace normalized by `d=dim(V)`.  If

```text
tr(P_omega U_s)=0
for every omega and every 1 != s in H_omega,           (FCM2)
```

then there is an orthonormal basis of `V` in which every `P_omega` is a
coordinate projection and every `U_h` is a permutation matrix.  Thus
cylinder-resolved canonical trace removes not only diagonal phases but every
unitary multiplicity fiber, jointly and coherently for the whole finite actor
table.

The statement has a quantitative regular-core form.  Suppose instead that

```text
|tr(P_omega U_s)| <= beta                              (FCM3)
```

for the same pairs.  For an orbit representative `omega`, put
`K_omega=H_omega` and let `r` be the number of `H`-orbits on `Omega`.  There
is a reducing subspace `V_perm` for the PVM and for `U(H)` on which all the
operators are simultaneously permutation matrices, and

```text
dim(V minus V_perm)/d
 <= beta sum_(omega in H\Omega) |H omega|(|K_omega|-1)
      + r|H|/d.                                        (FCM4)
```

In particular the first constant is at most `r|H|`, is independent of the
ambient dimension, and `(FCM3)` with `beta=o(1)` gives a `1-o(1)` permutation
core along any sequence with `d->infinity`.  When `beta=0`, one may take
`V_perm=V`; the additive integrality term in `(FCM4)` is only an artifact of
the approximate estimate.

## Proof

Fix an orbit representative `omega`, set `K=H_omega`, and put
`V_omega=P_omega V`, `m=dim(V_omega)`.  The restriction

```text
sigma:K -> U(V_omega),       sigma(s)=U_s|_(V_omega)    (FCM5)
```

is an exact representation.  Covariance identifies the summand over the
whole orbit with `Ind_K^H(sigma)`.  In the exact case `(FCM2)`, the character
of `sigma` equals `m` at the identity and zero elsewhere.  Character
orthogonality says

```text
m_pi=(1/|K|) sum_(s in K) conjugate(chi_pi(s)) Tr(sigma(s))
    =m dim(pi)/|K|                                             (FCM6)
```

for every irreducible `pi` of `K`.  Hence `sigma` is a multiple of the left
regular representation of `K`.  Induction carries `lambda_K` to `lambda_H`.
Choose a regular basis of `V_omega`, transport it by coset representatives,
and do this independently on every orbit.  The transported basis vectors
stay in the appropriate `P_omega`-fibers, while left multiplication by `H`
permutes them.  This proves the exact assertion.

For `(FCM3)`, character orthogonality and `|chi_pi(s)|<=dim(pi)` give

```text
|m_pi-m dim(pi)/|K||
 <= d beta (|K|-1) dim(pi)/|K|.                       (FCM7)
```

Consequently `sigma` contains at least

```text
floor(m/|K|-d beta (|K|-1)/|K|)
```

copies of `lambda_K` (with zero understood if the displayed number is
negative).  The complement in `V_omega` has dimension at most

```text
d beta (|K|-1)+|K|.                                   (FCM8)
```

Inducing this regular subrepresentation over the orbit multiplies the bound
by `|H omega|`.  Its induced span is reducing for `U(H)` and the PVM, and the
transported regular basis again makes both structures permutation-valued.
Summing `(FCM8)` over orbit representatives gives `(FCM4)` because
`|H omega||K_omega|=|H|`.

## Bernoulli specialization

For a finite lamp window `F`, its character atoms are

```text
p_omega=2^(-|F|) product_(x in F)(1+omega_x c_x),
omega in {+-1}^F.                                     (FCM9)
```

Every mixed coefficient `tr(p_omega U_h)` is a fixed finite linear
combination of traces of group words `a h`, with `a` a lamp word supported
in `F`.  In the canonical group trace it is zero whenever `h!=1`; for `h=1`
the same expansion gives `tr(p_omega)=2^(-|F|)`.  Therefore regular trace
provides exactly `(FCM2)`, not merely a scalar condition on `tr(U_h)`.
After exact extraction of a finite transformation-group table, the actor
normalizer gauge is therefore completely classical: no property-`(T)` input
is needed.

What this does **not** do is produce that finite table.  In a normalized-HS
microstate the lamps on a fixed window may be exactified, but the actor
unitaries generally transport them to a different window and obey the actor
relations only approximately.  There is then no finite group `H` acting on
one common `Omega` to which `(FCM1)` applies.  Property `(T)` alone is not an
HS-stability theorem for the actor presentation.  Thus the fixed-cylinder
Bernoulli route has a precise reduced gate: coherent finite actor/table
extraction, not residual unitary holonomy after such extraction.

## Sharpness of cylinder resolution

Scalar canonical-looking actor traces do not imply the theorem.  Let
`H=C_2={1,s}` act trivially on two atoms, take

```text
P_0=1_(C^m) direct_sum 0,       P_1=0 direct_sum 1_(C^m),
U_s=1_(C^m) direct_sum (-1_(C^m)).                     (FCM10)
```

Then `(FCM1)` is exact and `tr(U_s)=0`, but

```text
tr(P_0U_s)=1/2,             tr(P_1U_s)=-1/2.           (FCM11)
```

Any permutation implementing the trivial atom action preserves the two
blocks.  On the negative block its normalized-HS squared distance from
`-1_(C^m)` is `2+2 Fix(q)/m>=2`; hence the global normalized-HS distance
from `U_s` is at least `1`.  This persists for arbitrary multiplicity and
shows that cancellation in `tr(U_s)` cannot replace the atomwise mixed
moments `(FCM2)`.
