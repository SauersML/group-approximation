# Regular-table local H1 restatement firewall (2026-08-30)

## Result

The proposed premise `regular-table-defects-are-short-edge-h1-trivial` is,
at the qualitative asymptotic level used by the spherical program, exactly
the conclusion `spherical-short-holonomies-admit-local-gauge` in
nonabelian-cohomology notation.  Therefore
`regular-table-local-h1-gives-spherical-gauge` is circular and must not
count as a route.

This result does not decide the gauge claim or Q3.4.  It identifies what a
noncircular replacement must supply: an explicit bounded filler or an
independently proved matching-selection theorem, not the assertion that the
desired local class vanishes.

## 1. The asymptotic local coefficient group

Take any sequence of clouds `X_n={x_1,...,x_(N_n)}` and shadow
permutations `sigma_(s,n)`.  Let

```text
P = product_n Sym(X_n) / N_Ham,
```

where `N_Ham` consists of sequences equal to the identity off `o(N_n)`
points.  Define `L <= P` by

```text
[c_n] in L  iff  for every a>0,
 |{i: ||x_i-x_(c_n(i))||>a}|/N_n -> 0.                 (RHF1)
```

This is the invariant formulation of “moves all but `o(N)` points by a
radius tending to zero.”  It is well defined modulo `N_Ham`.

`L` is a group.  If `c_n,d_n` satisfy `(RHF1)`, the triangle inequality
gives

```text
||x_i-x_(c_n d_n(i))||
 <= ||x_i-x_(d_n(i))||
  + ||x_(d_n(i))-x_(c_n d_n(i))||.                     (RHF2)
```

The bad set for the second term is the `d_n`-preimage of a bad set for
`c_n`, hence has the same density.  The inverse case is identical after a
permutation change of variables.

Every tight shadow sequence normalizes `L`.  If `sigma_(s,n)` shadows
the isometry `U_(s,n)` with error tending to zero in measure, apply the
shadow estimate at `i` and at
`(sigma_s^(-1)c sigma_s)(i)`.  The middle displacement is a relabeling of
the displacement of `c`, and the two outer errors vanish.  This is the
in-measure version of the shadow-conjugation estimate.

Thus the short-edge coefficients required by the gauge law are an honest
asymptotic group stable under exactly the conjugations occurring in that
law.

## 2. Trivial local H1 means a local gauge exists

For each tested relation `r=(g,h,k)`, put

```text
delta_r = sigma_k^(-1) sigma_g sigma_h.
```

`spherical-relation-defect-pairs-small-chord`, followed by pullback
through the tight `k` shadow, gives `[delta_r] in L`.

Whatever relation-of-relations complex is used to package these defects,
saying that their nonabelian torsor class is trivial in the coefficient
group `L` has one operational meaning: there is a zero-cochain
`[c_s] in L` whose gauge kills every cell.  The exact cell equations are

```text
[c_k] = [delta_(g,h,k)
          (sigma_h^(-1)c_g sigma_h)c_h] in P.           (RHF3)
```

By `relation-defects-obey-permutation-gauge-law`, `(RHF3)` is equivalent
to

```text
(sigma_g c_g)(sigma_h c_h) = sigma_k c_k               (RHF4)
```

in `P`.  Equality in `P` means that the corresponding multiplication
relation fails on only `o(N_n)` roots.  Membership `[c_s] in L` means
that every correction is geometrically local off `o(N_n)` roots.  These
are exactly clauses 1--3 of
`spherical-short-holonomies-admit-local-gauge` along an asymptotic
sequence.

The converse is immediate: local corrections satisfying the target define
a zero-cochain in `L` satisfying `(RHF3)`, so the defect class is
trivial.

## 3. The finite tolerance formulations are equivalent

The sequence statement and the `eps`/tolerance statement are equivalent by
the usual diagonal argument.  If a uniform gauge theorem holds, apply it
with `eps=1/m` once the model, matching, and exceptional-set parameters
cross its `m`th thresholds.  Conversely, if no uniform thresholds exist
for some `eps_0`, choose for every `m` a regular-character model and
cloud with all input errors below `1/m` but with no admissible `eps_0`
correction.  The resulting sequence has a trivial local class only if it
has corrections with locality and relation error tending to zero,
contradicting the construction.

Therefore changing from asymptotic `H1` language to finite tolerances
creates no logical gap between the premise and target.

## 4. Why the quantitative torsor node does not rescue the route

`short-edge-gauge-torsor-h1-vanishes` asks for a sharper estimate, such as
correction radius `C_T rho` and exceptional density `C_T eta`, after
triviality in the local coefficient system is assumed.  Such a modulus may
be valuable.  But the consumer route also requires
`regular-table-defects-are-short-edge-h1-trivial`, and that prerequisite
already asserts existence of the local zero-cochain which is the qualitative
target.  A quantitative post-processing theorem cannot make that
prerequisite independent.

## 5. What a noncircular replacement would look like

A genuine special-table input must provide data stronger and more checkable
than the phrase “the class is trivial.”  One sufficient certificate would
be:

1. a fixed finite relation-of-relations complex for `T`;
2. for every label `s`, an explicit word `W_(s,T)` of uniformly bounded
   length in the defects `delta_r^(+/-1)`, transported only by bounded words
   in the shadow labels;
3. formal identities showing that `c_s=W_(s,T)(delta)` satisfy every gauge
   equation; and
4. a proof that each listed transport remains in the short-edge filtration,
   with the exceptional sets charged explicitly.

Subadditivity and the shadow-conjugation estimate would then give the
required local radius and density bounds.  No such filler is currently
supplied.  Ambient compatibility cannot supply it:
`ambient-h1-triviality-need-not-be-short-edge-local` gives the explicit
`D8` obstruction.

Absent an explicit certificate of this kind, the honest frontier remains
the original spherical gauge theorem itself.
