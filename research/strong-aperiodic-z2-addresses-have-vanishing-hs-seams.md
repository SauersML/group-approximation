---
rg: 2
id: strong-aperiodic-z2-addresses-have-vanishing-hs-seams
kind: claim
title: Strongly aperiodic two-dimensional address rules still have vanishing normalized-HS seam microstates
distinct_from:
  one-dimensional-address-rules-have-periodic-models: that gives exact periodic active models for one-dimensional finite-type rules; this handles genuinely strongly aperiodic two-dimensional rules, where exact periodic models are absent but approximate torus models have vanishing seam density.
  invariant-cartan-completion: that asks to recover a diagonal actor action from arbitrary Kun--Thom unitary microstates; this proves the separate robust finite-action gap and diagonal-classicalization hypotheses needed after leaving amenable seam models.
  kun-thom-compression-survives-amenable-near-model: that gives an actor-only charge-null exact representation; this computes the local-rule HS normalization and shows precisely why property (T) or expansion does not remove the Cartan-visible step.
  finite-memory-self-hash-non-mf: that asks for a finite self-hashing rule with a genuine finite-model floor; this proves that topological strong aperiodicity on an amenable two-dimensional host is insufficient for such a floor.
---

**ESTABLISHED VANISHING-SEAM COUNTERMODEL AND EXPANDER INTERFACE.**  Let
`X subset A^(Z^2)` be any nonempty finite-alphabet shift of finite type with
interaction radius `R`; `X` may be strongly aperiodic.  Choose `x in X`.
For every `N>2R`, color the torus

```text
Omega_N=(Z/NZ)^2
```

by copying `x` on the representatives `{0,...,N-1}^2`.  A radius-`R` check
can fail only at a site whose window crosses one of the two wrap seams.  Hence

```text
#bad_N/|Omega_N| <= 4R/N+O_R(N^(-2)).                  (ZSA1)
```

This is an exact unitary normalized-HS model of the address action.  On
`ell^2(Omega_N)`, let `U,V` be the two coordinate permutation shifts and let
`P_a` be the diagonal color PVM.  Then

```text
[U,V]=0
```

exactly, all packet/PVM rows are exact, and the translate of `P_a` is the
color projection at the translated site.  If `B_q` is the diagonal projection
of one forbidden local window `q`, then

```text
sum_q tr(B_q)=#bad_N/|Omega_N|=O_R(N^(-1)),            (ZSA2)
sum_q ||B_q||_2^2=O_R(N^(-1)).                         (ZSA3)
```

Thus every fixed reflection row `I-2B_q=I`, or every fixed packet word whose
failure is supported on `B_q`, has normalized-HS defect `O_R(N^(-1/2))`.
Take the payload projection `F=I`.  The active fiber is nonzero, the actor
relations are exact, and all local conditional defects tend to zero.  Strong
aperiodicity removes exact periodic points but gives no dimension-uniform
active-fiber HS floor.

The same proof works on any amenable address group along a Følner model: copy
one valid infinite configuration on a Følner set, and charge only its fixed
radius boundary.  The two-dimensional torus calculation is enough to refute
the proposed tree/2D successor whenever its nonstationarity is placed on an
amenable plane or grid inside the gadget.

## What an expander address would actually have to prove

For a nonamenable/Kazhdan actor, absence of Følner seams removes this particular
countermodel, but **strong aperiodicity is still only qualitative**.  The
finite-action hypothesis needed by the HS argument is the explicit robust
model gap

```text
inf_(finite canonical actor sets Omega, labelings c)
  #violated local checks(c)/|Omega| >= delta>0.         (ZSA4)
```

Expansion or property `(T)` does not formally imply `(ZSA4)` for an arbitrary
SFT; it controls almost-invariant Hilbert vectors, while `(ZSA4)` is a local
testability/cosystolic statement for the chosen constraint table.

Even `(ZSA4)` is not yet a unitary-HS theorem.  One also needs a
dimension-uniform **active Cartan classicalization**:

```text
an epsilon-representation on F
  -> an O(epsilon)-near finite permutation actor on a diagonal label PVM.
                                                               (ZSA5)
```

If `(ZSA4)--(ZSA5)` hold and the group-word defect controls the forbidden
window projections as in `(ZSA3)`, then summing their squared HS norms gives

```text
E_pres >= c_0 delta tr(F)-o(1),                         (ZSA6)
```

for a presentation-dependent `c_0>0`.  This is the desired
dimension-uniform active-fiber floor.  The proof is simply that after
classicalization the left side pays every violated diagonal atom, whose total
rank is at least `delta dim(F)` by `(ZSA4)`.

For the Kun--Thom coset action, the permutation/sofic obstruction is the
candidate for `(ZSA4)`, but `(ZSA5)` is exactly
`invariant-cartan-completion`.  Property `(T)` of the actor does not supply it:
`simple-lamp-gauge-rigidity-reduces-to-actor-classicalization` leaves arbitrary
unitary multiplicity cocycles, and
`kun-thom-compression-survives-amenable-near-model` gives faithful exact actor
blocks in which the compression Reynolds sector has asymptotic charge zero.
Kun--Thom's permutation rigidity becomes extensive only after the lamp/site
diagonal is recovered with positive charge.

Therefore the minimal live branching successor is not “a strongly aperiodic
SFT plus property `(T)`.”  It is a finitely presented lamp/address system
proving both the robust finite-action loss `(ZSA4)` and the unitary-to-diagonal
classicalization `(ZSA5)`.  Establishing those for the Kun--Thom action would
give `(ZSA6)` and the sought nonhyperlinear obstruction; neither follows from
generic tiling aperiodicity or actor expansion alone.

DERIVATION
z2-aperiodic-seam-microstate-proof
