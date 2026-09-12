# Phase unfolding: exact local rounding and the amenability barrier

This note tests one possible way around the circle-cocycle stability gate in
`notes/POPA_FACTOR_MODEL_LIFTING.md`.  The conclusion is exact but negative:
complete-simplex rounding does produce a finite-phase cocycle before one
identifies overlapping local charts, but making the unfolded chart into an
asymptotic action requires a Følner sequence.  For a nonamenable quotient,
the missing operation is precisely descent through those overlaps, which is
the original cocycle-stability problem.

## 1. Monomial data and exact transition phases

Let `F` be a finite subset of a group `Q`, containing `1`, and suppose a
finite-dimensional monomial table is written

`M_q e_v = a_q(v) e_(sigma_q v)`

for `q in F`, `v in V`, with `a_q(v) in T`.  For the moment no
multiplicativity is assumed.  For each `v`, define a transition phase on the
complete directed graph on `F` by

`tau_v(q,r)=a_r(v) overline(a_q(v))`.                 `(PU1)`

This is an exact complete-simplex cocycle:

`tau_v(q,r) tau_v(r,t)=tau_v(q,t)`.                  `(PU2)`

Thus no stability theorem is needed at this level.  The vertex phases
`a_q(v)` are already potentials for the label simplex.

Assume now that `g,q,gq in F` and that the monomial table is approximately
multiplicative.  On coordinates where

`sigma_g sigma_q(v)=sigma_(gq)(v)`,                  `(PU3)`

the normalized Hilbert--Schmidt defect of
`M_g M_q-M_(gq)` is the average squared chordal defect of

`a_g(sigma_q v)a_q(v)` from `a_(gq)(v)`.             `(PU4)`

Equivalently, `(PU1)` gives

`tau_v(q,gq) approximately a_g(sigma_q v)`.          `(PU5)`

The transition cocycle therefore reproduces the original phase table on
every tested local orbit chart.

## 2. Torsion rounding is exact on the unfolded chart

Choose one finite circle group `mu_M` and round all finitely many potentials
`a_q(v)` to elements `b_q(v) in mu_M`.  Define

`tau'_v(q,r)=b_r(v) overline(b_q(v))`.                `(PU6)`

The rounding can be uniformly as fine as desired, and `(PU2)` remains an
exact identity for `tau'`.

Put `Y=V times F`.  For `gq in F`, define the partial map and its phase by

`T_g(v,q)=(v,gq)`,

`phi_g(v,q)=tau'_v(q,gq)=b_(gq)(v) overline(b_q(v))`. `(PU7)`

Where all labels involved remain in `F`, these data form an exact
finite-phase monomial action:

`T_g T_h(v,q)=T_(gh)(v,q)`,

`phi_g(T_h(v,q)) phi_h(v,q)=phi_(gh)(v,q)`.           `(PU8)`

The phase equality telescopes.  By `(PU5)` and sufficiently fine rounding,
`phi_g(v,q)` approximates `a_g(sigma_q v)` in normalized `L^2` on every
fixed tested table.

This explains why complete-simplex cocycle stability does not settle the
global problem: before overlaps are identified, the relevant cocycle is
already exact.

## 3. Completing the partial translations costs the Følner boundary

For `g in Q`, set

`D_g(F)={q in F : gq in F}`,

`beta_g(F)=1-|D_g(F)|/|F|=|gF triangle F|/(2|F|)`.   `(PU9)`

Left multiplication is a bijection from `D_g(F)` to `D_(g^-1)(F)`.  It can
therefore be completed arbitrarily to a permutation `L_g` of `F`, agreeing
with `q |-> gq` on `D_g(F)`.  On every `q` for which `hq` and `ghq` both
belong to `F`, all three completed maps use their prescribed values, so

`L_g L_h(q)=L_(gh)(q)`.                              `(PU10)`

Consequently,

`d_Ham(L_g L_h,L_(gh)) <= beta_h(F)+beta_(gh)(F)`.   `(PU11)`

The same good set is where the phase identity `(PU8)` holds.  Acting
regularly on an additional `mu_M` coordinate therefore converts `(PU7)`
into genuine permutations with multiplication defect bounded by the same
boundary terms, plus the original monomial-table and torsion-rounding
errors.

For an exhaustion `F_n`, the boundary terms in `(PU11)` tend to zero for
every fixed `g,h` exactly when `(F_n)` is a left Følner sequence.  Hence this
unfold-and-complete construction works for amenable `Q` and cannot by itself
extend to a nonamenable quotient.

## 4. Why identifying the copies is the live gate

The local chart map is

`J:V times F -> V`, `J(v,q)=sigma_q(v)`.             `(PU12)`

On its good set, `J(T_g(v,q))=sigma_g(J(v,q))`.
Avoiding the Følner boundary would require identifying the many pairs with
the same endpoint under `J`.  For the rounded phase to descend, the ratio

`b_(gq)(v) overline(b_q(v))`                          `(PU13)`

must, outside a negligible set, depend only on `g` and the endpoint
`sigma_q(v)`, not on the chosen presentation `(v,q)` of that endpoint.
Approximate monomial multiplication gives only approximate agreement of
these overlap values.  Repairing them to exact agreement is precisely the
distance-to-the-exact-cocycle assertion `(PFL11)`, equivalently the
qualitative stability gate `(CS1)` in `notes/NOTEPAD.md`.

Thus the two available completions are sharply separated:

1. keep the local copies distinct, in which case torsion rounding is exact
   but the error is a Følner boundary;
2. identify the copies using the sofic chart, in which case the boundary
   disappears but exact overlap descent requires cocycle stability.

There is no third conclusion hidden in the complete-complex theorem.

## 5. Literature calibration

Chapman--Lubotzky, *Stability of Homomorphisms, Coverings and Cocycles I:
Equivalence* ([arXiv:2310.17474](https://arxiv.org/abs/2310.17474)), proves
the equivalence of homomorphism, covering, and cocycle stability and notes
that the complete complex has a linear stability rate.  Part II
([arXiv:2311.06706](https://arxiv.org/abs/2311.06706)) develops examples and
open problems.  Those results concern repairing overlap consistency; they
do not remove the boundary in `(PU11)`.  The calculation above explains why
applying complete-complex stability only inside each local orbit chart
recovers the amenable/Følner mechanism rather than a general rounding
theorem.
