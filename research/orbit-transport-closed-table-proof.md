---
rg: 2
id: orbit-transport-closed-table-proof
kind: route
title: Transport the regular action on disjoint blocks, then read off the closure requirement
target: orbit-transport-gauge-needs-a-closed-label-set
requires:
  - spherical-relation-defect-pairs-small-chord
  - trace-separation-sphere-distance-concentration
  - partial-schreier-completion-preserves-sofic-loss
---

**Well-definedness and bijectivity of `(OTC2)`.**  By section 1(3) the map
`a |-> sigma_a(b)` is injective on `A` for `1-o(1)` of the base points, so each
packed index has a unique expression `sigma_a(b)` with `b in B`; disjointness
of the blocks makes `b` unique too.  Since `a |-> sa` is a bijection of `A`
under the closure hypothesis, `tau_s` permutes each block, hence permutes the
packed region.  Extend by any bijection of the complement.

**Exactness of tested relations.**  Direct substitution, displayed in
section 1(1).  Nothing about `sigma` is used: the identity holds because the
block is a copy of the left regular action of the label set on itself.  This
is what removes the coupled-copy synchronization requirement that
`hypergraph-near-perfect-schreier-packing` still carries.

**The radius `(OTC3)`.**  Apply `spherical-relation-defect-pairs-small-chord`
at the root `b` to the tested triple `(s,a,sa)`: the two discrete outputs
`sigma_s sigma_a(b)` and `sigma_(sa)(b)` satisfy
`||x_(sigma_s sigma_a(b))-x_(sigma_(sa)(b))||<=3 rho+zeta`.  From
`||U_s x_i-x_(sigma_s(i))||<=rho`, substituting `i=sigma_s^(-1)(m)` gives
`||x_(sigma_s^(-1)(m))-U_s^(-1)x_m||<=rho` for every `m` in the range, so
`sigma_s^(-1)` distorts distances by at most `2 rho`.  Applying it to the two
indices above, and using `sigma_s^(-1)(sigma_s sigma_a(b))=sigma_a(b)=j` and
`sigma_s^(-1)(sigma_(sa)(b))=c_s(j)`, yields `5 rho+zeta`.

**Block size.**  `trace-separation-sphere-distance-concentration` gives a fixed
gap `kappa` with `||U_a x-U_(a')x||>=kappa` for `a!=a'` on `1-o(1)` of the
cloud.  For `rho<kappa/2` the shadowed images are distinct indices, so
`|O_b|=|A|` off the charged set.

**Fractional matching.**  Each vertex `v` lies in `O_i` exactly for the `|A|`
indices `i=sigma_a^(-1)(v)`, `a in A`, distinct by the same separation.  So `H`
is `|A|`-regular and `|A|`-uniform and the uniform weight `1/|A|` covers every
vertex with total weight one.

**The closure requirement and its Folner form.**  `(OTC2)` refers to
`sigma_(sa)`, which exists only when `sa` is a tested label.  Restricting the
domain to `{sigma_a(b):a in A cap s^(-1)A}` makes `tau_s` a partial bijection
onto `{sigma_a(b):a in sA cap A}`, and the relation identity survives on
`{a: a, ha, gha in A}`; `partial-schreier-completion-preserves-sofic-loss`
completes such near-total partial bijections with linear Hamming loss, so
`(OTC4)` is exactly what the construction needs.

Finally, if for every finite `S subset Gamma` and every `eps>0` there is a
finite `A` with `|A cap s^(-1)A|>=(1-eps)|A|` for all `s in S`, then `A` is an
`(S,eps)`-Folner set; running this over a generating set and exhausting
`Gamma` is the Folner criterion, so `Gamma` is amenable.  Amenable groups are
sofic, so on that class the conclusion is already available and the
construction adds nothing.
