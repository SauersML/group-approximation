# Positive stabilizer rows split into finitely many vertical decoder templates

Date: 2026-08-11

## Outcome

The positive rows in HAP's derived stabilizer total complex cannot acquire a
large integral filling constant from the **vertical** stabilizer
differentials.  For a fixed finite cell stabilizer `H` and an arbitrary
finite `H`-set `X`, every specialized stabilizer resolution splits as a
direct sum over the orbits of `X`.  Each transitive summand is indexed by a
subgroup `L<=H`, and there are only finitely many such subgroup types.

Consequently, in every fixed range of degrees there is one constant

`C(H,r)<infinity`

such that every integral vertical boundary in every finite coefficient
action has an integral vertical filling of normalized Euclidean norm at most
`C(H,r)` times the norm of the boundary.  The statement also holds for the
transposed cochain differentials and for cellular orientation twists.

For the fixed proper `SL_3(Z)` complex, only the groups of orders
`8,12,24` occur.  Thus the unresolved bounded-primary gate is strictly
smaller than “control the positive stabilizer resolutions”: after vertical
reduction, it is the horizontal Wall differential on the local groups

`H_s(L;Z_chi|L)`

and its coupling to the zero-row harmonic lattice.  A growing decoder can
only be assembled by those horizontal incidence maps.

## 1. Orbitwise splitting

Let `H` be finite and let `P_* -> Z` be one fixed free `Z[H]`-resolution,
finitely generated through degree `r`.  Let `chi:H->{+-1}` be fixed.  For a
finite `H`-set `X`, put

`C_s(X)=P_s tensor_(Z[H]) (Z_chi tensor Z[X])`.              `(VSD1)`

Write the orbit decomposition as

`X = disjointUnion_(alpha in A) H/L_alpha`.                  `(VSD2)`

Tensor products commute with direct sums, and every vertical differential
comes from the fixed `Z[H]`-linear differential of `P_*`.  Therefore `(VSD1)`
is an **integral orthogonal direct sum of complexes**

`C_*(X) = directSum_(alpha in A) C_*(H/L_alpha)`.             `(VSD3)`

The standard coordinate bases are disjoint in `(VSD3)`, so squared
Euclidean norms add exactly.  The orientation character changes the signs
inside a block but does not mix two `H`-orbits.

## 2. Uniform integral boundary sections

Choose one representative of every conjugacy class of subgroups `L<=H`.
For each such `L` and every `1<=s<=r`, consider the finite integral matrix

`d_(s,L):C_s(H/L)->C_(s-1)(H/L)`.                             `(VSD4)`

Its image is a free abelian group.  Hence the exact sequence

`0 -> ker d_(s,L) -> C_s(H/L) -> im d_(s,L) -> 0`

splits over `Z`.  Fix an integral linear section `S_(s,L)` and put

`C(H,r)=max_(L,s) ||S_(s,L)||`.                               `(VSD5)`

The maximum is finite because `H` has only finitely many subgroups and only
finitely many degrees are used.

**Theorem 1 (uniform vertical decoder).**  For every finite `H`-set `X`,
every `s<=r`, and every integral `b in im d_s(X)`, there is an integral
`a in C_s(X)` satisfying

`d_s(X)a=b`, and `||a||_2 <= C(H,r)||b||_2`.                  `(VSD6)`

**Proof.**  Decompose `b=directSum b_alpha` by `(VSD3)` and take

`a_alpha=S_(s,L_alpha)b_alpha`.

Then `d a_alpha=b_alpha`.  Orthogonality and `(VSD5)` give

`||a||_2^2=sum_alpha ||a_alpha||_2^2`
` <= C(H,r)^2 sum_alpha ||b_alpha||_2^2`
` = C(H,r)^2||b||_2^2`.

This proves `(VSD6)`.  End proof.

If every copy of `Z[X]` is equipped with normalized counting norm, the
source and target normalizations differ only by the fixed free ranks of
`P_s` and `P_(s-1)`.  Thus `(VSD6)` remains uniform after multiplying
`C(H,r)` by one fixed rank ratio.  Applying the same argument to the
transposed finite matrices proves the cochain version.

## 3. The remaining vertical homology is local

Theorem 1 decodes vertical **boundaries**; it does not erase positive
vertical homology.  Shapiro's lemma identifies the homology of a transitive
block as

`H_s(H;Z_chi tensor Z[H/L]) ~= H_s(L;Z_(chi|L))`.             `(VSD7)`

Combining `(VSD3)` and `(VSD7)` gives

`H_s(C_*(X)) ~= directSum_(alpha in A)`
`                     H_s(L_alpha;Z_(chi|L_alpha))`.          `(VSD8)`

Thus every positive-row coordinate has one of finitely many local subgroup
types.  Since `L` is finite, its positive homology is killed by `|L|`; this
recovers the bounded-exponent statement, but now with an orbitwise metric
splitting before the horizontal differential is applied.

## 4. Application to the HAP total complex

For `ContractibleGcomplex("SL(3,Z)")`, the cell stabilizers through degree
three are fixed groups of orders `8`, `12`, and `24`.  HAP's
`FreeGResolution` uses a fixed free resolution for each.  Apply Theorem 1 to
each cell orbit and take the maximum of the finitely many constants.  Every
`Del_0` vertical boundary in every finite projective specialization then has
a uniformly bounded integral filling.

The filtered `E^1` page is consequently a finite-type local system whose
fibres are exactly the groups in `(VSD8)`.  The remaining maps are induced by
the fixed cellular boundary bisets and the higher Wall corrections.  They
may connect linearly many orbit coordinates, so Theorem 1 alone does not
give a global decoder: a bounded-degree incidence family can still form a
nontrivial code.

The next exact task is therefore well posed:

1. enumerate the subgroup label `L_alpha` on each projective stabilizer
   orbit;
2. compute the induced horizontal maps between the finite groups in
   `(VSD8)`; and
3. prove that those maps split into bounded local templates, as was done for
   the two zero-th-row orientation-primary interfaces.

If step 3 holds, all stabilizer-primary arithmetic is uniformly local and
the only remaining TRUE question in this family is the compact free
harmonic section.  If it fails, the failure is an explicit horizontal code
on finite stabilizer-homology labels, rather than an opaque defect of the
large HAP resolution.
