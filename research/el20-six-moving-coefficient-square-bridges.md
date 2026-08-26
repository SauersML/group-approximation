---
rg: 2
id: el20-six-moving-coefficient-square-bridges
kind: claim
title: EL20 supplies six ungauged coefficient bridges between the order-seven moving cuts
distinct_from:
  six-ungauged-moving-squares-lock-seven-gauges: that proves the abstract quantitative gauge lock after bridges are authenticated; this asks for the actual EL20 words and full-Gram estimates.
  primitive-native-hecke-relators-have-no-odd-mixed-occurrence: that audits the primitive fixed relators between the original native and Hecke rows; this permits derived conjugate words acting between moving stages.
  middle-index-order-seven-orbit-cut-is-native-scale-neutral: that closes the fixed Fano actor packet; this requires bridges which retain the signed unequal-scale source rather than its scale-neutral constant atom.
---

**OPEN SIX-BRIDGE COEFFICIENT INTERFACE.**  In the setting of
`growing-multicut-el20-order-seven-inheritance`, construct for each row
`i=1,2` and `0<=k<=6` an ordinary EL20 coefficient word whose compression

```text
R_(i,k):E_(i,k)H -> E_(i,k+1)H                       (ESB1)
```

has source and range Gram equal to the corresponding moving cuts up to
`o_2(1)`, is typed in the adjacent packet charts as

```text
N_(i,k) tensor 1+o_2(1),                              (ESB2)
```

and participates in the mixed square

```text
C_(i,k+1)R_(i,k)=R_(i,k+1)C_(i,k)+o_2(1),            (ESB3)
```

with the exact label covariance `(SGL4)` for `0<=k<=5`.  All bridge and
square errors must be charged to one fixed finite ordinary-relator menu, with
dimension-independent constants.  A single base bridge is sufficient if
its six conjugates are authenticated with the same estimates.

The bridge must be coefficient-sensitive and ungauged on the multiplicity
factor.  Actor covariance alone only produces the order-seven holonomy of
`fano-moving-packet-retains-actor-holonomy`; independent stage typing leaves
the coboundary drift of
`moving-order-seven-stage-gauges-have-coboundary-drift`.

## Attempts

- The head `T_i` itself gives a full-Gram parallel transition, but carries
  the very reservoir gauge being measured, so its square is tautological.
  `order-seven-moving-cuts-realize-both-affine-profiles` makes this failure
  exact while also realizing the two required affine rank profiles: the
  head-powered squares, seventh powers, and moving boundaries all have zero
  defect, yet the initial row gauges have positive fractions `1/2` and
  `5/6`.  Thus neither polar cutting nor operator-norm exactification can
  turn a gauged head bridge into `(ESB2)`.
- The sharper factorization is now explicit in
  `literal-whiteheads-give-gauged-moving-bridge-table`: each `v_i` normalizes
  the signed Hecke source, so `J_i` alone and its six Singer conjugates have
  exact full Grams and exact mixed squares.  But `J_i` is the literal native
  Whitehead occurrence defining the stage discrepancy, so those bridges
  type as `N_(i,k) tensor D_(i,k)`, not as ungauged coefficient bridges.
- The seven-pair Fano packet gives ungauged root operators on its full label
  factor.  No established calculation shows that any such root has full
  source Gram from the signed Hecke character cut to its next Singer
  translate.  The only invariant Fano atom currently known is orthogonal to
  that signed source and collapses both native scales to `1/1`.
- A bridge built only from the finite actor group is insufficient: tensoring
  the actor table with its regular representation inserts a nontrivial
  order-seven reservoir holonomy while preserving every such covariance.
- Enlarging that search to the whole finite Fano semidirect packet still
  fails by `fano-semidir-bridges-are-wrong-subgroup-or-gauged`.  Pure
  coefficient words are ungauged but preserve the actor-subgroup Fourier
  support `L_0`, while the Singer stage uses `t_iL_0t_i^(-1)`.  Any word
  which moves this support has nontrivial actor quotient and reacquires the
  regular-amplification gauge.
- Refining each moving cut by a Singer-normalized incoming-root Lagrangian
  does not turn that subgroup mismatch into a character mismatch.  By
  `incoming-lagrangian-refinement-preserves-hecke-actor-support`, an affine
  stabilizer refinement still has actor support `t_i^kL_0t_i^(-k)`.  A
  dual Pauli translation preserves this subgroup support and changes at
  most its character/cocycle, whereas the next stage has the genuinely
  different subgroup `t_i^(k+1)L_0t_i^(-(k+1))`.
- The canonical full-Leavitt escape also has the wrong support, for a
  different exact reason.  By
  `leavitt-compression-preserves-root-position-support`, the compression
  endomorphism `x_ab(r) |-> x_ab(s_0rt_0)` and its explicit 20-by-20
  Whitehead implementation preserve every ordered root position.  The
  Singer step sends the actual `(2,8)` root of `L_0` to `(2,7)`, so the
  compression cell sends `Q` to the Reynolds cut over `alpha(L_0)` rather
  than to `t_iQt_i^(-1)`.  Its Singer conjugates therefore fail `(ESB1)`
  before the mixed-square estimate is reached.
- Dressing the literal Whitehead by any collection of already ungauged
  source/range normalizers cannot repair `(ESB2)`.  By
  `label-only-dressing-cannot-ungauge-a-whitehead-bridge`, a composite with
  exactly one gauged Whitehead occurrence is still typed `N tensor D`, and
  its distance from the required `N tensor 1` is exactly `||D-1||_2` up to
  the accumulated chart errors.  A successful composite therefore needs a
  second genuinely gauged mixed/opposite-root occurrence whose reservoir
  action cancels `D` while its total label action still moves the signed
  Hecke source exactly once; pure normalizer dressing is not enough.
- Adding that second gauge-bearing occurrence inside a larger **finite
  normal extraspecial packet** also fails.  By
  `finite-extraspecial-mixed-words-cannot-ungauge-singer-transport`, all
  outer reservoir factors multiply to the projective operator indexed by
  the total quotient element.  Moving `L_0` to `t_iL_0t_i^(-1)` forces that
  quotient element to be nontrivial, while universal cancellation of the
  reservoir factor forces it to be trivial.  This covers any finite number
  of mixed normalizer letters, not merely one Whitehead plus label-only
  dressing.
- The first genuinely nonnormal full-Leavitt candidate is also now exact
  and fenced.  Rootwise compression sends
  `W_87(s_0,t_0)` to `J_1` and the depth-one analogue to `J_2`, so the
  Hilbert-hotel conjugate has the correct full Gram.  By
  `compression-preimage-whitehead-preserves-gauge`, however, the two
  compression letters only change the source and range charts: the
  preimage gauge is conjugated to the literal Whitehead gauge.  Exact
  finite amplifications retain any nontrivial involution on both sides.
  Iterating the preimage only pushes that gauge to greater prefix depth.
- Closing both compression-preimage branches through the literal range-sum
  fold still does not remove the gauge.  By
  `closed-compression-fold-loop-retains-s3-gauge`, the complete bounded
  occurrence table has an exact three-character model: the two branch edges
  are the transpositions `(0 2),(0 1)`, while the fold signs are diagonal.
  The alternating hexagon closes the reservoir only by returning the marked
  character object; appending one required signed-Hecke move restores a
  nontrivial transposition.  Hence the first genuine **closed**, non-chain
  full-Leavitt loop is also fenced.
- Adding the smallest actual opposite-root relation beyond that closed
  character table still does not collapse it.  The involutive Leavitt unit
  `u=s_0t_1+s_1t_0` and Weyl word `w_ab(u)` swap both complete branch arms.
  By `binary-branch-flip-weyl-has-s3-c2-model`, the three-character escape
  extends exactly: the character transposition is accompanied by a swap of
  the two Pauli reservoirs, enlarging the finite actor from `S_3` to
  `S_3 x C_2`.  Thus literal symmetric branch exchange is not the missing
  asymmetric payload return.
- Closing the **entire depth-one actor menu** does not change that verdict.
  `full-depth-one-leavitt-menu-has-finite-clifford-model` includes both
  compression preimages, all inverse/cross-zero/fold rows, the branch flip,
  every fixed root-position Weyl conjugacy used by ESB, their Singer role
  translates, and every mixed naturality square.  They act through one
  finite role-permutation/two-qubit-Clifford group whose regular model keeps
  the marked involution nontrivial.  The next possible breaker must be an
  address-sensitive asymmetric return beyond affine depth-one Pauli labels.
- Nor can one append a single genuinely nonnormal opposite-root letter to
  the known Whitehead.  By
  `one-nonnormal-dressing-cannot-preserve-moving-full-gram`, all exact
  transports from `Q` to `J_iQJ_i^(-1)` form the torsor
  `J_i Norm(Q)`.  A relative factor outside the source normalizer changes
  the range Gram.  Explicitly, `x_82(1)` conjugates the source root
  `x_28(1)` to the `(2,8)` swap, which is not in `L_0`.
- Pairing two exits in that same critical opposite-root channel gives no
  extra freedom.  By
  `paired-critical-opposite-roots-return-only-trivially`, root additivity
  reduces `x_82(b)x_82(a)` to `x_82(a+b)`, and the exact `(2,8)` block
  calculation shows that a return to the constant Hecke normalizer forces
  `a+b=0`.  The returned normalizer is therefore the identity and cannot
  cancel the Whitehead reservoir gauge.
- The equally literal pair obtained by reversing two distinct displayed
  arrows of `L_0` also cannot return.  By
  `two-distinct-reverse-hecke-roots-cannot-return`, the directed Hecke roots
  determine an intrinsic four-step fixed-space filtration.  Each bare
  reverse root raises that filtration, and two distinct such letters cannot
  cancel the first raised coordinate.  This is only a fence on the bare
  reverse-arrow menu, not on general two-channel coefficient words.
- Different root channels do contain genuine returns, so the preceding
  same-channel fence must not be overgeneralized.  The exhaustive calculation
  `signed-hecke-normalizer-has-eight-external-root-returns` finds exactly
  eight constant root transvections outside `L_0` which preserve the signed
  Hecke pair.  Each is the literal inverse-pair commutator
  `[x(t_0),x(s_0)]=x(1)` in suitable root positions.  These words supply the
  first concrete nontrivial two-exit candidates, but on the Hecke character
  carrier each retains a free multiplicity involution.  The next calculation
  must tie one of those eight involutions to the Whitehead gauge by a mixed
  relation; merely observing that the output returns to the normalizer does
  not make it ungauged.
- Even the coordinate-matched return `x_78(1)` is not authenticated by its
  first Singer square.  By
  `one-singer-square-does-not-identify-external-return-gauge`, that square
  carries its multiplicity involution `E` to `DED^(-1)` on the target
  carrier, where `D` is the Whitehead gauge.  A two-qubit exact model has
  `D=Z tensor 1`, `E=1 tensor Z`, so coordinate overlap and one transport
  leave `||E-D||_2=sqrt(2)`.
- Expanding the root-position conjugator into its actual native word does
  create the first unequal-odd-parity closed cell, but still not
  cancellation.  By `native-weyl-return-gauges-have-s3-model`, with
  `n=x_78(1)`, `m=x_87(1)` and `w=nmn`, the factorization and native square
  give reservoir equations `D=EFE`, `F=DED^(-1)`.  Their exact solution by
  the three distinct reflections of `S_3` keeps `DE` a nontrivial
  three-cycle.  All other fixed Weyl mixed squares extend by literal
  conjugation.  Thus parity is finally odd in the required sense, but a
  second relation must rule out this order-three gauge product.

The smallest remaining algebraic search is therefore explicit: find one
genuinely nonnormal coefficient/root-opposite word with the full-Gram property
`(ESB1)--(ESB2)` and verify its six Singer conjugate squares.  It must contain
at least two occurrences in different root channels, or a longer asymmetric
return with an intervening coefficient word, which exit and then return to the
Hecke atom normalizer.  The returned nonidentity normalizer must cancel the
Whitehead gauge; normalizer letters inside a larger finite packet and a
same-channel opposite-root pair are both insufficient.  No Property `(T)`,
canonical trace profile, or tracial-von-Neumann extension is allowed.

For the eight external returns, the gate is now sharper: exhibit a mixed
closed full-EL20 word on one Hecke carrier in which `E_(s,t)` and the
literal Whitehead gauge occur with unequal odd parity.  A normalization
identity or a single Singer conjugacy square cannot supply that equality.

The native Weyl expansion supplies such an odd-parity word but reveals the
next obstruction: odd parity identifies only the `C_2` abelianization of
the gauges.  The surviving search must additionally force the resulting
`S_3` reflection pair to commute, or impose an incompatible braid length,
so that the order-three product dies.

The first two-return attempt does not kill that product.
`two-external-return-cell-has-finite-s3-model` adds the commuting return
`r=x_59(1)`, the matrix root for the enumerated arrow `9->5`, and the
literal same-carrier triangle
`[x_45(1),x_59(1)]=x_49(1)`, whose other two roots lie in `L_0`.
The triangle cancels the new gauge on its two commutator appearances and
does not determine it.  Native commutation reads `[E,G]=1`, realized by
`G=E`, while the old Whitehead and external
gauges remain the distinct reflections `D=(1 2),E=(2 3)`.  Singer
conjugates transport `G=E` covariantly.  Thus the next relation must
place `D` itself in a commutation row with `E`, or provide a reverse
same-carrier triangle that kills `E`; a second commuting return appearing
only between scalar `L_0` legs is insufficient.

The complete eight-root/one-Whitehead index search is now closed as well.
`eight-external-returns-have-no-whitehead-gauge-lock` conjugates all eight
external roots by `J_1,t_1,J_2,t_2`.  The only fixed external roots are
`x_59,x_96` in row 1 and `x_27,x_74` in row 2, all disjoint from the active
Whitehead coordinates.  Every overlapping root maps to `L_0`, an opposite
or nonexternal root, or a non-root transvection.  Fixed-root squares give
only stage covariance `G_(k+1)=D_kG_kD_k^(-1)` between different charts;
they do not give `[D_k,G_k]=1`.  Hence no smallest native mixed relation in
this menu kills the surviving order-three `DE`.  A live next word must mix
at least two non-fixed external orbits before returning to the same cut.

The complete constant-root external-return group is now closed as well.
By `external-return-group-has-only-spectator-singer-centralizers`, adjoining
all eight returns to `L_0` gives a group of order `2097152`, but either full
Singer head has only `64` centralizers in that group and every one lies in
the subgroup generated by `L_0` and the two disjoint spectator returns for
that row.  Thus no constant-root product of any length supplies the desired
active same-chart commutation lock.  Nonconstant Leavitt coefficients and
mixed returns weaker than direct Singer centralization remain live.

The first nonconstant modification of the eight inverse-pair commutators is
also closed.  `one-asymmetric-prefix-cannot-be-signed-hecke-return` exposes
the inserted coefficient by conjugating with one literal constant Hecke
root in each external position.  Normalization forces that coefficient to
lie in `F_2`; a nontrivial asymmetric prefix matrix unit therefore fails
`(ESB1)`.  Sandwiching it between any number of constant returns cannot
help, because the signed normalizer is a group.  The first surviving
coefficient-sensitive word must contain at least two nonconstant root
occurrences which both leave the normalizer and only jointly return; one
asymmetric insertion plus a different constant return is impossible.

The complete two-letter depth-one version of that next search is now closed
as well.  `two-depth-one-leavitt-roots-return-only-constantly` tests all
`42` root positions and all eight nonconstant depth-one matrix units for
both factors.  Among the `92416` ordered pairs whose factors individually
leave the signed normalizer, every returning product is a same-root identity
or the constant fold `s_0t_0+s_1t_1=1`; there is no genuinely paired return.
This is broader than the named depth-one actor menu.  A live two-exit word
must therefore use depth-two address data, at least three prefix leaves, or
more than two nonconstant root occurrences.

- **Extend the exact prefix search to three depth-one roots.**  This remains
  computationally open and is not being promoted to a fence.  The `304^2`
  ordered two-factor histories collapse to `54897` exact symbolic group
  elements.  A bounded MSI pass then filtered possible third factors using
  one signed `L_0` generator, but exceeded its hard `250000` survivor cap
  (`253762` survivors) before the first `32` of `304` third factors had been
  processed, and was stopped after `16.5` seconds.  Thus one-row conjugation
  is far too weak.  A viable exact classification needs a simultaneous
  multirow signature quotient or a structural double-coset reduction before
  any further enumeration; no three-letter hit or no-go follows from this
  bounded pass.

The first such jointly returning coefficient packet is now explicit but
still gauged.  `asymmetric-depth-two-fold-return-retains-external-gauge`
uses the complete prefix code `{00,01,1}` and three private commutators to
produce

```text
x_78(e_00)x_78(e_01)x_78(e_1)=x_78(1).
```

It is a literal asymmetric depth-two same-carrier return, but equality with
the old external root means that its reservoir factor is still `E`.
Conjugating the entire expanded word by the Whitehead or Singer head gives
only `E'=DED^(-1)`.  The private arms do not separately reduce the Hecke
cut, so Hall--Witt reassociation or occurrence counting cannot cancel their
intermediate gauges.  The next live word must mix nonconstant root channels
before the final return, rather than fold private prefix leaves additively
inside one root subgroup.

The first genuinely nonseparated A3 version is also exact and stops at the
same gauge.  `depth-two-a3-return-is-gauged-external-root` uses

```text
alpha=t_00, beta=s_00t_01, gamma=s_01,
alpha beta gamma=1, alpha gamma=0,
```

on a composable three-root path.  Both associator bracketings equal
`x_78(1)`, while the private-arm shortcut is cross-zero.  Appending one
Whitehead therefore gives a moving bridge with reservoir factor `DE`, not
the identity; the internal arms do not reduce the Hecke cut and have no
same-carrier gauges to cancel.  The old exact `S_3` assignment keeps `DE`
of order three.  The next cell must attach an opposite-root/Whitehead word
to an individual private A3 arm before the triple product becomes one, and
must close a new same-carrier relation rather than conjugate the total
external output.

That individual-arm refinement is now fenced too.
`depth-two-a3-private-whiteheads-have-finite-gl6-model` attaches the genuine
partial inverse coefficients and opposite-root Whiteheads to each of `A`,
`B`, and `G` before either A3 bracketing forms `x_78(1)`.  One exact
`GL_6(F_2)` occurrence model realizes the two marked bracketings, the
cross-zero shortcut, all three private rank-two Weyl cells, and even the
output Whitehead while the marked long root remains nontrivial.  Thus three
separate individual-arm cells add no reservoir equation beyond
`E'=DED^(-1)`; a successful cell must make an opposite arm interact with a
different A3 channel on the returned Hecke carrier.

Using both complementary branches before collapse still does not kill that
order-three gauge.  `complementary-depth-two-a3-whiteheads-have-a6-gauge-model`
builds two depth-two A3 cells with private coefficients

```text
a_i=s_it_(i0), b_i=s_(i0)t_(i1), c_i=s_(i1)t_i,
a_ib_ic_i=q_i, a_ic_i=0.
```

Their outputs `P_i=x_78(q_i)` enter the opposite-root words
`V_i=P_ix_87(q_i)P_i` before completeness is used, and the literal
full-Leavitt relation is `V_0V_1=w_78(1)`.  On reservoir factors this adds
`G_0G_1=D` to the native equations `D=EFE,F=DED`.  An exact `A_6` model
realizes all three equations and the three-chart branch permutation while
keeping `DE` equal to a product of two 3-cycles.  Thus even complementary
private-arm Whiteheads do not give `(ESB2)`; the next occurrence must put an
individual private arm and `D` or `E` in a new same-chart commutator or
other relation beyond completeness fusion.

The first literal same-chart private-Weyl commutator is now also computed.
Writing `P_i=x_78(q_i)`, `R_i=x_87(q_i)`, and
`V_i=P_iR_iP_i`, orthogonality and completeness give

```text
nV_in=R_i,       mV_im=P_i,       [w,V_i]=1,
n=P_0P_1,        m=R_0R_1,        w=V_0V_1.
```

Thus `complementary-private-weyl-loops-have-s3-square-gauge-model` does put
each individual private Whitehead in a common-carrier commutator with the
native Weyl.  It is still insufficient: the complete table has an exact
`S_3 times S_3` gauge model with the two branches in separate factors and
the native gauges embedded diagonally.  The private commutators hold while
the diagonal `DE` has order three.  The next word must mix the two branch
reservoir factors off this direct-product decomposition, not merely
centralize each private factor by their diagonal product.

Directly crossing the uncompleted depth-two private packets does not provide
that word.  `complementary-private-a3-root-packets-cross-commute` observes
that every private coefficient and genuine reverse in branch `i` has the
form `s_(i mu)t_(i nu)`.  Prefix orthogonality therefore makes both products
between a branch-zero and a branch-one coefficient vanish.  This remains
true at actual shared EL20 indices: for example

```text
[x_(10,7)(s_00t_0),x_(7,12)(s_1t_10)]=1,
[x_78(q_1),x_(8,10)(s_0t_01)]=1.
```

Indeed all individual complementary private-root words commute factor by
factor, including opposite-root occurrences.  The existing `S_3 times S_3`
gauge fence already realizes every such cross commutation while its diagonal
native `DE` retains order three.  Thus a positive cell must first leave the
pure top-prefix components--through a genuinely mixed `0`-to-`1`
coefficient or through completeness before the noncommuting occurrence;
one pure individual arm from each branch cannot produce a new `D/E`
equation.

The cross matrix units provide exactly that first off-diagonal actor, but it
still has a finite wreath gauge.  With `p=s_0t_1`, `r=s_1t_0`, the literal
partial Whiteheads

```text
K_0=x_78(p)x_87(r)x_78(p),
K_1=x_78(r)x_87(p)x_78(r)
```

are commuting involutions whose product is `T=w_78(p+r)`.  The aggregate
same-carrier rows send `P_i` to `R_(1-i)`, `R_i` to `P_(1-i)`, swap
`V_0,V_1`, interchange `n,m`, and fix `w`.  By
`cross-branch-partial-whiteheads-have-finite-wreath-gauge-model`, the full
table is realized in `(S_3 times S_3) semidirect C_2`, with an extra central
`C_2` factoring `T` into the two private involutions, while diagonal `DE`
still has order three.  The next relation must type one individual `K_i`
against a native occurrence on a common Hecke carrier before their product
becomes the aggregate branch flip.

That individual typing test is now exact and negative at the first native
row.  `individual-cross-whiteheads-miss-native-hecke-target` conjugates the
literal Hecke generator `x_28(1)` and obtains

```text
K_0x_28(1)K_0=x_27(r)x_28(q_0),
K_1x_28(1)K_1=x_27(p)x_28(q_1).
```

Thus neither `K_i` preserves the constant signed cut.  Multiplying by the
actual native `J_1` still leaves explicit nonconstant entries, so
`J_1^(-1)K_i` is not in the signed normalizer; because `t_1=J_1v_1` and
`v_1` is in that normalizer, the Singer target fails identically.  The one
literal short native relation that remains is `wK_0w=K_1`.  Its complete
local reservoir table has an exact `S_4` model in which the two individual
gauges are exchanged by `D`, their product is a double transposition, and
`DE` remains order three.  Hence an individual cross-branch Whitehead plus
one native row still supplies no `(ESB1)--(ESB2)` square.  A live word must
first return its nonconstant `K_i` cut to `Q` or to `J_iQJ_i^(-1)` through
another coefficient-sensitive occurrence.

The complete one-occurrence depth-one menu does not supply that return.
`one-depth-one-occurrence-does-not-return-cross-whitehead` tests all `336`
nonconstant depth-one elementary roots and all `2688` depth-one
three-factor opposite-root Whiteheads on the actor coordinates.  Each
candidate is checked on all ten generators and the character of the full
signed group `L_0`, against both `Q` and `J_1QJ_1^(-1)`.  The native target
has no hits.  The source target has only the two braid spellings of `K_i`
itself, and in both cases `LK_i=1`.  Thus the next live word needs either a
depth-two coefficient or at least two additional nonnormal occurrences;
one more depth-one root/Whitehead cell only cancels the original word.

The matching depth-two boundary is now closed as well.
`one-depth-two-monomial-does-not-return-cross-whitehead` tests every one of
the `48` exact prefix monomials `s_mu t_nu` with both prefix lengths at most
two, first as one elementary root and then as the genuine partial Whitehead
with matched reverse `s_nu t_mu`, at all `42` actor positions.  Among
`16128` branch/target tests, the exposed generator `x_28(1)` leaves only
the same two braid spellings of `K_i` for the source target and no survivor
for the `J_1` target.  The full signed signature confirms that both source
survivors have `LK_i=1`.  Thus one genuine depth-two partial inverse still
does not return the cut; the next search must use an asymmetric/unmatched
three-factor word, a coefficient sum, greater depth, or two additional
nonnormal occurrences.

Using two additional depth-one root channels instead of one deeper
occurrence is also fenced.  `two-depth-one-nonnormal-roots-do-not-return-cross-whitehead`
enumerates all `89984` ordered pairs of individually nonnormal depth-one
roots in distinct actor positions, for both branches and both targets.  The
`J_1` target has no `x_28(1)` survivor.  The source target has one survivor
per branch, but its product with `K_i` cancels to the single nonnormal root
`x_78(p)` or `x_78(r)`, which fails the remaining signed signature.  All
`359936` full cases therefore fail.  This leaves unmatched three-factor
words, deeper two-occurrence coefficients, or the first genuine
three-channel factorization; a pair of elementary depth-one exits is not
enough.

The unmatched three-factor boundary has now produced the first exact
individual source returns.  `cross-whitehead-sandwiches-branch-roots-into-signed-normalizer`
tests every arbitrary depth-one word
`x_ab(c)x_ba(d)x_ab(c)` together with one individually nonnormal depth-one
root in a different channel, in both orders, for both branches and both
source/native targets.  Hashing the exposed `x_28(1)` row reduces the
`6381568` syntactic cases to `1128560` exact state transitions and `1700`
full-signature survivors.  The only hits are `24` source spellings: the
three-factor word is one of the two braid spellings of `K_i`, the added
root enters coordinate `8` from `6` or `9`, and

```text
K_0x_(8,k)(g)K_0=x_(7,k)(pg),   g in {s_1,r,q_1},
K_1x_(8,k)(g)K_1=x_(7,k)(rg),   g in {s_0,p,q_0}.
```

These close the complete signed source Gram table, but the returned
nonconstant normalizer root has an uncontrolled reservoir gauge.  No word
returns to the native `J_1` target.  Thus the next relation must type or
cancel this returned normalizer action; the positive full-Gram identity by
itself is not yet the ESB bridge.

Fusing the complementary authenticated returns does use completeness, but
does not cancel that action.  For either `k=6` or `9`, the two identities

```text
K_0x_(8,k)(r)K_0=x_(7,k)(q_0),
K_1x_(8,k)(p)K_1=x_(7,k)(q_1)
```

multiply on their common output root to `x_(7,k)(1)`.  The full table in
`fused-authenticated-cross-returns-retain-s3-square-gauge` has an exact
`S_3 times S_3` model: the two `K_i` gauges are `(c,1),(1,c)`, the incoming
gauges are `(a,1),(1,a)`, and the returned gauges are `(b,1),(1,b)`, with
`cac=b`.  The fused constant output therefore carries `(b,b)`, not the
identity.  Hence even two full-Gram authenticated returns reconstruct an
external constant-normalizer gauge; a native occurrence must still type
that fused output or one branch return individually.

Dyadically refining the two cross coefficients does not supply that return.
In `dyadic-cross-whitehead-fusion-has-finite-product-gauge`, the exact
splittings

```text
p=sum_(j=0,1)s_(0j)t_(1j),
r=sum_(j=0,1)s_(1j)t_(0j)
```

factor each coarse `K_i` into two commuting suffix-private Whiteheads.
Every private factor still sends `x_28(1)` to a matrix with nonconstant
entries, and multiplication by the actual `J_1` leaves the explicit
coefficient `x_1`; hence neither the native Whitehead nor Singer target is
reached before fusion.  Coarse equality and the literal swap of the two
orientations have an exact `S_4 times S_4` gauge model, one factor per
suffix leaf, with diagonal `DE` of order three.  The same construction
iterates at every fixed dyadic depth.  Thus address refinement alone merely
factorizes the old gauge; a live word must interact across distinct suffix
leaves before their completeness sum.

The direct low-depth return equation after a coarse `K_i` is now solved as
well.  `first-cross-whitehead-has-no-alternative-low-depth-return` proves
that appending any one elementary root leaves at least one of the two
nonconstant entries exposed by `K_0x_28(1)K_0`.  Allowing an arbitrary
depth-changing partial inverse pair in a second Whitehead on `(7,8)` still
gives only the tautological return `K_0K_0=1`: the other constant signed
return `x_78(1)` violates the necessary Whitehead block diagonal identity.
The corresponding equations for the native `J_1` coset also fail, since
their forced off-diagonal product is zero while the actual diagonal is
`q_1` or `q_1+r`, rather than one.  Thus no one-root or same-pair
partial-Whitehead object eraser yields a new gauge equation.  The remaining
structural possibility must use at least two additional nonnormal
occurrences in genuinely different root channels.

Two such occurrences are still insufficient if each is an arbitrary
rank-two coefficient word.  The support calculation in
`two-distinct-rank-two-channels-cannot-factor-cross-return` is independent
of coefficient depth: two distinct coordinate pairs whose product is
supported on `(7,8)` must have the form `{k,7}` and `{k,8}`.  Multiplying
the two general invertible blocks in either order leaves the resulting
`(7,8)` block triangular.  But every undressed return `NK_0` and native
target `J_1NK_0`, with the supported signed normalizer
`N in {1,x_78(1)}`, has both off-diagonal entries nonzero.  Hence two
different elementary/partial-Whitehead channels cannot furnish even the
ordinary return word, regardless of full Leavitt coefficient sums.  A live
independent factorization now needs at least three rank-two occurrences or
one genuinely three-coordinate occurrence; dyadic same-pair fusion and
normalizer dressing remain excluded.

The first live three-channel factorization exists, but its complementary
fusion does not have the advertised constant coefficients.
`stabilized-cross-braid-has-s3-square-gauge-fence` verifies the exact
ordinary identities

```text
K_i=P_iQ_iP_i=Q_iP_iQ_i
```

through stable coordinate `9`, together with all complementary cross
commutations.  Only `P_0P_1=w_79(1)` is constant: direct multiplication
gives `Q_0Q_1=w_89(p+r)` and `K_0K_1=w_78(p+r)`, where the branch-flip unit
`p+r` is not one.  The full corrected table has an exact
`S_3 times S_3` reservoir model, with the two complementary braid packets
in separate factors and their fusions diagonal.  The diagonal product of
the first two fused gauges remains order three.  Thus a three-coordinate
braid alone still does not authenticate a shared selector; the next word
must form a genuine coefficient sum before complementary separation or add
a same-carrier relation between the two private factors.

Forming completeness inside one aggregate mixed commutator is also now
explicit, rather than merely proposed.  In
`aggregate-cross-commutator-sum-has-finite-s6-gauge`, the two-arm row and
column words

```text
A=x_79(p)x_(7,10)(r),
B=x_98(r)x_(10,8)(p)
```

satisfy `[A,B]=x_78(pr+rp)=x_78(1)`.  Thus `q_0+q_1=1` is genuinely formed
inside a single four-coordinate commutator before an output-root fusion.
Nevertheless the relation on reservoir factors is only
`E=[alpha,beta]`.  An exact `S_6` model realizes `alpha,beta` as
involutions with that commutator while a native involution `D` still has
`DE` of order three.  Appending this word to `K_0` is precisely normalizer
dressing and supplies no shared occurrence with `J_1`.  The next live cell
must make one of the private row/column roots occur literally inside the
native Whitehead/Singer word, or impose another same-carrier relation
between its factor and `D`.

A still tighter completeness word can share literal factors with `K_0`,
but it too retains a finite spectator.  In
`mixed-completeness-braid-retains-s3-square-gauge`, take

```text
U=x_78(p), V=x_87(r), U'=x_79(1), V'=x_97(q_1),
A=UU', B=VV'.
```

The nilpotent products satisfy `XY=E_77` by
`pr+q_1=q_0+q_1=1`, while
`YX=q_1E_88+rE_89+q_1E_99`; hence `ABA=BAB`.  The word also contains the
actual mixed occurrence `[V,U']=x_89(r)`, and `U,V` are the literal factors
of `K_0=UVU`.  Even this full displayed table admits an exact
`S_3 times S_3` gauge: put `U,V` in the first factor and `U',V'` in the
second.  Then `K_0` has gauge `(c,1)` while the aggregate braid output has
gauge `(c,c)`.  Thus the completeness calculation creates an independent
channel-nine spectator instead of identifying the native gauge.  The next
word must return and type that spectator on an already shared occurrence.
