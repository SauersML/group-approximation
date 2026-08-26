---
rg: 2
id: binary-leavitt-three-row-atomic-compiler
kind: claim
title: Compile three bounded prototype rows into one returned binary Leavitt atom
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that authenticates a coarse M2 packet, a fine M4 packet and a support row; this may bypass both packet exactifications and must output only the two inverse rows and completeness row on the prescribed root atom.
  leavitt-steinberg-bounded-area-carmichael-lift: that seeks uniformly bounded fillings for an unbounded Thompson Carmichael family; this permits a coordinate-dependent address of arbitrary length but insists that the three semantic discrepancies be literal conjugates of finitely many prototypes.
artifacts:
  - research/binary-leavitt-atomic-return-via-three-row-compiler.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.** In the finite presentation of
`St_20(L_(F_2)(1,2))`, find finitely many fixed prototype discrepancy words
`q_1,...,q_N`, a constant `C`, and a finite-matrix selection rule with the
following property.  Each `q_j` must lie in the normal closure of the fixed
defining relators and must be supplied with one fixed expression as a product
of conjugates of those relators and their inverses.  In particular, every
prototype has a fixed relator-area bound independent of matrix dimension,
selected address and coefficient window.

Whenever the rounded nontrivial spectral atom `p_U` of `z=x_13(s_1t_1)` is
nonzero, the rule may inspect the matrix coordinate and select an arbitrary
Leavitt address and finite coefficient window.  It must then produce four
operators in `p_U M_d(C)p_U` for which each of

```text
t_0s_0-p_U,
t_1s_1-p_U,
s_0t_0+s_1t_1-p_U
```

has operator norm at most

```text
C max_j ||q_j(U)-1||_op.                               (BAC1)
```

Every check at the selected address must be a literal unitary conjugate of a
prototype, so its defect is independent of address length.  This formulation
allows the depth and window to depend on the actual matrix dimension without
asking for a full multiplication table or a coherent inverse-limit module.

The phrase "finite presentation" need not assume a separate finite-
presentation theorem for the literal Steinberg group.  By
`finite-saturated-table-cover-removes-literal-group-presentation`, the
finitely many prototypes, every finite coefficient identity used by the
compiler, and finite normal-generation certificates for `z` define a
finitely presented cover surjecting onto the literal group.  It is enough to
prove `(BAC1)` for that cover: collapse of its normally generating lift of
`z` descends through the surjection.  This finite-cover formulation is the
input intended here.

## Attempts

The obvious depth-one prefix word does not work: its exact typed rectangular
model swaps equal minimal corners while leaving the two packet identities
unidentified.  Adding fixed typed Steinberg triangles, PI tests, Reynolds
ranks, or finite semisimple packet multiplicities still admits the same
escape.  The nearest operator-norm tools are
`conjugacy-addressed-opnorm-challenges-are-lossless` and
`opnorm-coordinatewise-capacity-diagonal`; neither currently constructs the
cross-typed additive completeness row.  A concrete next probe is to close
off-diagonal loops through the depth-one chart and test whether finitely many
loop discrepancies control the operator sum of the returned range
projections on `p_U`.

Nodewise recursion of the two inner Morita branches does not provide the
missing capacity by itself.
`local-morita-sibling-cells-have-a-two-qubit-periodic-absorber` assigns the
two tensor-factor Pauli groups alternately by address parity.  Every parent
has two conjugate commuting marked children and every local sibling cell is
exact at every depth, but cousins reuse the same two factors and the ambient
dimension remains four.  Thus a viable off-diagonal loop must use the
coefficient range-sum/parent-generation occurrence to detect cousin reuse;
another locally conjugated sibling Pauli check cannot control the
completeness row in `(BAC1)`.

There is a sharper language boundary for the prototype list.  By
`finite-positive-root-fragments-have-marked-regular-models`, every finite
collection of positive-root addition, multiplication, shared-occurrence and
range-sum-fold rows has an exact finite regular model with the mark
surviving.  By `partial-whitehead-cell-has-marked-finite-model`, adjoining
one complete non-scalar prefix Whitehead cell still has an exact marked
finite model.  Therefore the finitely many prototypes in `(BAC1)` cannot all
belong to either class.  At least one prototype must simultaneously couple
both binary branches through a mixed/opposite-root occurrence and attach that
occurrence to the packet payload on the prescribed `p_U` corner.  Merely
adding the scalar range-sum fold to one Whitehead actuator is below the known
finite-model firewall.

The exact finite-dimensional collapse of the full signed occurrence system
shows that such a two-branch fragment exists algebraically, but its proof
intersects coordinate-dependent additive root kernels.  Turning that
intersection into `(BAC1)` without a depth-dependent word-area loss is now
the precise operator-norm task: the selected kernel coefficient may depend
on the matrix coordinate, while every return check must still be a literal
conjugate of one of finitely many fixed prototype discrepancies.

The later authenticated support-return loops do not evade this boundary.
`support-return-odd-loops-do-not-imply-atomic-return` places both exact odd
factorizations `J_i=W_i(Z_iH_iZ_i)W_i`, their transported Pauli covariances,
their chart intersection and the native braid in a finite exact model with
the marked atom nonzero.  The atomic Leavitt gap then rules out any deduction
of `(BAC1)` from that menu alone.  A viable prototype must add an occurrence
which couples the coefficient completeness fold to the prescribed atom;
another formal recombination of the returned native words is insufficient.

The first literal mixed-loop completion of the private-column geometry is
also below this boundary.  In
`tagged-whitehead-two-branch-loop-has-a-three-qubit-marked-model`, adjacent
Whiteheads transport the tagged marked commutator from one branch to the
other and close a genuine null loop.  Three Pauli factors and tensor swaps
realize that loop, every crossed-zero row, and the Whitehead braid exactly
with the mark equal to `-1`.  Thus the required prototype cannot merely
return the same payload commutator through both branch charts.  It must make
the coefficient range-sum/parent-generation occurrence act on the selected
atom, thereby ruling out Pauli-factor reuse.

The smallest output-authenticated implementation of that requirement has
now also been tested.  In
`payload-range-sum-whitehead-has-three-character-model`,
each inverse payload commutator is transported by its own literal Whitehead
to the corresponding `s_it_i` range sign, and the two range signs multiply
to the parent sign.  This excludes the scalar-mark three-qubit reuse model,
but a twelve-dimensional three-character orbit satisfies the whole table
with the parent mark surviving.  Each Whitehead moves half of its negative
range through the complementary parent-sign sector.  Thus the next fixed
prototype must authenticate an individual coefficient arm on the prescribed
parent atom, not only the inverse and reverse **output commutators** and
their exact range sum.

Authenticating only one such arm is still insufficient.
`one-arm-range-sum-whitehead-has-marked-model` fixes one full Pauli arm
through each Whitehead, so the same named coefficient occurrence participates
in both the inverse and reverse product rows and is non-scalar on the
prescribed parent atom.  A twelve-dimensional exact model makes those fixed
arms global while placing all three-character support motion in the
complementary controlled arms.  Thus a viable prototype must authenticate
both sides of at least one transported product, or use a mixed cross-arm row
which forces the complementary range support back into the parent atom.

Depth does not repair this one-arm failure.  The construction
`full-prefix-range-cells-have-three-state-model` conjugates the fixed cell
through the `S_3` action on the three nonzero two-bit characters and realizes
the full binary prefix tree at every depth on one twelve-dimensional space.
Every node has exact inverse rows, exact parent range-sum, exact one-arm
Whitehead authentication, and the attached mixed reverse-range crossed-zero
row `e_0e_1=0`.  Address words collide in the six-element actor, but the
collisions are harmless because each child retains an equal-rank wing outside
the current parent atom.  Hence choosing depth beyond `log d` after seeing a
matrix coordinate cannot by itself produce `(BAC1)`.  The prototype menu
must contain a cross-address holonomy or cousin-arm occurrence which detects
reuse of those complementary wings.

The smallest such occurrence is now explicit.
`first-cousin-cross-arm-breaks-three-state-reuse` adds one equal-depth
prefix cross-zero row `[X_alpha,Z_beta]=1` between two cousin cells that the
three-state actor identifies.  It rejects the twelve-dimensional periodic
model because the reused pair has commutator `J`, not one.  A fresh Pauli
factor repairs any finite collection of these rows, however; the complete
depth-`n` table has exact marked models of growing dimension.  Conversely,
the whole growing cross table would give the required operator-norm packing
capacity, but its canonical discrepancies have unbounded equal-level
relator area and therefore cannot be literal conjugates of finitely many
fixed prototypes.  The surviving design target is a fixed nonlinear
holonomy compressing many cousin collisions without recreating that area
divergence.

The first nonlinear compression attempts are also fenced.
`bounded-cousin-checksums-have-finite-clifford-models` evaluates the balanced
four-commutator checksum and finds it parity-blind: it is one both for the
correct two-cousin table and after identifying the cousins.  A bounded
relative-address holonomy can permute only finitely many named arms and is
implemented by a finite monomial/Clifford factor.  Any bounded connected
pairwise mark-seam complex has the same finite-range obstruction.  An odd
checksum detects reuse only by retaining an asymmetric cousin cross row,
returning to the finite-fresh-factor/unbounded-area dichotomy above.  The
remaining prototype must therefore be a non-pairwise coefficient relation
whose value is neither central mark parity nor a finite affine-symplectic
permutation of the cousin factors.  A fixed higher-arity product of
conjugate marks is not enough either:
`fixed-arity-mark-fusion-has-finite-character-model` realizes every such
fusion in a finite character actor, even with one controlled Pauli payload
per chart.  The boundary must read noncommuting row/column payloads in an
address-sensitive way.

Nor can finite group-algebra polynomial recombination of these packet words
bypass that occurrence boundary.  By
`fixed-group-algebra-polynomials-cannot-supply-atomic-return`, arbitrary
compressed Fourier/Pauli polynomials in either the exact three-qubit model
or the exact twelve-dimensional three-character model have total AMR defect
at least one on the nonzero marked atom.  The same bound holds in the left
regular marked corner for any fixed polynomials in actual Steinberg words.
Thus a successful compiler must make a genuinely coordinate-dependent
finite-matrix choice or prove the uniform prototype gap; it cannot extract
the three rows by a fixed analytic polynomial inside the recovered packet.

The coefficient boundary is now sharper than the earlier Boolean-window
fence.  `degree-zero-leavitt-core-has-locally-finite-marked-models` identifies
the whole balanced-prefix core as a nested union of finite matrix rings over
`F_2`.  Consequently every fixed ordinary-word inventory whose coefficients
are finite sums of equal-length prefix matrix units has one exact finite
marked model, even when it contains `s_0t_1,s_1t_0`, arbitrary opposite-root
Whiteheads, and mixed commutators.  A live prototype must therefore carry
nonzero Leavitt gauge degree through the marked occurrence (for example an
uncancelled `s_i` or `t_i`), or use genuinely unbounded adaptive depth.
Replacing the Boolean range projections by more balanced prefix coefficients
cannot prove `(BAC1)`.

The first literal noncommuting depth-two payload loop is not enough.
`depth-two-cousin-loop-has-finite-ut5-fusion-model` uses the shared-arm
identity `t_(00)(s_(00)t_(11))s_(11)=A` as a four-arm nested Steinberg
commutator, transports the complete loop through both Whitehead address
moves, and attaches its three outputs to the parent range-sum fold.  Three
copies of `UT_5(F_2)`, modulo the product of their central long roots and
with `S_3` permuting the copies, realize the whole table exactly with the
mark surviving.  Thus conjugating complete noncommuting payload packets and
fusing only their central outputs still admits a finite nilpotent escape.
The next word must mix arms from **different** addressed payload copies in
one noncommuting occurrence; a whole-packet address permutation is not
enough.

Literal sharing across those copies has now been tested as well.
`shared-cousin-arm-loop-has-finite-matrix-fusion` puts the source and two
cousin ranges in `M_3(F_2)`, uses the actual matrix units as the common
`t_u,s_u,t_v,s_v` occurrences in every inverse, crossed-zero, Whitehead, and
mixed four-arm row, and imposes the range fold in the top root of
`UT_5(M_3(F_2))`.  Quotienting that central root by the scalar identity makes
`q_u+q_v=1-p` equal to `p` in characteristic two while the rank-one mark
`p` survives.  Thus cross-copy noncommutation plus literal arm sharing is
still insufficient if the object-erasing equality appears only in a central
output root.  The surviving candidate must propagate the fold into a second
composable root by multiplying the identified output with another shared
coefficient arm.

That first propagation is now fenced too.  In
`two-step-fold-loop-has-finite-64-model`, the three fold coefficients
`C_0,C_1,J=C_0C_1` are all sent through the same literal nested word
`[T,[-,S]]`, where the shared arm occurrences `S,T` are commuting
involutions.  The active child and parent both return the same nontrivial
mark and the crossed child returns one, exactly as the coefficient rows
`t_us_ut_us_u=A`, `t_u(s_vt_v)s_u=0`, and `t_uAs_u=A` require.  Nevertheless
the whole cell has an exact model of order `64`: on
`F_2[e,h]/(e^2,h^2)`, the two arms act by multiplication by `1+e,1+h`, so
the nested word is the nonzero mixed second difference `eh`.  Thus forcing
the fold out of the central scalar quotient is necessary but not sufficient.
The next prototype must authenticate an intermediate propagated root (or an
individual arm action there), rather than checking only equality of the
three returned long-root words.

The smallest such authentication still has a finite escape.
`intermediate-fold-arm-has-finite-s6-model` names the propagated root
`E=[C_0,S]=[J,S]`, imposes `[C_1,S]=1`, uses the same `S` and `T` in every
row, and adjoins an involution `W` satisfying `WSW^(-1)=E`.  This does rule
out the preceding square-zero semidirect product because its actor and
additive-kernel elements cannot be conjugate.  But an exact permutation
model in `S_6` survives: overlapping double transpositions realize all
three fold rows, the intermediate transport, the distant-arm commutation,
and the nontrivial final return simultaneously.  Therefore an abstract
transport of the intermediate arm is not yet its full native
authentication.  The remaining bounded target must attach `W` to the
actual Whitehead factorization (including its other already-shared root
occurrences), or authenticate the final `T` action by an equally literal
native occurrence row.

That literal factorization has now also been tested.
`partial-whitehead-fold-return-has-finite-s6-model` adjoins
`W=UVU`, transports `U` to the reused `S` arm and `V` to the reused final
`T` arm, and keeps every preceding fold/intermediate/return row.  The same
six-point permutation packet extends exactly: take `U=S`, `V=(3 5)` and
two involutory conjugators for the root-position identifications.  Thus even
both factor arms in one partial-Whitehead word do not force a common matrix
reservoir.  The next test must constrain the two root-position transports
by their full native mixed-square menu rather than allowing independent
conjugacies.

Doing both at once is still insufficient.
`whitehead-fold-return-has-affine-model` returns to the full four-bit model
and defines each partial Whitehead by the literal word
`W_i=S_iT_iS_i`, using exactly the same affine transvections `S_i,T_i` as
the two-branch fold-compose-return table.  The braid
`S_iT_iS_i=T_iS_iT_i`, both Whitehead involution and root-swap rows, and the
adjacent braid `W_0W_1W_0=W_1W_0W_1` all hold.  More strongly, `W_i` swaps
the parent mark label `A` with the actual intermediate label `R_i`, and the
same `T_i` then satisfies `[T_i,R_i]=A` and the crossed-zero row.  Hence both
intermediate roots and both final outputs are natively authenticated with
no duplicate arm actor.  The finite affine group, together with its
equivariant `GL_5(F_2)` payload/opposite packet, nevertheless retains the
nontrivial mark exactly.  The surviving boundary is no longer occurrence
sharing or Whitehead factorization: a new row must force these affine
actors to be coefficient multiplication on one common payload matrix
corner, rather than merely automorphisms of a finite label packet.

The first literal arm-inside-opposite-root attempt does leave the affine
actor category, but it still does not close.
`native-opposite-arm-return-has-finite-s6-model` uses actual indices and the
chain `x_15(q_i),x_56(s_0),x_16(s_0),x_01(t_0),x_06(A)`.  It inserts the
opposite root `x_61(t_0)` and the genuine partial Whitehead
`P=x_16(s_0)x_61(t_0)x_16(s_0)`, including its braid, involution, and root
swap.  Fixed spare-index Weyl words identify both repeated arm coefficients
and the returned `A` coefficient with their other named root occurrences.
Nevertheless explicit permutations in `S_6` satisfy the fold, matching and
crossed rows, every opposite-root row, and every occurrence transport while
the final mark remains nontrivial.  Thus authenticating one binary branch
all the way through one native opposite-root packet is insufficient.  The
remaining candidate must put both branches into one opposite-root relation
which reads their coefficients on the same payload corner; another
single-branch occurrence transport can be absorbed by overlapping finite
Klein-four/`S_3` packets.

The most obvious two-branch opposite-root word is not such a reader.
`aggregate-binary-whitehead-does-not-read-completeness` places
`x_16(s_0),x_17(s_1)` in one row, `x_61(t_0),x_71(t_1)` in one column, and
forms the aggregate partial Whitehead `RLR`.  Because the crossed products
vanish and the two matching root pairs commute across branches, its braid
`RLR=LRL` factors exactly as the product of the two ordinary branch braids.
The derivation never uses `s_0t_0+s_1t_1=A`.  An exact
`S_3 times S_3 times C_2 times C_2` model keeps the aggregate word and an
independent nontrivial fold mark.  Therefore visually placing both arms in
one three-by-three block is not enough.  The unresolved word must put the
shared **reverse products** `s_it_i` themselves into a noncommuting
opposite-root coefficient occurrence before their completeness sum is
collapsed to a root label.

That exact target now has a smallest explicit word, but it too has a finite
fence.  In `reverse-product-whitehead-fold-has-finite-fusion`, each shared
reverse-product output `x_14(q_i)` and the opposite root carrying the same
coefficient `x_41(q_i)` form the partial Whitehead `W_i`; the parent
coefficient `A` forms `W_A` in the same root pair.  Orthogonality and
`q_0+q_1=A` give the genuinely nonlinear relation `W_0W_1=W_A`.  This time
completeness is essential in the coefficient derivation, and both
`s_it_i` coefficients occur inside noncommuting words before the comparison.
Nevertheless three finite `GL_4(F_2)` packets with supports
`(1,1,0),(1,0,1),(0,1,1)` satisfy the complete shared-path table and the new
relation because the scalar Whitehead is an involution.  The mark survives.
Thus the remaining seam is not merely to use completeness nonlinearly; it
must prevent this three-packet support fusion by forcing the opposite-root
coefficient occurrences for both children and the parent onto one
indivisible payload reservoir.

One literal mixed cross-zero square now eliminates that entire scalar
support-fusion firewall.  In
`cross-zero-breaks-reverse-whitehead-support-fusion`, fixed Weyl words move
the same `C_0=x_14(q_0),C_1=x_14(q_1)` occurrences, together with their
opposite factors `D_i`, to `x_12(q_0),x_23(q_1)` and the corresponding
opposite roots.  The Leavitt crossed product gives a trivial commutator.
Any scalar packet coordinate active for both children would instead contain
`[x_12(1),x_23(1)]=x_13(1)`, so the two child supports must be disjoint.
But completeness makes the parent support their symmetric difference, and
the native partial-Whitehead transports make both child supports equimeasurable
with the parent.  Their common weight is therefore both `r` and `2r`, hence
zero.  This rules out arbitrary finite scalar support fusions, not only the
three-copy model.  The remaining gap is promotion from scalar support
coordinates to arbitrary non-scalar finite packet holonomy: one must show
that the mixed squares force intersection-zero on the exactified payload
reservoir without first assuming a character decomposition.

That promotion is false under the current rows.
`mixed-cross-zero-squares-have-four-state-gauge-model` takes rank-two source
supports `P_0=<e_1,e_2>`, `P_1=<e_2,e_3>` and parent symmetric difference
`P_A=<e_1,e_3>`.  They are equirank and the source intersection has rank
one.  Separate native reservoir gauges transport the two children to the
complementary target supports `<e_1,e_2>` and `<e_3,e_4>`.  Controlling the
complete positive/opposite finite packet by these projections makes every
fold, Whitehead, opposite-factor mixed square, and composable cross-zero row
exact, while the parent mark survives.  In particular the target cross-Gram
is zero but the source intersection has operator norm one, so neither
operator-norm perturbation, rank integrality, nor coordinate-dependent
spectral cuts can prove the desired promotion.  The remaining prototype
must contain a relative reservoir-gauge lock coupling `U_0^*U_1` to the
source packet; two separately authenticated branch transports leave exactly
the four-state freedom above.

The actual relative root-position word and its complete finite orbit still
do not provide that lock.  In
`relative-a2-weyl-orbit-has-seven-state-gauge-model`, choose `U_0` sending
the common source root to `x_12` and write `U_1=HU_0`, where the adjacent
Weyl product `H` cycles `x_12,x_23,x_31` and has order three.  Thus
`U_0^(-1)U_1` is a conjugate native `A_2` Coxeter word.  Imposing its full
braid/order action and both oriented cross-zero rows rules out the
four-state swap, but a seven-state carrier survives: the branch-one source
support overlaps branch zero, while an order-three reservoir permutation
moves it through two fresh supports, both disjoint from branch zero, before
returning.  Every complete positive/opposite occurrence square is exact and
the parent mark survives.  The remaining fixed relation must compare a
returned orbit reservoir directly with the source intersection; finite
Coxeter covariance alone merely bounds the number of fresh gauges rather
than identifying them.

The direct returned-source comparison exists as an ordinary word, but it
still has a finite non-scalar escape.
`returned-opposite-cross-zero-has-finite-s6-model` adds
`[x_41(q_0),x_14(q_1)]=1` and its symmetric companion after the relative
orbit returns.  These genuine Leavitt consequences compare the original
opposite/positive source occurrences.  They kill the canonical seven-state
payload, but `S_6` realizes the two child Whiteheads on disjoint Coxeter
triples: the cross-child opposite factors commute, the two child outputs
multiply to the parent Whitehead, and the diagonal parent mark survives.
Three cyclic copies add the full native `A_2` orbit and exact return.  Thus
the missing lock must identify the cross-child opposite factors with the
canonical noncommuting factors on one irreducible payload block; returned
zero-product words alone allow finite Coxeter re-gauging.

There is also a coefficient-wide fence beyond the returned Boolean window.
`degree-zero-leavitt-core-has-locally-finite-marked-models` identifies all
balanced prefix coefficients `s_u t_v`, `|u|=|v|=n`, with the matrix units
of `M_(2^n)(F_2)`.  The nested union over `n` is locally finite.  Hence any
fixed ordinary-word menu confined to gauge degree zero -- including the
non-Boolean cross coefficients `s_0t_1,s_1t_0`, arbitrary opposite-root
Whiteheads and arbitrary mixed commutators -- has a simultaneous finite
exact elementary-group model with the mark surviving.  A live bounded
prototype must therefore contain a coefficient of nonzero gauge degree,
not merely a non-diagonal balanced prefix unit.  Literal `s_i,t_i` and
unequal-length prefixes remain outside this fence; the native-arm models
above show that their presence is necessary but not sufficient.

The first literal nonzero-degree mixed completeness cell is also now
fenced.  `aggregate-morita-row-column-fold-has-d8-square-model` puts
`s_0,s_1` in one positive-root row and `t_0,t_1` in one composable column.
Their aggregate commutator forms `s_0t_0+s_1t_1=1` internally, while one
matching subcommutator is the marked `q_1` root occurrence.  The exact table
still factorizes in `D_8 times D_8`, with the two child commutators as
independent central directions and their product as the parent output.
Thus even literal use of all four gauge-nonzero arms in one completeness
word is insufficient.  The next occurrence must couple an opposite-root or
returned payload to those two child directions on the prescribed mark
carrier; another positive-root aggregate fold remains below the finite-model
firewall.
