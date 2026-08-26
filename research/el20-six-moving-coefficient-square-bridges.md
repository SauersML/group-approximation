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
