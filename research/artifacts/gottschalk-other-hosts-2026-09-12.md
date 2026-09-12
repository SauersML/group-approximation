# Gottschalk over nonsofic hosts outside the proven permanence classes

Lane `gk-other-hosts`, 2026-09-12. A census of the nonsofic groups that are
candidate Gottschalk counterexamples, sorted by whether an existing surjunctivity
permanence theorem reaches them, and by how they relate to the one open root
`leavitt-unit-group-nonsurjunctive`.

Supports the Cairn claims `surjunctivity-passes-to-subgroups`,
`leavitt-surjunctivity-tower` and
`fournier-facio-outside-surjunctivity-permanence`.

## 0. The one tool that orders everything

**(P) Surjunctivity is inherited by subgroups.** If `G` is surjunctive and
`H <= G`, then `H` is surjunctive. Proof (Ceccherini-Silberstein--Coornaert,
*Cellular Automata and Groups*, 2010; the (F2) argument): an injective cellular
automaton `tau` over `H` with alphabet `A`, memory `M <= H` and rule
`mu: A^M -> A` defines a cellular automaton `tau^G` over `G` with the *same*
memory and rule. On each left coset `gH`, `tau^G` acts as a copy of `tau`
transported by `h -> gh`, so `tau^G` is injective. `G` surjunctive makes `tau^G`
surjective; reading off one coset, `tau` is surjective. QED

Contrapositive, the form the counterexample search uses:

**(P') Non-surjunctivity is inherited by overgroups.** If `H <= G` and `H` is
not surjunctive, then `G` is not surjunctive.

So along any chain of subgroups, *surjunctivity descends and non-surjunctivity
ascends*. This is what lets a family of hosts be compared instead of attacked
one at a time.

## 1. The Leavitt tower: V ≤ R^× ≤ A^×

Write `R = L_{F_2}(1,2)`, `R^× = L_{F_2}(1,2)^×` (the binary Leavitt unit group,
the group of the open root), and `A^× = L_{F_2}(1,d)^×` for `d >= 2` (a d-ary
Leavitt unit group over `F_2`).

**Bottom: Thompson's `V` embeds in `R^×`.** By
`leavitt-cylinder-swaps-generate-thompson-in-el`, `V <= EL_D(R) =~ EL_9(R)` for
the complete nine-leaf code `D`; by `leavitt-gl-equals-el-and-perfect-unit-group`,
`GL_n(R) = EL_n(R)` for every `n >= 2` and all these groups are the one group
`R^×` (the three-leaf code identifies `R^× = GL_3 = EL_3`, and prefix-code
self-similarity carries every rank to every other). So `V <= R^×`.

**Top: `R^×` embeds in `A^×`.** By `d-ary-leavitt-groups-nonsofic-over-finite-fields`
and its route, the corner of `L_{F_2}(1,d)` at `e = p_0 + ... + p_{d-2}` carries a
unital *binary* Leavitt family; over `F_2` the subalgebra it generates is a copy
of `L_{F_2}(1,2)` (a Leavitt algebra `L(1,2)` is simple, so the family generates
exactly it), and the corner-extension homomorphism `cornerUnitsExtend` is
injective. So `R^× <= A^×`.

Hence the tower of group embeddings

    V  <=  R^×  <=  A^×.

By (P) and (P'):

- **Surjunctive descends:** `A^×` surjunctive `=>` `R^×` surjunctive `=>` `V`
  surjunctive.
- **Non-surjunctive ascends:** `V` not surjunctive `=>` `R^×` not surjunctive
  `=>` `A^×` not surjunctive.

The open question sits at `R^×` (`leavitt-unit-group-nonsurjunctive`). The tower
decides none of the three, but it orders both searches:

- *Counterexample search.* A non-surjunctive automaton on `V` is the **strongest**
  target: it refutes Gottschalk and, ascending, also refutes it on `R^×` and
  `A^×`. A non-surjunctive automaton on `A^×` is the **weakest** target: `A^×` is
  the largest group, so it has the most room for an injective non-surjective map,
  and finding one still refutes Gottschalk -- but it does **not** by itself settle
  `R^×`, because non-surjunctivity ascends, not descends. So the d-ary groups are
  a legitimately *easier* counterexample host than the binary one, not a
  redundant one.
- *Positive search.* Proving `A^×` surjunctive would settle `R^×` and `V` at
  once; proving `V` surjunctive is the humblest first step and is implied by the
  binary conjecture.

Two corollaries worth stating:

- The finitely presented simple nonsofic group of
  `fp-simple-nonsofic-via-leavitt-unit-group` **is** `R^×`. It is not a separate
  host; its surjunctivity is exactly the open root.
- A non-surjunctive `V` would be nonsofic by Gromov--Weiss, settling
  `thompson-v-not-sofic` as a free corollary. (Nonsoficity of `V` is otherwise
  open and does not follow from `V <= R^×`, since soficity, unlike
  surjunctivity, is inherited downward: `R^×` nonsofic says nothing about its
  subgroup `V`.)

Every d-ary Leavitt unit, `GL` and `EL` group over `F_2` contains the binary
core `R^×`, so all of them sit above `R^×` in this order and inherit the same
statements.

## 2. The Fournier--Facio torsion-free group is a genuinely separate host

`G = <Gamma, t_1, t_2>` with `Gamma` an infinite property-(T) subgroup,
`t_1 Gamma t_1^{-1} <= Gamma` a proper (compressing) self-embedding, and a
simple group `S` inside the compression defect
(`fournier-facio-torsion-free-skeleton`). It is finitely presented, torsion-free,
property (T), and nonsofic (`fournier-facio-group-is-nonsofic`).

None of the surjunctivity permanence theorems on main reaches it:

- **`finitary-split-extension-surjunctivity-permanence`** needs `W = N ⋊ Q` with
  a *residually finite* finitary kernel over a *surjunctive* base. `G`'s
  nonsoficity is intrinsic to the compression of the Kazhdan `Gamma`; there is no
  presentation of `G` as a split extension of a surjunctive base by a residually
  finite kernel with detection, finite support and stabilizer invariance. The
  compressed Kazhdan `Gamma` is precisely not such a base.
- **`graph-folds-over-surjunctive-groups-are-surjunctive`** needs a graph of
  groups mapping faithfully on vertex groups to a surjunctive host, with any HNN
  self-embedding realized by conjugation *inside that host*. `G` is an
  ascending-HNN-flavored `<Gamma, t_i>`, but the required host would have to be
  surjunctive and already contain the proper compression of the Kazhdan `Gamma`
  -- essentially `G` itself. The theorem does not apply.
- **`lef-lamp-graph-wreaths-are-surjunctive`** needs a graph-product lamp kernel
  with a permutation actor. `G` has no such description.

Moreover `R^×` is not known to embed in `G` nor `G` in `R^×`, so `G` is not part
of the Leavitt tower. It is an **independent** open nonsofic host: a Gottschalk
counterexample on `G` would be a mechanism distinct from the Leavitt one.

What does *not* help: `G` contains a simple wreath shift
(`fournier-facio-group-contains-simple-wreath-shift`) and other subgroups, but
by (P) a surjunctive subgroup carries no information about the whole group;
subgroup structure constrains counterexamples (P'), not surjunctivity proofs.
And the fixed-tester `gottschalk-surjunctivity-fixed-two-generator-tester` shows
one FP group already tests the universal conjecture, so `G` is not *needed* for
the universal question -- but its own surjunctivity is a separate open problem,
and it is the one nonsofic host here that is neither Leavitt-derived nor inside a
proven permanence class.

## 3. Amalgams and extensions: what is already covered

- **Amalgams `A *_C B`.** `graph-folds-over-surjunctive-groups-are-surjunctive`
  already makes `A *_C B` surjunctive whenever `A, B` embed in one common
  surjunctive group `G` with `C <= A ∩ B`, and an HNN extension surjunctive when
  its associated-subgroup isomorphism is conjugation in a surjunctive host. The
  Kun--Thom doubles `G *_Gamma G` are the case `A = B`
  (`doubles-of-surjunctive-groups-are-surjunctive`).
- **The only nonsofic amalgams identified here are the Kun--Thom doubles**, which
  are covered. A nonsofic amalgam outside the graph-fold class would need vertex
  or edge data not embeddable in a common surjunctive group; no such example is
  recorded in this graph. (Nonsoficity of amalgams over amenable edge groups is
  excluded by the sofic amalgam permanence theorems; the interesting edge groups
  are non-amenable, exactly the Kazhdan `Gamma` of the doubles.) This is a
  scoping note, not a new theorem: it says the amalgam direction adds no
  independent open host beyond the doubles.
- **Non-split extensions** with residually-finite-p kernels in matching
  characteristic are handled at the ring level by
  `residually-p-kernels-preserve-modular-stable-finiteness` (stable finiteness,
  hence the linear route to surjunctivity); non-split extensions without that
  structure remain open and are the FF case above.

## 4. Host census

| host | permanence class reaches it? | relation to the binary root | status |
|---|---|---|---|
| Kun--Thom wreaths `(Z/2) wr_{G/Γ} G` | yes (rf-lamp / LEF-graph-wreath) | -- | **surjunctive** (established) |
| Kun--Thom doubles `G *_Γ G` | yes (graph-fold / finitary-split) | -- | **surjunctive** (established) |
| KT graph wreaths, LEF lamps | yes (LEF-graph-wreath) | -- | **surjunctive** (established) |
| Thompson's `V` | no | `V <= R^×` | open; surjunctive if `R^×` is |
| binary Leavitt unit `R^×` (= FP simple nonsofic) | no | the root itself | **open** (`leavitt-unit-group-nonsurjunctive`) |
| d-ary Leavitt `A^×`, `GL`, `EL` over `F_2` | no | `R^× <= A^×` | open; easier counterexample target; non-surjunctive if `R^×` is |
| Fournier--Facio torsion-free `G` | no | independent (no known embedding either way) | **open**, distinct mechanism |
| general amalgam `A *_C B` | yes when `A,B <= ` common surjunctive `G` | -- | covered; no independent nonsofic case found |

The upshot for the counterexample search: after the permanence theorems, the
genuinely independent open nonsofic hosts are the **Leavitt tower**
`V <= R^× <= A^×` (all coupled to the one binary question, with `A^×` the
roomiest target) and the **Fournier--Facio group** (a separate mechanism). No
other nonsofic host in the graph escapes both the permanence theorems and these
two families.
