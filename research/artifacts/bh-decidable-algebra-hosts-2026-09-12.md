# The algebra route to Boone--Higman: verification and where the wall is

Lane `bh-decidable-algebra-hosts`, 2026-09-12. Scope: the route
`boone-higman-via-central-simple-leavitt-tensor-host` and its premise
`decidable-group-algebras-have-fp-central-simple-hosts`.

## 1. The route is sound as stated

Let `G` be finitely generated with solvable word problem, `B` the premise host,
`L = L_(F_2)(1,2)`, and `R = B ⊗ L`.

- `G <= F_2[G]^x -> B^x -> R^x`. The first map is the inclusion of group
  elements, the second is the unital embedding, and `b |-> b ⊗ 1` is injective
  because tensoring over a field is faithful.
- `R^x` is finitely presented by `leavitt-tensor-hosts-acyclic-steinberg-and-fp`
  (3). This needs `B` simple and finitely presented and `K_1(R) = K_2(R) = 0`,
  all of which the premise supplies.
- `R^x` is simple by `central-simple-leavitt-tensor-unit-groups-are-simple`
  (2). This needs `B` central simple and the same `K`-theory.
- `R ≅ M_3(R)` because `L ≅ L^3` as right modules, so `R^x ≅ GL_3(R)`. That is
  the identification the simplicity claim uses.

No hidden hypothesis was found. The route is a correct reduction.

## 2. Separating the three obstacles in the premise

The premise asks for (A) a finitely presented central simple `B` containing
`F_2[G]`, and (C) `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`. Centrality (B) is part of (A).

### 2.1 `K_1` is never needed

New claim `perfect-unit-subgroups-embed-in-elementary-groups`: over ANY unital
ring, a perfect subgroup of `R^x` embeds in `E_n(R)` for all `n >= 2`.
- Whitehead's lemma: `diag(u, u^-1) = w(u) w(-1) in E_2(R)`, with
  `w(u) = e_12(u) e_21(-u^-1) e_12(u)`, checked without commutativity.
- Consequently `diag([u,v], 1) in E_2(R)`.

New claim `leavitt-tensor-elementary-host-criterion`: for `B` finitely
presented and central simple, a perfect `S <= B^x` and `n >= 4`, `E_n(B ⊗ L)`
is a finitely presented simple group containing `S` as soon as
`ker(St_n(B ⊗ L) -> E_n(B ⊗ L))` is finitely normally generated.
- Simplicity: `central-simple-leavitt-tensor-unit-groups-are-simple` part 1,
  which uses no `K`-theory.
- Finite presentation: Krstić--McCool for `St_n` (item 6 of
  `khanh-acyclicity-and-steinberg-criteria`) and
  `fp-quotient-iff-kernel-finitely-normally-generated`.

Boone--Higman needs only infinite simple inputs
(`boone-higman-iff-infinite-simple-inputs`), and those are perfect. So the
unit group, and with it `K_1`, drops out.

### 2.2 The weakest premise on this route

New open claim `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`: every
infinite finitely generated computably presented simple `S` embeds in `B^x`
for a finitely presented central simple `B` whose unstable Steinberg kernel
`ker(St_n(B ⊗ L) -> E_n(B ⊗ L))` is finitely normally generated for some
`n >= 4`.
- Route `infinite-simple-input-bh-via-elementary-leavitt-hosts`: this premise
  implies `infinite-simple-input-boone-higman`, hence Boone--Higman.
- Route `elementary-leavitt-hosts-from-central-simple-hosts`: the old premise
  implies this one. With `K_1 = K_2 = 0` the kernel is trivial by
  `leavitt-tensor-hosts-acyclic-steinberg-and-fp` (2).

So the new premise is at most as hard as the old one, and it asks less.
- It asks for a group embedding into units, not an algebra embedding of the
  group algebra.
- It needs no `K_1` condition.
- It needs finite normal generation of one unstable kernel, not vanishing.

### 2.3 Which obstacle is the wall

- **(C′), the kernel condition.** It follows from `K_1 = K_2 = 0`, which in turn
  follows from regular supercoherence of `B` (Ara--Cortiñas Proposition 6.2). It
  is a homological regularity requirement on the host, not a new existence
  problem.
- **(A), the host.** A finitely presented SIMPLE algebra containing `S` in its
  units. That is the algebra form of Boone--Higman.
  - Evans--Mandelberg--Neff (1975) prove only the weak half for algebras: a
    simple algebra inside a finitely presented algebra.
  - Belyaev (1976--78) proves a Higman embedding for associative algebras, with
    no simplicity.
  - The swarm's literature lane found no published theorem giving finitely
    presented simple envelopes for decidable algebras
    (`boone-higman-frontier-2026-09-12.md` §4). This is a bounded check.
- **The group problem reappears inside the algebra problem.** The natural
  construction takes a maximal ideal `M` of a finitely presented algebra
  containing `S`. It needs `M` finitely generated as an ideal, which is the
  ring counterpart of the finite normal generation wall for groups.
- **Complexity.** A fixed family of hosts has one word-problem bound, and
  `complexity-bounded-host-classes-are-not-universal` forbids that.

**Conclusion.** The wall on this route is (A): finitely presented simple
algebra envelopes. (C′) is a regularity side condition, automatic for regular
supercoherent hosts. `K_1` and centrality beyond part 1 of the simplicity
theorem play no role.

## 3. Trust surfaces

- Everything through the Leavitt tensor claims inherits Khanh arXiv:2609.08428v1
  (unrefereed), as recorded by `reviewer-2`.
- The Whitehead-lemma claim and the criterion are elementary derivations from
  established nodes. They are not reviewed and not in Lean.
- Evans--Mandelberg--Neff and Belyaev were not read from the primary sources
  here. Their roles above come from the survey arXiv:2306.16356v3 §3 as reported
  by `bh-lit-map`.
