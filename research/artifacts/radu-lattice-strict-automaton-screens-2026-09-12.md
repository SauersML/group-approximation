# Radu's BMW lattice as a host for a strict automaton: screens

Lane `w3-lattice`, 2026-09-12. Handwritten proofs, nothing run. Supports
`radu-bmw-lattice-nonsurjunctive`, `radu-bmw-lattice-has-no-invariant-output-injective-automata`,
`strict-composites-have-strict-factors`, and the Attempts of
`strict-automaton-on-lattice-in-product-of-trees`.

Conventions follow `canonical-table-groups-for-automaton-designs-2026-09-12.md`:
`tau(x)(g) = mu((x(g m))_(m in M))`, and `G` acts on `A^G` by `(g.x)(g') = x(g^(-1) g')`.
An automaton is **surjunctive** when injectivity implies surjectivity, and **strict** when it
is injective and not surjective.

## 0. The host

`radu-bmw-lattice-embeds-in-titz-witzel-kernel` imports from Titz Mite--Witzel
(arXiv:2509.05054v2, Example 3.3 and Proposition 3.4, read from the PDF in
`titz-witzel-radu-sublattice-2026-09-11.md`):

    Gamma_R = <a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>.

* `Gamma_R` is the BMW group of Radu's complex `S_R`. It acts simply transitively on the
  vertices of `X = T_h x T_v`, a product of two 3-regular trees, and the six letters are the
  edge inversions at the base vertex `o`, so the 1-skeleton of `X` is the Cayley graph.
* The action is free on vertices, so faithful. Vertex stabilizers are trivial, so the image in
  `Aut(T_3) x Aut(T_3)` is discrete, and one vertex orbit makes it cocompact. So `Gamma_R` is a
  cocompact lattice in a product of two trees.
* It is irreducible and not residually finite, and `(xz)^4` lies in its finite residual.
* `pi_1(S_R)` has index four in `Gamma_R` and embeds in `K = Gamma_1^2`, the smallest
  Titz--Witzel kernel, which is finitely presented, infinite, simple and Kazhdan.

**Letters and normal forms.** The horizontal letters are `a,b,c` and the vertical letters are
`x,y,z`. The square relations `h v = v' h'` form the complete table (RS3) of the Titz--Witzel
artifact:

    (h,v) -> (v',h'):  (a,x)->(x,a)  (a,y)->(y,a)  (a,z)->(z,b)
                       (b,x)->(x,b)  (b,y)->(y,c)  (b,z)->(z,a)
                       (c,x)->(z,c)  (c,y)->(y,b)  (c,z)->(x,c)

Each row is a relator or a rotation of one. `azbz` gives `az = zb` and `bz = za`, `bycy` gives
`by = yc` and `cy = yb`, and `cxcz` gives `cx = zc` and `cz = xc`. All letters are involutions,
so inverting a row gives `v h = h' v'`. Every element has a unique normal form
(reduced word in `a,b,c`)(reduced word in `x,y,z`), and a unique one in the opposite order.
`A = <a,b,c>` is the stabilizer of the root of `T_v` and `V = <x,y,z>` that of `T_h`. Each acts
simply transitively on the vertices of a 3-regular tree with every letter inverting an edge, so
both are `C_2 * C_2 * C_2`.

**Why this host.** The lattice target is existential. `Gamma_R` is one explicit instance, with
its table quoted from the source.
* `Gamma_R` is surjunctive iff `pi_1(S_R)` is (`surjunctivity-is-a-commensurability-invariant`),
  so the torsion of `Gamma_R` costs nothing.
* A strict automaton over `Gamma_R` is the lattice target
  (`radu-bmw-nonsurjunctivity-gives-lattice-target`). It makes `Gamma_R` nonsofic
  (`radu-bmw-nonsurjunctivity-gives-nonsoficity`), hence `K` nonsofic
  (`titz-witzel-kernel-nonsofic-from-radu-lattice`).
* It also makes `K` nonsurjunctive: `pi_1(S_R)` is nonsurjunctive by commensurability, and
  nonsurjunctivity ascends from `pi_1(S_R)` to `K` (`surjunctivity-passes-to-subgroups`). So one
  counterexample would also refute `fg-simple-kazhdan-groups-are-surjunctive`.

## 1. No output symmetry on Gamma_R

**Theorem 1.** Let `A` be finite with `|A| >= 2`, `H <= Gamma_R`, and `tau` an injective
automaton on `A^(Gamma_R)` with `tau(x)(g h) = tau(x)(g)` for all `x`, all `g` and all `h in H`.
Then `H = 1`.

*Proof.*
1. `H` is finite, by `invariant-output-injective-ca-need-torsion`.
2. **Finite quotients see the symmetry (any group).** Let `N` be a normal subgroup of finite
   index in a group `G`, and `tau` as above over `G`. The set `Fix_N` of configurations constant
   on the cosets `gN` has `|A|^([G:N])` elements and is `tau`-invariant, because `tau` commutes
   with left translation. `tau` is injective on it, so `|tau(Fix_N)| = |A|^([G:N])`. Each
   `y = tau(x)` with `x in Fix_N` is constant on the cosets `gN` and satisfies `y(gh) = y(g)`, so
   it is constant on the cosets of the subgroup `HN`. Hence `|tau(Fix_N)| <= |A|^([G:HN])`,
   which forces `HN = N`, that is `H <= N`. This is the finite-quotient shadow of
   `invariant-output-injective-automata-need-invisible-symmetry`, which places `H` in the sofic
   radical of the memory group.
3. **Involutions of `Gamma_R`.** Let `t` be an involution. `<t>` fixes a point `p` of the
   complete CAT(0) space `X`, so `t` preserves the open cell containing `p` and permutes its
   vertices without fixed vertices.
   * If the cell is an edge, `t` swaps its endpoints. After conjugation it swaps `o` and `l.o`
     for a letter `l`, and the unique element carrying `o` to `l.o` is `l`.
   * If the cell is a square, `t` preserves the product decomposition, so it is not a quarter
     turn. If it swaps adjacent vertices it inverts an edge of the square: first case. Otherwise
     it is a half-turn. Conjugate so that the square has corner `o` and is spanned by `h.o` and
     `v'.o`, with opposite corner `hv.o` for a row `(h,v) -> (v',h')`. Then `t = hv`, and `t^2 = 1`
     gives `hv = vh`, which holds exactly in the rows `(a,x)`, `(a,y)`, `(b,x)`.

   So every involution is conjugate to one of `a, b, c, x, y, z, ax, ay, bx`.
4. **Abelianization.** `azbz`, `bycy` and `cxcz` give `a = b`, `b = c` and `x = z`. The other
   relators become squares or commutators, so `Gamma_R^ab = (Z/2)^3` on the images of `a, x, y`.
   The nine involutions map to `a, a, a, x, y, x, a+x, a+y, a+x`, all nonzero. So no involution
   lies in `N = [Gamma_R, Gamma_R]`, a normal subgroup of index eight.
5. A nontrivial finite `H` contains an involution, while step 2 puts `H` inside `N`. So
   `H = 1`. QED

*Alternative for step 3–4.* `Gamma_R` is the extension of `pi_1(S_R)` by `D_2`, so `pi_1(S_R)` is
normal of index four. It acts freely on the CAT(0) cover `X`, so it is torsion-free, and step 2
with `N = pi_1(S_R)` gives the same conclusion. The proof above uses only the presentation and
the simply transitive action.

**What it kills.** The invariant-output family has no instance on `Gamma_R`, even though
`Gamma_R` has 2-torsion. That covers swap and Klein corner automata, the architecture of
`leavitt-units-carry-injective-invariant-output-automaton`, and designs of any degree over any
alphabet whose output is constant on cosets of a subgroup. On torsion-free lattices, including
one-vertex complete VH lattices and `pi_1(S_R)`, the torsion claim had already excluded it.

**Linear shadow.** For odd `p` and each involution `t`, some character
`chi : Gamma_R -> {+-1}` has `chi(t) = -1`, since `t` maps to a nonzero vector of `(Z/2)^3`.
It sends the averaging idempotent `(1+t)/2` of `F_p[Gamma_R]` to `0`, so that idempotent is full
at no matrix size. Through `low-degree-invariant-output-reduces-to-corner-fullness`, this is
Theorem 1 in the low-degree case.

## 2. Composites and square-reading layers

**Lemma 2.** Let `tau = tau_1 ... tau_k` be automata on one full shift `A^G`. If `tau` is
injective, every tail `tau_j ... tau_k` is injective. If `tau` is strict, some factor `tau_j` is
strict.

*Proof.* `tau` injective forces `tau_k` injective. If `tau_k` is strict we are done. Otherwise
`tau_k` is a bijection. If `tau_1 ... tau_(k-1)` identified `u = tau_k(w)` and `u' = tau_k(w')`,
then `tau(w) = tau(w')`, so `w = w'` and `u = u'`. So `tau_1 ... tau_(k-1)` is injective with the
same image as `tau`. Induct. QED

So composites of surjunctive automata are surjunctive. The linear-and-bijective case is the
induction behind `linear-reversible-words-strict-via-strict-linear-factor`. The alphabet must
stay fixed: gathering windows into larger alphabets presents every automaton as a composite.

**Lemma 3.** If the memory of `tau` lies in a surjunctive subgroup `S`, then `tau` is
surjunctive. Here `tau(x)(g)` depends only on `x` restricted to `gS`, so `tau` acts as the same
automaton over `S` on every factor of `A^G = prod_(gS) A^(gS)`. This is the no-peeling case of
`peeling-to-surjunctive-memory-tail-forces-surjectivity`.

**Surjunctive subgroups of `Gamma_R` used below.**
* `<h, v>` for a horizontal letter `h` and a vertical letter `v`. It is generated by two
  involutions, hence finite dihedral or infinite dihedral, so amenable and surjunctive
  (`amenable-groups-satisfy-the-garden-of-eden-theorem`).
* `A`, `V` and their conjugates. `C_2 * C_2 * C_2` is virtually free: by Kurosh, the kernel of
  `C_2 * C_2 * C_2 -> (Z/2)^3` meets no conjugate of a factor, so it is free. Hence these
  subgroups are sofic (`abelian-by-virtually-free-groups-are-sofic`, with trivial abelian kernel)
  and surjunctive (`sofic-groups-are-surjunctive`).

**Corollary 4.** No composite of automata on `A^(Gamma_R)` whose memories each lie in a
conjugate of `A`, of `V`, or of some `<h, v>` is strict. In particular:
* an automaton reading only the corners `{1, h, v', hv}` of one square is surjunctive;
* the proposed architecture has a surjunctive key automaton, so the design is not strict
  (`shear-designs-are-strict-iff-their-key-automaton-is`). Here a square is forced through a key
  automaton that reads a key track at two addresses joined by a square;
* alternating horizontal and vertical automata are never strict.

So in any factorization of a strict automaton on `Gamma_R` some factor is strict. By Lemma 3
its memory generates a nonsurjunctive, hence nonsofic, subgroup, contained in no conjugate of
`A`, `V` or a dihedral `<h, v>`.

## 3. Letter hinges always transpose

**Lemma 5.** In any group, if `s, m, s', m'` each have order at most two and `s m = s' m'`, then
`m s = m' s'`: invert both sides.

So every identification between two-letter products of `Gamma_R`, and in particular every row
of (RS3), keeps its transposed reverse identification. In the notation of
`transposed-hinges-are-conjugated-commutators`, `[m'^(-1) m, s m] = 1`. This is the torsion
counterpart of Corollary H of `vh-lattice-table-hosts-2026-09-12.md` (reflection-symmetric
squares): on `Gamma_R` every letter square behaves as a symmetric one.
* A strict design with letter addresses on `Gamma_R` needs decisive reverse coincidences that are
  not transposes of forward identifications.
* Transposes among longer products are decided by the normal forms of Section 0. None is
  computed here: by Section 2 the decisive part of the rules is a layer with nonsofic memory, and
  the hinges of that layer are what matter.
