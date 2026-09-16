# Swarm notes: some type-F group has no contractible Rips complex (2026-09-16)

Target and locked hole: `some-type-f-group-has-no-contractible-rips-complex`,
the negative answer to Zaremsky Problem 4.7 under its literal reading.

## Setup

By `group-rips-complexes-are-cayley-graph-flag-complexes`, the Rips complex
`VR_r(G, d_S)` equals `Flag(Cay(G, B_S(r)))`. So a witness `G` needs this: for
every finite symmetric generating set `T` (take `T = B_S(r)`), the clique
complex of `Cay(G,T)` is not contractible.

The target's Attempts section names two test objects, the integral Heisenberg
group `H_3(Z)` and `BS(1,2)`. Both are groups of type F with distorted infinite
cyclic subgroups. This run attacked them directly. Both turn out to have
contractible Rips complexes, so neither is a witness.

## What was proven

### Theorem 1: Baumslag–Solitar groups

- **Nodes:** claim `baumslag-solitar-groups-have-contractible-rips-complexes`,
  route `...-proof`, and artifact
  `research/artifacts/baumslag-solitar-contractible-rips-2026-09-16.md`.
- **Statement.** Let `G = BS(m,n)` with `m >= 1` and `N = |n|`. Let `P` be any
  monotone lattice path from `(0,0)` to `(m,N)`. Take
  `S = {a^±1} ∪ {(a^(-δi) t a^r)^±1 : (r,i) ∈ P}`.
- **Conclusion.** `Flag(Cay(G,S))` is the staircase triangulation of the
  universal cover of the presentation complex. It is 2-dimensional and
  contractible.
- **Key steps:**
  - Contractibility of the presentation complex, by a direct cellular `H_2`
    argument.
  - The Britton-lemma label identity `s(p) = s(p')` iff `p - p' ∈ Z(m,N)`.
  - The `t`-exponent bookkeeping that forces every 3-clique to be a
    triangle of the subdivision: consecutive points of the periodic path
    `P + Z(m,N)`.
  - `H_2(Y;F_2) = 0`, which excludes duplicate triangles and 4-cliques.
- **Brute-force check.** `experiments/baumslag-solitar-contractible-rips-2026-09-16/`
  checks the link-level predictions for `1 <= m <= 4`, `1 <= |n| <= 4` and
  every path: 484 generating sets. It cross-checks against the affine model
  of `BS(1,n)`.
- **Example.** For `BS(1,2)`, `S = {a^±1, t^±1, (a^-1 t)^±1, (a^-2 t)^±1}`.

### Theorem 2: the Heisenberg group

- **Nodes:** claim `heisenberg-group-has-a-contractible-rips-complex`, route
  `...-proof`, and artifact
  `research/artifacts/heisenberg-contractible-rips-2026-09-16.md`.
- **Statement.** For `H = H_3(Z)` in coordinates
  `(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`, take
  `S = {x, y, z, xz, yz, xy, xyz}^±1`, which has 14 elements.
- **Conclusion.** `Flag(Cay(H,S))` is homeomorphic to `R^3`, via the affine
  extension of the orbit map into `H_3(R)`.
- **Key steps:**
  - Left translations are affine in these coordinates, so the affine
    extension is equivariant.
  - A finite exact certificate at one vertex, (L1)–(L4). The link is a
    14-vertex, 24-triangle 2-sphere, all determinants are `±1`, there are no
    folds, and the degree along a ray is 1.
  - This makes the radial projection of the link a homeomorphism, so `f` is
    a local homeomorphism.
  - Properness from cocompactness and proper discontinuity. A proper local
    homeomorphism onto `R^3` is a covering, hence a homeomorphism.
- **Search and verification.** `experiments/heisenberg-contractible-rips-2026-09-16/`
  holds the search script, which found 20 passing sets with 7 inverse pairs
  in the box `|a|,|b| <= 1`, `|c| <= 2`, and the verification output.

### Consequence for the target

Neither named test object is a witness. A witness therefore cannot be detected
by any of the following alone:
- an exponential or cubic Dehn function;
- exponentially or polynomially distorted cyclic subgroups;
- non-automaticity;
- nilpotency without virtual abelianness;
- non-Hopficity.

The target stays OPEN. No negative mechanism was found.

## Approaches toward a negative answer, and where each dies

1. **Dimension, Euler characteristic, vertex count.**
   - Idea: if `R = Flag(Cay(G,T))` is contractible, then `R/G` is a finite
     `K(G,1)` with a single vertex.
   - Where it dies: every group of type F has such a model (collapse a
     maximal tree of any finite `K(G,1)`). `χ(G)` places no constraint on
     the simplex-orbit counts, and `dim R` is unrestricted. Dead.
2. **A free cocompact flag model exists; transitivity is the only gap.**
   - Idea: a finite CW `K(G,1)` is homotopy equivalent to a finite
     simplicial complex (standard; Hatcher Thm 2C.5, not re-checked). The
     barycentric subdivision of its universal cover is a contractible flag
     complex with a free cocompact `G`-action.
   - So any obstruction must use *one vertex orbit* together with *flagness*.
     That is, it must use that the complex is the clique complex of a Cayley
     graph.
   - Where it dies: contracting an equivariant forest that joins the vertex
     orbits gives one vertex orbit but destroys simpliciality. The clique
     complex of the resulting graph has new simplices whose homotopy type is
     uncontrolled. No invariant was found that separates the two situations.
3. **Coarse and persistence invariants.**
   - Idea: the Rips system of a group of type F is essentially contractible
     (this is already in the target's Attempts).
   - Where it dies: a witness needs a non-contractible complex for every `T`,
     but coarse invariants only see large scales, where classes die. No
     mechanism controls the scale-1 complex of *every* generating set.
4. **Distortion as an obstruction** (the motivation for the two test objects).
   - Idea: distorted cyclic subgroups might force `Cay(G,T)` to contain
     "short cuts" whose cliques create spherical classes.
   - Where it dies: Theorems 1 and 2. In `BS(1,2)` the chords `a^(-i) t`
     *are* the short cuts, and they triangulate the relator cells exactly. In
     `H_3(Z)` the extra generators `xz, yz, xy, xyz` give an affine Freudenthal
     triangulation of Nil. Distortion is absorbed by choosing `S`.
5. **Where the positive methods stop, as possible places to look for a witness.**
   - **Affine certificate (Theorem 2).**
     - It needs a properly discontinuous cocompact action of `G` on `R^d`
       by *affine* maps, with an equivariant vertex map.
     - Nilpotent groups without complete affine structures are expected to
       exist (Benoist, "Une nilvariété non affine", J. Differential Geom.
       1995; not fetched in this run, unverified). For those groups the
       method does not apply directly.
     - This does not make such groups witnesses. It only marks where this
       technique stops.
   - **Staircase triangulation (Theorem 1).**
     - It uses the specific relator shape `t a^m t^-1 a^-n`, whose relator
       polygon has two monotone sides.
     - For a general aspherical one-relator or 2-dimensional complex, chords
       with equal labels in different cells can create extra 3-cliques, and
       then the argument fails.
     - A 2-dimensional witness would have to defeat every chord
       triangulation of every finite aspherical 2-complex for `G`. No
       candidate was identified.

## Literature gate (2026-09-16)

- M. C. B. Zaremsky, *Some open problems* (personal problem list), §4, text
  read 2026-09-16.
  - Problem 4.7, "(Added 7/24/25): Relatedly, does every group of type F have
    a contractible Rips complex?", carries no answer note.
  - Problem 4.3 (`Z^n`) is marked as solved by Virk, arXiv:2405.09134 (not
    fetched).
- arXiv:2608.24279v1 (Li–Sánchez Saldaña) and arXiv:2608.25614v1
  (Hulbert–Zaremsky) are known to the graph through existing nodes. A re-fetch
  of their abstracts failed in this run (the arXiv connection was reset), so I
  make no claim about their contents regarding `BS(m,n)` or `H_3(Z)`.
- Graph searches (`bin/cairn search`) for Baumslag–Solitar, Heisenberg and
  nilpotent Rips nodes found no existing claim covering Theorems 1 or 2.
- Standard background, used without re-checking: Britton's lemma
  (Lyndon–Schupp, Ch. IV §2), the Whitehead and Hurewicz theorems (Hatcher),
  and degree theory for maps of closed surfaces. The standard non-membership
  facts for `H_3(Z)` (not CAT(0), not automatic, not Helly) are not used in
  any proof.
- I found no source stating Theorems 1 or 2. They may nevertheless be known.

## Open

- The target itself.
- A natural next test: does every torsion-free nilpotent group, or every
  polycyclic group, admit a contractible Rips complex?
  - For nilpotent groups, a candidate method is the local certificate
    combined with a non-affine equivariant map, for example a Mal'cev
    coordinate map. The difficulty is that simplices are then not mapped
    linearly.
- Another test: 2-dimensional groups of type F whose finite aspherical
  2-complexes all have relator cells with repeated long subwords.

## Referee (2026-09-16)

**Verdict:** both theorems are sound and honestly labelled. Landed with small
fixes. The target stays OPEN.

**Baumslag–Solitar (hand check).** I re-derived every step of the artifact:
- the relator polygon and its vertex labels;
- the chord label `s(r,i)`, including `s(m,N) = t`;
- the cellular `H_2` argument: the coefficient of `(x,t)` is
  `c_x - c_(x a^-n)`, and the cosets `x<a^n>` are infinite;
- (F2)–(F6) from Britton's lemma, including the case `n < 0`;
- Lemma B;
- both cases of Lemma C, including the index bookkeeping `b_(i+δ) = g a`;
- the `F_2` 2-cycle arguments of Lemmas D and E.

I found no gap. The properties the claim says cannot obstruct are stated
correctly: `<a>` is exponentially distorted in `BS(1,2)`, which is not
automatic, and `BS(2,3)` is non-Hopfian.

**Heisenberg (hand check).** I checked:
- the group law, the inverses and the listed elements of `S`;
- the affine form of left translation, and equivariance of the affine
  extension;
- the cone structure of `St(1)`;
- the degree argument;
- properness;
- the covering upgrade.

I found no gap. I added a short justification for the local model `w -> w^k`
at link vertices.

**Independent computation.** I wrote both scripts from scratch; neither
reuses solver code.
- `experiments/baumslag-solitar-contractible-rips-2026-09-16/referee_check_bs.py`
  uses its own Britton normal form. It checks 329 staircase generating sets
  in twelve groups beyond the solver's range, up to `BS(8,5)`, `BS(6,-9)` and
  `BS(7,7)`. For each set: `|S| = 2+2(m+N)`, exactly `3(m+N)` 3-cliques at
  `1`, and no 4-clique. Two non-staircase mutants are rejected.
- `experiments/heisenberg-contractible-rips-2026-09-16/referee_check_h3.py`
  recomputes (L1)–(L4) (`V,E,F,Q = 14,36,24,0`, `χ = 2`, ray count `{1}` over
  3000 directions). As a global sanity check, 300 random points of `[0,1]^3`
  each lie in exactly one affinely realized tetrahedron.
- I re-ran both solver scripts; their outputs match the committed files.

**Changes made.**
- BS artifact Remark 3 claimed a mutation test that is not in
  `check_bs_rips.py`. I corrected it and added Remark 4, describing the
  referee check.
- Fixed a markdown typo in Lemma B.
- The BS route and the Heisenberg artifact now mention the referee checks,
  which the proof does not use.
- Added a dated Attempts bullet to
  `some-type-f-group-has-no-contractible-rips-complex`, recording that both
  named test objects are ruled out.

**Literature gate, rechecked 2026-09-16.**
- Zaremsky, *Some open problems*
  (https://zaremsky.github.io/open_problems.pdf), fetched and text-extracted.
  Problem 4.7 "(Added 7/24/25)" still has no answer note, and the list does
  not mention Heisenberg or Baumslag–Solitar groups.
- arXiv abstracts of 2608.24279 (Li–Sánchez Saldaña, type R, closure under
  finite-edge-group graphs of groups, 2-dimensional RAAGs) and 2608.25614
  (Hulbert–Zaremsky, word-length Morse theory, triangle-free RAAGs at scale
  2), fetched. Neither abstract mentions BS, Heisenberg or nilpotent groups.
- arXiv API search for abstracts containing "Rips complex" together with
  Heisenberg, nilpotent or Baumslag: 0 hits.
- arXiv API search for "contractible Rips" / "contractible Vietoris": only
  2608.24279, 2410.11993 (Virk) and 1812.10976 (Zaremsky).
- Full texts were not read, so novelty is "no source found", not
  "certainly new", as the claim files already say.

**Not established.**
- The target itself.
- Whether all torsion-free nilpotent or polycyclic groups have contractible
  Rips complexes.
- The unfinished `H_3(Z)` slab construction in
  `every-type-f-group-has-a-contractible-rips-complex` is now superseded for
  `H_3(Z)` by the Freudenthal-pattern set. That node was not edited.
