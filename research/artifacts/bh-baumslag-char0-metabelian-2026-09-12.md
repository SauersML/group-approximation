# Boone--Higman for Baumslag's torsion-free metabelian group

Lane `bh-baumslag-char0-metabelian`, swarm 6, 2026-09-12.

## 1. The group and what is known

```text
B = < a, s, t | [s,t], [a, a^t], a^s = a a^t >  ≅  R x| Z^2,
R = Z[x^±1, (1+x)^-1],   s.r = (1+x) r,   t.r = x r.
```

Facts about `B`:
- **Finitely presented.** Baumslag 1972. The derived subgroup `R` is free abelian
  of infinite rank.
- **Linear over `Q(x)`, and residually finite.** Use
  `r -> [[1,r],[0,1]]`, `s -> diag(1+x,1)`, `t -> diag(x,1)`. Route
  `baumslag-char-zero-bh-via-char-zero-linear-groups`.
- **Linear in no positive characteristic.** A finitely generated solvable linear
  group in characteristic `p` is virtually (unipotent `p`-group)-by-abelian. `B`
  is torsion-free and not virtually abelian.
- **Every nontrivial normal subgroup meets `R` in a nonzero ideal.** An embedding
  of `B` into a finite product is therefore faithful on one factor, so
  mixed-characteristic products do not help.
- **It contains `Z wr Z = Z[x^±1] x| <t>`,** which lies in Thompson's `F` and
  so satisfies Boone--Higman.

Baumslag's group with the extra relation `a^p` is covered by the
positive-characteristic Leavitt hosts
(`positive-char-surface-linear-groups-satisfy-boone-higman`). The torsion-free
`B` is the first case of BBMZ Problem 5.3(7) outside the hosts found so far.

## 2. Theorem: `B` is not self-similar

`baumslag-char-zero-metabelian-group-is-not-self-similar`, with proof route
`baumslag-char-zero-metabelian-not-self-similar-proof`. For every `d >= 2`, every
homomorphism `B -> Aut(T_d)` with state-closed image has nontrivial kernel.
Intransitive actions are included.

**Mechanism.**
- **Joint cores.** A faithful state-closed action gives virtual endomorphisms
  `f_i : H_i -> B` with trivial joint core.
- **Each `f_i` is rigid.** Every `f_i` either kills a nonzero ideal of `R`, or
  acts on `H_i ∩ R` as `r -> lambda sigma(r)` with `lambda in R` and `sigma` one
  of the six anharmonic automorphisms of `R`, which permute `0, -1, infinity`.
- **Where the rigidity comes from.**
  - The support of `R` is the curve `s = 1 + t` in the 2-torus.
  - Restricting to a finite-index sublattice is birational on it:
    `Q(x^m,(1+x)^m) = Q(x)`.
  - A field map sending monomial units to monomial units solves the unit equation
    `U + V = 1` in `Q(x)`. Mason--Stothers leaves only the six Möbius
    permutations.
  - `lambda in R` because `R/pR` is a domain for every prime `p`, and the
    domain of `f_i` has finite index.
- **Conclusion.** A nonzero `Aut(R)`-stable ideal inside all `H_i` and all
  kernels lies in the joint core.

**Contrast with `Z wr Z`.** Dantas--Santos--Sidki (arXiv:2004.08941) build a
faithful intransitive state-closed action of `Z wr Z` of degree 3, with 3 states
(Proposition 3.1, read through a summarizing fetch of the ar5iv rendering). The
reason it works: the support of `Z[t^±1]` is the whole 1-torus, and restricting to
`mZ` has degree `m`. That leaves room for the decimation map
`sum c_k t^k -> sum c_(mk) t^k`, which contracts. `B` has no such room.

**Relation to the literature** (read through summarizing fetches of the ar5iv
renderings):
- Kochloukova--Sidki (arXiv:1710.04745), Theorem C: metabelian `B x| Q` with `B`
  of Krull dimension 1 and trivial centralizer is transitive self-similar. Their
  remark: "By the main result of Dantas and Sidki, Theorem C does not hold for
  metabelian groups, where the Krull dimension of B is bigger than 1".
- Their Section 7 localizes the example `C_p wr Z^d`, which is characteristic
  `p`.
- The theorem here is the intransitive statement for the characteristic-zero
  curve module of `B`. No novelty claimed.

**Scope.** The theorem does not exclude a larger finitely presented self-similar
group containing `B`. That would suffice: by Zaremsky, arXiv:2405.09722v2,
Theorem 1.1, every subgroup of such a group satisfies Boone--Higman. His
definition, read from the arXiv HTML through a summarizing fetch, is
`G <= Aut(T_d)` with image in `S_d wr_d G`, and does not require transitivity.

## 3. Attempts recorded on the open claim

`baumslag-char-zero-metabelian-group-satisfies-boone-higman`, `## Attempts`:
- self-similarity of `B` itself: dead, Section 2;
- affine digit hosts: dead, `affine-self-similar-coordinate-rings-are-one-dimensional`;
- algebra unit hosts: dead, `char-zero-algebra-unit-hosts-exclude-unipotents`;
- characteristic-`p` hosts and products: dead for `B`, Section 1;
- the `p`-adic tree action and BLIW Theorem B: dead for `B`'s own action,
  Section 4;
- twisted Brin--Thompson hosts: owned by lane `bh-type-a-actions`.

## 4. The `p`-adic tree route in more detail

**The action.** Choose `xi in Q_p` transcendental with `v_p(xi) = 1`, and embed
`R -> Q_p` by `x -> xi`. Then `B <= PGL_2(Q_p)` acts on the
`(p+1)`-regular Bruhat--Tits tree.
- **Faithful.** The image is upper triangular with `(2,2)`-entry 1, so it
  contains no nontrivial scalar.
- **Vertex-transitive.** `R` is dense in `Q_p`, since it contains `Z` and
  `xi^-1`, so translations reach every ball of a given radius. `t` shifts radii
  by one.
- **Finitely many edge orbits.** Translations in `R ∩ Z_p` hit every residue
  mod `p`.

**Edge stabilizers.** For the edge `(Z_p, pZ_p)` the stabilizer is
`E = (R ∩ pZ_p) x| <1+xi>`. `E` is finitely generated iff `R ∩ pZ_p` is a
finitely generated `Z[(1+xi)^±1]`-module, and it is not:
- `p^(k+1) xi^-k` lies in `R ∩ pZ_p` for every `k`;
- `xi^-1` does not lie in `Z[xi,(1+xi)^±1]`, because `xi` is transcendental;
- so a finitely generated submodule lies in some `xi^-n Z[xi,(1+xi)^±1]`, which
  misses `p^(n+2) xi^-(n+1)`.

So Theorem B of Bux--Llosa Isenrich--Wu
(`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`) does not apply to
this action.

**Other valuations.**
- If `v_p(xi) = 0 = v_p(1+xi)`, then `B` fixes the vertex `Z_p`, and there are
  infinitely many vertex orbits.
- The remaining cases, `v_p(1+xi) > 0` or `v_p(xi) < 0`, are the images of the
  first case under the anharmonic symmetries.

**Untested enlargement.** The finitely generated metabelian overgroup
`G = R[1/p] x| <xi, 1+xi, p>`, with `U_0 = <1+xi, p/xi>` of valuation zero, acts on
the same tree cocompactly and faithfully. Its edge stabilizer is
`(R[1/p] ∩ pZ_p) x| U_0`. Theorem B needs this to be finitely presented, and the
Bieri--Strebel criterion (2-tameness of the module over `Z[U_0]`) decides that.
- **Heuristic, not a proof.** The support curve `w(y-1) = p`, with
  `y = 1+xi` and `w = p/xi`, has a `p`-adic point with valuation vector `(0,1)`.
  The trivial valuation gives the rays `(1,0)`, `(0,-1)` and `(-1,1)`. So
  `Sigma^c` appears to contain the antipodal pair `(0,±1)`, which would mean not
  finitely presented.
- **Obstacle to a proof.** The module `R[1/p] ∩ pZ_p` is not an ideal of
  `R[1/p]`, so its `Sigma`-invariant is not the ring's logarithmic limit set as
  stated.

Recorded as an Attempt only; no graph node.

## 5. Sources and verification

- Dantas--Santos--Sidki, arXiv:2004.08941: abstract, the G-data definition,
  Proposition A (kernel = F-core) and Proposition 3.1.
- Kochloukova--Sidki, arXiv:1710.04745: abstract, Theorem C and Section 7.
- Zaremsky, arXiv:2405.09722v2: definition of self-similar and Theorem 1.1.

All three were read through summarizing web fetches (arXiv abstract pages,
ar5iv, arXiv HTML), not from PDF text on MSI.

The theorem in Section 2 does not depend on any of these sources. Its Step 0 is
proved from scratch.
