# Bestvina--Brady kernels: a hyperlinear obstruction to embeddings and the ε-map route (lane hl-eg-bestvina-brady, 2026-09-14)

This builds on `research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md`, which pinned
Theorem 8.7 and its proof from the Springer PDF. It adds three results and states the exact
gap. All results are unreviewed.

## 1. Sources read by this lane

**Bestvina--Brady, Invent. Math. 129 (1997) 445--470.**
- Copy used: the open course copy
  `https://people.math.osu.edu/davis.12/courses/8800-20/Bestvina-Brady.pdf`, fetched with
  curl and converted with pdftotext. Ligature glyphs were lost and are restored below.
- **Lemma 2.3 (p. 448).** "If J ⊂ J′ ⊂ R are connected and X_J′ \ X_J contains no vertices of
  X, then X_J ↪ X_J′ is a homotopy equivalence."
- **Lemma 2.5 (p. 449).** "Let f : X → R be a Morse function on an affine cell complex as
  above. Suppose J ⊂ J′ ⊂ R are closed and connected, inf J = inf J′, and J′ \ J contains only
  one point r of f(0-cells). Then X_J′ is homotopy equivalent to X_J with the copies of
  Lk↓(v, X) (v a vertex with f(v) = r) coned off. A similar statement holds when inf J = inf J′
  is replaced by sup J = sup J′ and Lk↓(v, X) by Lk↑(v, X)."
  - Proof, last sentence: "These strong deformation retractions induce a strong deformation
    retraction of X_J′ onto X_J with the cones attached as stated in the Lemma."
- **p. 454.** "The map Q_L → S¹ lifts to a φ-equivariant Morse function f : X → R with the
  ↑-links and ↓-links all isomorphic to L".
- **Theorem 8.6 (p. 468).** "X_J is homotopy equivalent to the wedge of L's, one for every
  vertex of X not in X_J."
- **After Definition 8.8 (p. 469).** "The homeomorphism above becomes a quasi-isometry, with
  constants which are independent of |f(v) − t|."
- **Proof of Theorem 8.7 (p. 469).**
  - "Thus point preimages of φ will have diameters bounded by the quasi-isometry constants."
  - "For vertices v with |f(v) − t| large enough one can define a left homotopy inverse to φ_v
    by taking each vertex of φ_v(S_(v,L)) to a point of its φ_v-preimage, and extending over
    skeleta."
- **Remark (p. 470).** "Fix a metric on L. We conjecture that there is ε > 0 such that if
  g : L → K is a surjective PL ε-map, then K is homotopy equivalent to L with 1- and 2-cells
  attached. This conjecture implies that the geometric dimension of H_L is 3."
  - The source gives no proof of the implication.

**Howie 1999.** J. Howie, *Bestvina--Brady groups and the plus construction*, Math. Proc.
Cambridge Philos. Soc. 127 (1999), no. 3, 487--493, doi:10.1017/S0305004199003928. Abstract
from Cambridge Core, verbatim excerpts:
- "we show that these Bestvina–Brady complexes are (up to homotopy equivalence) formed by
  applying the Quillen plus construction to certain finite 2-complexes"
- "we recover the result of Bestvina and Brady [1] that the Bestvina–Brady groups act freely
  on acyclic 2-complexes, and hence have cohomological dimension at most 2"
- "we use our construction to give an alternative proof of the cited theorem of Bestvina and
  Brady; at least one of the Eilenberg–Ganea and Whitehead conjectures is false"

The body is paywalled and was not read. Novelty of §2 relative to Howie is therefore unchecked.

**Gersten, arXiv:1501.06875v3.** The abstract, via a web tool, includes "A finite connected
subcomplex of an aspherical 2-complex is aspherical iff its fundamental group is of
cohomological dimension 2."

**Leary, arXiv:1512.06609v4.** Pages 1--3 were read, and the full text was grepped. It
introduces `G_L(S)`, interpolating between `G_L(∅) ≅ BB_L~ ⋊ π_1(L)` and `G_L(Z) = BB_L`. The
grep finds no statement about Eilenberg--Ganea or Whitehead, and no geometric-dimension result.

**Nguyên-Phan, arXiv:1907.12063v1 (2019).** Read from the arXiv PDF.
- It restates the Remark as Conjecture 1 for any finite 2-complex and says "it remains open".
- Its Theorem 3 shows that in dimension 1 the relative form fails: a small-fiber loop need not be
  a free-basis element. The literal form holds in dimension 1.
- Pins are in `bestvina-brady-epsilon-map-conjecture`.

**Nitsche--Thom Theorem 1.2.** Taken as pinned on main in
`kervaire-laudenbach-holds-for-hyperlinear`.

## 2. Results

**A. `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear` (ESTABLISHED).** A finite
acyclic subcomplex `K` of a contractible 2-complex has trivial or non-hyperlinear `π_1`.
- Proof: kill `π_1(K)` at a finite stage `K ∪ a e¹ ∪ b e²` with `H_2 = 0`.
- Since `H_1(K) = 0`, the exponent-sum matrix is injective, so Nitsche--Thom 1.2 embeds `π_1(K)`
  in the stage group, where it is trivial.
- Corollary: the Poincaré spine, or any acyclic finite 2-complex with nontrivial finite `π_1`,
  is not a subcomplex of any contractible 2-complex.

**B. `epsilon-map-conjecture-gives-poincare-kernel-gd-three` (route).** This proves the unproved
sentence of the Remark.
- Rescaling the shadow `S_(v,L)` by `1/|f(v) − t|` turns `φ_v` into a surjective PL ε-map, with
  ε → 0.
- The conjecture gives `K_v ≃ M`, a 2-complex containing `L`.
- Transport: the pushout `M ∪_(K_v) Y` is contractible and contains `L`, which contradicts A.
- Only a weak form (E) is used: `K_v` is homotopy equivalent to some 2-complex containing `L` as
  a subcomplex. No `π_2` hypothesis is used. So the route covers every acyclic flag 2-complex
  with nontrivial hyperlinear `π_1` that satisfies (E), aspherical ones included.

**C. `bb-kernel-gd-two-if-l-lies-in-contractible-2-complex` (ESTABLISHED).** If `L` is a
subcomplex of a contractible 2-complex `Z`, then `gd(H_L) ≤ 2`.
- Run Lemma 2.5 from `X_t` outward, one critical level at a time.
- At each level, glue `H_L`-orbits of copies of `Z` along cellular approximations of the
  attaching maps, instead of coning off copies of `L`.
- A homotopy pushout along `L ↪ Z` with `Z ≃ *` is the mapping cone, so every stage is
  homotopy equivalent to `X_J`. The union is a contractible free `H_L`-2-complex.
- By A, the hypothesis forces `π_1(L)` to be trivial or non-hyperlinear. C is honest but nearly
  vacuous on hyperlinear inputs.

**Combined picture for acyclic `L` with nontrivial hyperlinear `π_1`:**
- **Sufficient for gd 2.** C's embedding hypothesis never holds (A).
- **Necessary for gd 2** (the Bestvina--Brady proof). `L` is a homotopy retract of a small-fiber
  PL image `K_v ⊆ Y`.
- **The gap between them.** Upgrading "homotopy retract of a small-fiber image" to "homotopy
  equivalent to a 2-complex containing `L`" is exactly (E). If (E) holds, gd is 3.

## 3. Attempts that failed

1. **Pushing the killing system along the retraction `r: K_v → L`.** For
   `Z' = K_v ∪ a e¹ ∪ b e²`, the exact sequence gives `ker E ↪ H_1(K_v)`, and `H_1(K_v)` is free
   abelian and can be nonzero. Relators with zero exponent rows may map under `r_*` to arbitrary
   elements of `π_1(L)`. So Nitsche--Thom does not apply. The Whitehead-side subcomplex alone
   gives no contradiction, as the 2026-09-13 artifact already found.
2. **Proving (E) directly.**
   - For ε below a Lebesgue number of the open-star cover of `L`, coarse lifting builds
     `λ: K → L` with `λ g ≃ id`, as in Bestvina--Brady. Point preimages of `K` near a point lie
     within `ε + 2η` of one fiber, by upper semicontinuity.
   - The relative version, with `L` included through `g` itself, is false already in dimension
     1 (Nguyên-Phan, Theorem 3). So any proof of (E) has to change the inclusion.
   - Upgrading to (E) for `g` itself is a relative D2-type problem. The obstruction
     `H_3(M~_g, L~) = ker(Z[π_1 K] ⊗_(Z π_1 L) π_2(L) → π_2(K))` need not vanish. (E) allows other
     inclusions, which this computation does not rule out.
   - Examples all satisfy (E): collapsing a small subcomplex `F`, since `ΣF ≃ ∨S²` when
     `H_2(F) = 0` and `H_1(F)` is free; identifying two small discs or annuli; folds.
3. **L² and Euler characteristic.** Dead, per `ideas-topology-2026-09-14` I5.

## 4. Exact gap

(E) for a flag triangulation `L` of the Poincaré spine: for some ε > 0, every surjective PL
ε-map `g: L → K` has `K` homotopy equivalent to a 2-dimensional CW complex containing `L` as a
subcomplex. It is needed only for the maps `φ_v` in the proof of Theorem 8.7.
- If true, `H_L` refutes Eilenberg--Ganea.
- (E) has Whitehead-type strength. Through A it forbids any small-fiber PL image of `L` from
  lying in a contractible 2-complex. So the route converts Eilenberg--Ganea into a
  Whitehead-type property of images; it is not an unconditional result.

MSI was down for the whole lane (after the 08:13 reboot), so no Cairn check was run.
