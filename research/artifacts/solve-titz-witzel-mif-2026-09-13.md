# solve-titz-witzel-mif, 2026-09-13

Target: `titz-witzel-kernels-are-mif`. The criterion and the density lemma land
with complete proofs. Three building premises are OPEN.

## Source pins

The quotes below were transcribed from rendered PDF pages, not copied from TeX.

**Caprace--Ciobotaru, *Gelfand pairs and strong transitivity for Euclidean
buildings*, arXiv:1304.6210v2.**

- **Theorem 1.2 (p. 3):** "Let G be a group acting cocompactly by automorphisms
  on a locally finite Euclidean building Δ. Then G contains a strongly regular
  hyperbolic element." The same page adds: "The special case when G is discrete
  can be deduced from Ballmann–Brin [BB95], where they use a Poincaré recurrence
  argument on the geodesic flow."
- **Definition 2.2 (p. 4):** "We say that γ is strongly regular hyperbolic if γ
  is regular hyperbolic and if one (and hence all) of its translation axes
  crosses all the walls of the unique apartment contained in Min(γ)."
- **Lemma 2.3 (p. 4):** "Let Δ be a Euclidean building and γ ∈ Aut(Δ) be a
  type-preserving automorphism. Then γ is strongly regular hyperbolic if and
  only if γ is a hyperbolic isometry and the two endpoints of one (and hence
  all) of its translation axes lie in the interior of two opposite chambers of
  the spherical building at infinity. In particular, if γ is strongly regular
  hyperbolic, then Min(γ) is an apartment."
- **Proposition 2.9 (p. 7), second paragraph of the conclusion:** "…there is an
  increasing sequence {f(n)}_n of positive integers such that, for all
  n > m > 0, there is a hyperbolic isometry h_{m,n} ∈ G which has a translation
  axis containing the geodesic segment [ρ(t_{f(m)}), ρ(t_{f(n)})]. If in addition
  X is a locally finite Euclidean building and the geodesic line ρ(R) is
  strongly regular, then h_{m,n} is a strongly regular hyperbolic automorphism."
- **Proposition 2.10 (p. 8):** "Let Δ be a Euclidean building and a ∈ Aut(Δ) be a
  type-preserving strongly regular hyperbolic element with unique translation
  apartment A. Let c₋ ∈ Ch(∂A) be the unique chamber containing the repelling
  fixed point of a. Then, for any ξ ∈ ∂Δ, the limit lim_{n→∞} aⁿ(ξ) exists (in
  the cone topology) and coincides with ρ_{A,c₋}(ξ) ∈ ∂A. In particular, the
  fixed-point-set of a in ∂Δ is ∂A."
- **Retraction (p. 12):** "Given an apartment A in a Euclidean building Δ and a
  chamber at infinity c contained in ∂A, there is a map ρ_{A,c}: Δ → A, called
  the retraction on A based at c, characterised by the following properties:
  the restriction of ρ_{A,c} to A is the identity on A and the restriction of
  ρ_{A,c} to any apartment B whose boundary contains c, induces an isomorphism
  of B onto A."

**Neyt--Parkinson--Van Maldeghem, *Uniclass automorphisms of spherical
buildings*, arXiv:2403.17443v1.**

- **Abstract (p. 1):** "An automorphism of a building is called uniclass if the
  Weyl distance between any chamber and its image lies in a single (twisted)
  conjugacy class of the Coxeter group."
- **Theorem 1 (p. 1):** "Let θ be a nontrivial automorphism of a thick irreducible
  spherical building Δ of rank at least 2. Then θ is uniclass if and only if θ
  is either anisotropic, or: (1) Δ has type I₂(2m) (m ≥ 2) and in the associated
  generalised 2m-gon (a) θ is a collineation that elementwise fixes an ovoid or
  a spread, or (b) θ is a polarity …"
- **Table 1 (p. 3), row I₂(2m):** "an ovoid or a spread | Cl(s_i), i ∈ {1, 2}".
- **Consequence drawn here.** In W(I₂(4)), the dihedral group of order 8,
  `Cl(s_i)` consists of reflections, while the longest element `w₀ = (s₁s₂)²` is
  a rotation. So these collineations map no chamber to an opposite chamber: they
  are domestic.

**Web summaries, not read at source.** These came from fetch summaries and must
not be quoted as their authors' words.

- **BFFHZ arXiv:2503.21882v2, Remark 3.5:** Burger–Mozes groups are highly
  transitive and MIF. The proof shows the action on a tree boundary is
  topologically free, using extreme proximality.
- **Vigdorovich arXiv:2503.12737v3, Theorem 1.2:** linear effective
  mixed-identity-freeness for cocompact lattices in PSL_d(K), K a local field.
  It doesn't apply: the Titz–Witzel lattices aren't residually finite, so they
  aren't linear.

## Why (GP) needs non-domesticity

- **Pairs used.** The chase in `opposition-ping-pong-mif-criterion-proof` uses
  only the pairs `(s_i, −s_{i−1})`.
- **Sign changes.** A sign change `x^{+}·g·x^{−}` asks `g` to map a pole to an
  opposite chamber.
- **Rank one vs rank two.** In rank one, "opposite" means "distinct", so
  topological freeness is enough. In rank two it isn't.
- **Products of trees.** On `T₁ × T₂` the condition becomes topological
  freeness on each factor boundary.

## Checks

- Local lint before landing: ids are at most 64 characters, every node has a
  title, and every `requires` and `distinct_from` entry names a claim on main or
  in this commit.
