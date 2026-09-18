---
rg: 2
id: hyperbolic-cayley-graph-ozawa-boundary-facts
kind: claim
title: "Cayley graphs of hyperbolic groups are hyperbolic in Ozawa's thin-triangle sense, and limits of geodesics to convergent vertices connect to the limit point in Bowditch's compactification"
distinct_from:
  kazhdan-host-route-imports-have-verbatim-sources: that is the citation gap for exactness to an amenable compact model and for (T) plus Haagerup is finite; this is a different, narrower gap about the geometry of Cayley graphs of hyperbolic groups in Ozawa's framework, which the expansive host route uses in place of exactness.
  hyperbolic-group-cantor-model-simple-kazhdan-not-mf: that asks for a minimal topologically free Cantor action with a north-south element; this records two boundary facts used to show the horofunction subshift is an amenable model.
---

**OPEN (narrow import gap).** Let `Γ` be a finitely generated word-hyperbolic group, let
`S = S^{-1}` be a finite generating set not containing `e`, and let `K = Cay(Γ, S)` (vertices
`Γ`, edges `{g, gs}`). The notation follows N. Ozawa, *Boundary amenability of relatively
hyperbolic groups*, arXiv:math/0501555, §2 (source tex, l.159–262).

**Claim.**

1. **Thin triangles.** There is `δ > 0` such that `K` is *hyperbolic* in Ozawa's sense.
   Verbatim definition: "for any geodesic paths $\alpha$ and $\beta$ with
   $\alpha_-=\beta_-=z$ and any $k\le\ip{\alpha_+,\beta_+}_z$, we have
   $d(\alpha(k),\beta(k))<\delta$."
2. **Limits of geodesics.** Let `x ∈ V(K)`, let `z_n → z` in `ΔK` with `z ∈ ∂K`, and let
   `α_n ∈ F(x, z_n)` be geodesic paths such that `α_n` agrees with `α_{n'}` on `[0, n]`
   whenever `n ≤ n'`. Then the infinite geodesic `α(k) = α_k(k)` satisfies `α ∈ F(x, z)`,
   that is, `α_+ = z`.

**Why this is a gap and not an import.**

- Item 1 is the standard fact that a `δ'`-hyperbolic geodesic space has uniformly thin
  (tripod-thin) triangles, applied to the Cayley graph with `δ = 4δ' + 1`. It has not been
  quoted verbatim from a source whose definition of hyperbolicity is matched to Ozawa's.
  Likely references, not verified: Ghys–de la Harpe, *Sur les groupes hyperboliques*,
  Ch. 2, Prop. 21; Bridson–Haefliger III.H.1.17.
- Item 2 is stated in the proof that `M(x, A)` is open, in Ozawa l.254–257: "Since the set
  of geodesic paths connecting any two points is locally finite, we may pass to a
  subsequence and assume that $\alpha_n(1)=\cdots=\alpha_n(n)$ for every $n$. It follows
  that the geodesic path $\alpha$, given by $\alpha(n)=\alpha_n(n)$, connects $x$ to $z$".
  So it is an in-proof assertion ("It follows"), not a displayed statement, and its proof
  is deferred to Bowditch's §8.

**Verified so far (verbatim, Ozawa).**

- Fine: "for any $n$ and any edge $e\in E(K)$, the set $C(e,n)$ of circuits of length at
  most $n$ containing the edge $e$ is finite." Every locally finite graph is fine.
- Boundary: "The Gromov boundary $\bk$ of $K$ is defined as the set of all equivalence
  classes of infinite geodesic paths in $K$." So an infinite geodesic determines its
  endpoint `α_+`.
- Theorem bowditch: "The family $\{M(x,A)\}_A$ defines a neighborhood base for
  $x\in\dk$. With this topology, $\dk$ is a compact topological space, in which $V(K)$ is
  dense. Every graph automorphism on $K$ uniquely extends to a homeomorphism on $\dk$."

## Attempts

- **Direct proof of item 2 from the neighbourhood base (deferred, 2026-09-17, e-nv-affine).**
  - The plan: if `α_+ ∉ M(z, A)` for every finite `A`, a geodesic from `z` to `α_+`
    through a fixed vertex would give, by thinness (item 1) and uniform fineness, geodesics
    from `x` to `z_n` passing within `δ` of a fixed finite set. That contradicts
    `z_n → z`.
  - Where it stalls: Ozawa's neighbourhoods `M(x, A)` are based at the limit point `z`,
    which is ideal, so the argument needs geodesic lines between two ideal points and
    Bowditch's equivalent base `M'(w, B)` (§8). Neither has been read. The attack was
    deferred in favour of reading Bowditch.

A closing route should quote a thin-triangle statement whose constant matches item 1. For
item 2 it should quote Bowditch, *Relatively hyperbolic groups*, §8, or give a direct
proof from the neighbourhood base `M(x, A)`.
