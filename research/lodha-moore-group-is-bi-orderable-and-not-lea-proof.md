---
rg: 2
id: lodha-moore-group-is-bi-orderable-and-not-lea-proof
kind: route
title: Germ order at the leftmost moved point, and proper quotients of the Lodha--Moore group are abelian
target: lodha-moore-group-is-bi-orderable-and-not-lea
requires: []
---

**Inputs, read from the arXiv abstract pages on 2026-09-12.**

- Lodha--Moore, arXiv:1308.4250: "In this article we will describe a finitely
  presented subgroup of Monod's group of piecewise projective homeomorphisms
  of R. This in particular provides a new example of a finitely presented
  group which is nonamenable and yet does not contain a nonabelian free
  subgroup. It is in fact the first such example which is torsion free."
- Burillo--Lodha--Reeves, arXiv:1509.04586 (Adv. Math. 332 (2018) 34-56):
  "We establish simplicity of the commutator subgroup of the group `G_0`,
  which admits a presentation with 3 generators and 9 relations. Further we
  show that every proper quotient of `G_0` is abelian."
- Trust surface: the theorem numbers inside the papers were not read.  The
  identification of the 3-generator, 9-relation `G_0` with the Lodha--Moore
  subgroup is the papers' own usage.

**1.** This is item 1 of the claim, from Lodha--Moore.

**2. Bi-orderability.**  Elements of Monod's `H` are homeomorphisms of
`P^1(R) = R u {infinity}` fixing `infinity`, projective on each of finitely
many intervals.  For `f in H` with `f != id` put
`m_f = inf {x in R : f(x) != x}` in `[-infinity, infinity)`.

- *Right germ.*  Let `J` be an interval just to the right of `m_f`:
  `(m_f, m_f + eps)` if `m_f` is finite, `(-infinity, -1/eps)` otherwise.
  Take `eps` small, so that `J` lies in one piece and `f|_J` is a projective
  map `phi`.  If `phi = id`, `f` would fix `J`, contradicting the choice of
  `m_f`.  A nontrivial projective map fixes at most two points of `P^1`.
  Shrinking `J`, we get that `f(x) - x` has constant nonzero sign on `J`.
- *Positive cone.*  Let `P` be the set of `f != id` with `f(x) > x` on `J`.
  The set `J` changes with `eps` but the sign does not.
- *Semigroup.*  Let `f, h in P`.  If `m_f < m_h`, then `h = id` near the
  right of `m_f`, so `fh = f` there and `fh in P`.  The case `m_h < m_f` is
  symmetric.  Suppose `m_f = m_h = m`.  Then `h` fixes `m`, or `h(y) -> -infinity`
  as `y -> -infinity` when `m = -infinity`.  So `h(y)` lies in the positive germ
  interval of `f` for `y` close to `m`, and `fh(y) > h(y) > y`.  In every case
  `m_(fh) = min(m_f, m_h)` and `fh in P`.
- *Trichotomy.*  `f` and `f^-1` have the same `m`, and opposite signs near it.
  So `H = P u P^-1 u {id}` disjointly.
- *Conjugation invariance.*  `g f g^-1` has `m_(g f g^-1) = g(m_f)`, since `g`
  is orientation preserving and fixes `infinity`.  Moreover
  `g f g^-1 (y) > y` iff `f(g^-1 y) > g^-1 y`.  So `g P g^-1 = P`.

`P` is the positive cone of a bi-invariant order on `H`, and on its subgroup
`G_0`.  Bi-orderable groups are locally indicable, locally indicable groups
are left-orderable, and left-orderable groups have unique products.

**3. Not LEA.**

- *LEA gives residual amenability.*  Let `F` be the finite set containing the
  generators, all prefixes of the relators and one element `c != 1`.  A local
  embedding of `F` into an amenable group sends every relator to `1`.  So it
  defines a homomorphism `G_0 -> A` with `A` amenable and `c` not in the
  kernel.  This is the window argument of
  `fp-upgrades-make-non-lef-and-non-lea-cheap`.
- *The commutator subgroup cannot be separated.*  Take `c != 1` in `G_0'`.
  `G_0` is nonamenable, so it is not abelian, and `G_0' != 1`.  Let
  `phi : G_0 -> A` be a homomorphism to an amenable group.
  - If `ker phi != 1`, then `G_0/ker phi` is a proper quotient, hence abelian
    (Burillo--Lodha--Reeves).  So `ker phi` contains `G_0'` and `phi(c) = 1`.
  - If `ker phi = 1`, then `G_0` embeds in `A` and is amenable, a
    contradiction.
- So `G_0` is not residually amenable, and not LEA.
- LEF implies LEA, so `G_0` is not LEF.  ∎
