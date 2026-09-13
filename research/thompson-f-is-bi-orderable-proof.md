---
rg: 2
id: thompson-f-is-bi-orderable-proof
kind: route
title: Germ order at the leftmost moved point for piecewise linear homeomorphisms of the interval
target: thompson-f-is-bi-orderable
requires: []
---

Let `G` be any group of orientation-preserving homeomorphisms of `[0,1]` in
which every element has finitely many breakpoints and is affine between
consecutive breakpoints.  `F` is such a group.  We put a bi-invariant order on
`G`.

**1. The germ sign.**  For `f in G` with `f != id` put
`m_f = inf {x in [0,1] : f(x) != x}`, so `m_f in [0,1)`.

- `f` fixes `[0, m_f]` pointwise, by continuity.
- Choose `eps > 0` so that `(m_f, m_f + eps)` contains no breakpoint of `f`.
  On that interval `f(x) = lambda x + c`, and `f(m_f) = m_f` gives
  `f(x) - x = (lambda - 1)(x - m_f)`.
- `lambda != 1`, since otherwise `f` would fix `(m_f, m_f + eps)`, contradicting
  the choice of `m_f`.

So `f(x) - x` has the constant nonzero sign of `lambda - 1` just to the right of
`m_f`.

**2. The positive cone.**  Let `P` be the set of `f != id` with `f(x) > x` just
to the right of `m_f`.

**3. `P` is a semigroup.**  Let `f, h in P`.

- *`m_f < m_h`.*  `h` is the identity on `[0, m_h]`, so `fh = f` just to the
  right of `m_f` and `fh` fixes `[0, m_f]`.  So `m_(fh) = m_f` and `fh in P`.
- *`m_h < m_f`.*  Just to the right of `m_h`, `h(x) > x` and, by continuity and
  `h(m_h) = m_h`, `h(x) < m_f`.  So `f(h(x)) = h(x) > x` there, and `fh` fixes
  `[0, m_h]`.  So `m_(fh) = m_h` and `fh in P`.
- *`m_f = m_h = m`.*  Just to the right of `m`, `h(x) > x`, and `h(x)` is still
  just to the right of `m` by continuity.  So `f(h(x)) > h(x) > x`, and `fh`
  fixes `[0, m]`.  So `m_(fh) = m` and `fh in P`.

**4. Trichotomy.**  `f^-1` fixes exactly the points `f` fixes, so
`m_(f^-1) = m_f`.  Its slope just to the right of `m_f` is `lambda^-1`, so the
germ signs of `f` and `f^-1` are opposite.  Hence `G` is the disjoint union of
`P`, `P^-1` and `{id}`.

**5. Conjugation invariance.**  Let `g in G`.  `g` is an increasing bijection of
`[0,1]`, so the moved set of `g f g^-1` is `g` of the moved set of `f`, and
`m_(g f g^-1) = g(m_f)`.  For `y` just to the right of `g(m_f)`, `x = g^-1 y` is
just to the right of `m_f`, and `g f g^-1(y) > y` iff `f(x) > x` because `g` is
increasing.  So `g P g^-1 = P`.

By 3–5, `x < y` iff `x^-1 y in P` defines a total order on `G` invariant under
left and right multiplication.

**6. Torsion-freeness.**  If `f in P`, then every power `f^n` with `n >= 1` lies
in `P` by 3, so `f^n != id`.  The same holds for `f in P^-1`.  ∎
