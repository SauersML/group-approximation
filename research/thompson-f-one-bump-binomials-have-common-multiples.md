---
rg: 2
id: thompson-f-one-bump-binomials-have-common-multiples
kind: claim
title: In K[F] every one-bump element has property O, so twisted binomials of one-bump elements with any endpoint slopes have common right multiples with each other and with any element
distinct_from:
  thompson-f-rescaled-x0-binomials-have-common-multiples: that proves families, global torsion and products for the class O_1 of one-bump elements with property O, with members of endpoint slopes 2^{+-1}; this proves that O_1 contains every one-bump element, whatever its endpoint slopes.
  thompson-f-twisted-x0-binomial-is-ore-with-every-element: that is the single element x_0; this reruns its count with the shift phi^n for every one-bump g of slope 1/2 at 0, and reaches the other slopes through a finite-index copy of F.
---

**ESTABLISHED.** Let `K` be a field and `R = K[F]`. Notation (`F_[p,q]`, one-bump
element, property O, `O_1`) is that of
`thompson-f-rescaled-x0-binomials-have-common-multiples`.

1. **Every one-bump element has property O.** `O_1` is the set of all one-bump elements
   of `F`. There is no condition on the endpoint slopes.
2. **Consequences.** Items 1–3 of `thompson-f-rescaled-x0-binomials-have-common-multiples`
   hold for every one-bump element:
   - (a) for one-bump `g_1, ..., g_m` and `lambda_i` in `K^x`, `∩_i (1 + lambda_i g_i) R ≠ 0`;
   - (b) for one-bump `g`, `lambda` in `K^x` and nonzero `b` in `R`,
     `(1 + lambda g) R ∩ b R ≠ 0`;
   - (c) a unit times a finite product of twisted binomials `1 + lambda g` of one-bump
     elements has a nonzero common right multiple with every nonzero element, and such
     products together with one arbitrary element have a common right multiple.
3. **Binomials.** Let `u, w` be in `F` and `alpha, beta` in `K^x`. If `w u^-1` is one-bump,
   then `(alpha u + beta w) R ∩ b R ≠ 0` for every nonzero `b`, because
   `alpha u + beta w = alpha (1 + (beta/alpha) w u^-1) u`.

**Consequence for the roots.** A non-Ore witness for `thompson-f-is-not-amenable` needs
both sides outside the product class of item 2(c). A binomial side `alpha u + beta w` must
have a ratio `w u^-1` with at least two bumps. The shapes left open in
`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md` §4 lose "other germ
slopes"; multi-bump elements, genuine trinomials (`Q_4` with two full trinomials over a
field other than `F_2`, generic `P_(2,2)`) and evacuation of capacity `>= 2` remain.

**Scope.**
- A one-bump `g` with `g(t) < t` has slope `2^-m` at the left endpoint and `2^n` at the
  right one, `m, n >= 1`. Item 1 covers all `(m, n)`, and inverses cover `g(t) > t`.
- Not covered: elements with two or more bumps. The count pushes supports toward one
  endpoint by conjugating with powers of `g`, and an interior fixed point stops that.
- Novelty: not checked beyond this graph. Guba's survey arXiv:2305.07113 has not been
  read in full, and it may treat general one-bump elements.

Proof route: `thompson-f-one-bump-binomials-have-common-multiples-proof`.
