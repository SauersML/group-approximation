---
rg: 2
id: equicontinuous-bs-bases-force-conjugator-entropy
kind: claim
title: A homeomorphism conjugating an equicontinuous map g to g^k has entropy at least log of the index of cl<g^k> in cl<g>, when no point is fixed by an element outside cl<g^k>
distinct_from:
  brin-thompson-proper-power-conjugates-have-zero-entropy: that shows the base g of a proper-power relation in nV has zero entropy and that the specific baker map has entropy at least log 2; this bounds the entropy of every conjugator f from below, in any compact metrizable space, as soon as the base is equicontinuous with a free divisible part.
  bg-in-isometric-brick-hosts-needs-unbounded-exponents: that excludes the landed BS(1,2) = <s,u> of 2V_tau as a Baumslag--Gersten image through the particular conjugator u and bounded exponent sums; this excludes every conjugator of s (and of any equicontinuous map with the same closure data) whenever the conjugator must have zero entropy, as for Higman's group.
  higman-group-images-in-nv-force-zero-entropy-bs12-cycles: that forces zero entropy on the four generators of an nV image of H4; combined with this node it forbids any of them to be equicontinuous with a free 2-divisible closure, in any finite-entropy host.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority
claimed). Route: `equicontinuous-bs-bases-force-conjugator-entropy-proof`.

## Statement

Let `X` be a compact metrizable space and `g, f` homeomorphisms of `X` with
`f g f^-1 = g^k` for some integer `k ≥ 2`. Suppose `g` is equicontinuous. Put
`Z = cl<g>` and `Z_k = cl<g^k>`, closures in `Homeo(X)` with the uniform topology,
and `m = [Z : Z_k]`. Assume

> **(H)** no point of `X` is fixed by an element of `Z \ Z_k`
> (for instance, `Z` acts freely on `X`).

Then the topological entropy of `f` satisfies `h(f) ≥ log m`.

Here `Z` is a compact abelian group, `Z/Z_k` is cyclic of order `m` dividing `k`,
and `m = k` when `Z` has a continuous quotient `Z/k` (for example `Z ≅ Z_2` and
`k = 2`, where `m = 2`).

## Consequences

1. **The odometer copy of `BS(1,2)`.** In `2V_tau`
   (`odometer-2v-is-fp-simple-and-contains-bs12`), `s = tau × id` is an isometry
   with `cl<s> ≅ Z_2` acting freely on `C × C`, and `m = 2`. So **every**
   homeomorphism `f` of `C × C` with `f s f^-1 = s^2` has `h(f) ≥ log 2`, not only
   the inverse baker map `u`. The same holds for every conjugate of `s`, and for
   the translations `x ↦ x + c` (`c` a 2-adic unit) of the affine hosts in
   `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`.
2. **Higman's group in finite-entropy hosts.** Let `H4 = <g_0..g_3 | g_i g_(i+1)
   g_i^-1 = g_(i+1)^2>` act on compact metrizable `X` so that every generator has
   finite entropy. This holds for every homomorphism into `nV`, `2V_tau`, the
   affine hosts `2V_(G_N)`, and any isometric-section brick group `𝔅_n`, by
   item 3 of `bg-in-isometric-brick-hosts-needs-unbounded-exponents`. Then every
   generator has zero entropy, so for each `i`:
   - if `γ_(i+1)` is equicontinuous and satisfies (H) with `k = 2`, then
     `cl<γ_(i+1)^2> = cl<γ_(i+1)>`, that is, `cl<γ_(i+1)>` has no continuous
     quotient `Z/2`.

   In particular no generator of a nontrivial image of `H4` in such a host acts as
   `s`, as any conjugate of `s`, or as any free 2-adic translation.
3. **Baumslag--Gersten.** The same holds for the generator `a` of
   `BG = <a,t | b a b^-1 = a^2>`, `b = t a t^-1`, in any finite-entropy host,
   because `h(b) = h(a) = 0`.
4. **General `BS(1,k)`.** For `k ≥ 2` and `cl<g>` isomorphic to the `k`-adic
   integers (with `g ↦ 1`) acting freely, conjugators of `g` to `g^k` have entropy at least `log k`. This matches
   the baker map for `k = 2`, which has `h = log 2`.

## Sharpness

- **Odd closures give nothing.** On `Z_3`, `g = (x ↦ x+1)` and `f = (x ↦ 2x)` satisfy
  `f g f^-1 = g^2`. Here `f` is an isometry with zero entropy, and `m = 1`, since
  `2` is a 3-adic unit.
- **The bound is attained.** For `s` and the baker map `u` in `2V_tau`,
  `h(u) = log 2`: the baker map is conjugate to the two-sided full 2-shift
  (textbook, not pinned here), and item 4 of
  `brin-thompson-proper-power-conjugates-have-zero-entropy` gives the lower bound.

## What this does not decide

It constrains only equicontinuous generators with a free divisible part. A copy of
`H4` in `nV`, `2V_tau` or `𝔅_n` with no equicontinuous generator, or whose
equicontinuous generators have odd procyclic closures, is not excluded.
`higman-group-satisfies-boone-higman` stays OPEN.
