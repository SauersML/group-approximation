---
rg: 2
id: one-relator-products-three-groups-short-relators-citation
kind: route
title: Import Chinyere--Howie Theorem 1.3 on one-relator products of three groups with short relators
target: short-relator-three-factor-one-relator-products-are-nontrivial
requires: []
---

Citation import, not reproved. Source: I. Chinyere and J. Howie, *Non-triviality of some
one-relator products of three groups*, arXiv:1509.02717 (e-print dated 28 October 2015),
file `Nontriviality.tex`, fetched on MSI on 2026-09-13 and read at the lines given. The
journal version (Internat. J. Algebra Comput. 26 (2016) 533–550, as listed by a web
search) was not read. TeX macros are stripped from the quotes.

- **Abstract, l.88–91:** "In this paper we study a group G which is the quotient of a
  free product of three non-trivial groups by the normal closure of a single element.
  In particular we show that if the relator has length at most eight, then G is
  non-trivial. In the case where the factors are cyclic, we prove the stronger result
  that at least one of the factors embeds in G."
- **l.104–106, Conjecture 1.1:** "A one-relator product on three non-trivial groups is
  non-trivial." l.108: "Conjecture 1.1 is an extension of the Scott-Wiegold conjecture
  (see Problem 5.53 in [Kh]). The latter problem was solved by the second author
  [Howie8], who also conjectured that a free product of (2n-1) groups is not the normal
  closure of n elements." Conjecture 1.1 is attributed there to [Fint] (Fintushel–Stern,
  Math. Z. 175 (1980)) and [Den2] (Gordon, Trans. Amer. Math. Soc. 275 (1983)).
- **l.128–130, Theorem 1.3** (`t2`): "The one-relator product on three non-trivial groups
  is non-trivial when the relator has length at most eight."
- **l.143, length:** relators are words "with free product length at least two", and
  pictures are taken over cyclically reduced words in the free product.
- **l.115–122, Theorem 1.2** (`t1`), recorded for context: for nontrivial cyclic
  `G_a, G_b, G_c` and `w` whose exponent sum in each generator is nonzero modulo that
  generator's order, each factor embeds in `(G_a * G_b * G_c)/N(w)`.

**How the proof goes** (§§4–5, read for the trust surface).
- **l.244:** the cyclic case "follows closely the one in [Howie8]": faithful
  representations of the three cyclic factors in `SO(3)` along axes `v ∈ S^2`, compared
  through classes in `H_2(S^3 \ {±1})`, with the exponent sums fixing the values at
  coaxial configurations (Lemma 4.1 and its proof, l.245–333).
- **l.369–427, Theorem 5.1** (`t33`), proved in full through trace coordinates on the
  `PSL_2(C)` character variety of `F_3`.
- **l.429–431, Theorem 5.3** (`t3`): "Let G be a one-relator product of non-trivial groups
  A and B, with relator r^n for some integer n. If 2 ≤ ℓ(r) ≤ 6 and n ≥ 2, then r has
  order n in G." l.433–435: "Theorem 5.3 is a consequence of various results proved in
  Chapter 4 of [ihe]. We omit the proof which is straightforward but lengthy. It uses
  standard curvature arguments on pictures." [ihe] is Chinyere's thesis, *Certain
  one-relator product of groups: Freiheitssatz and non-triviality*.
- **l.436–440:** a relator with one letter `α` from a factor reduces to
  `(B*C)/N(W^n)` amalgamated with `A` over `<α> = <W>`, using Theorem 5.3.
- **l.445–end:** the remaining words of length six to eight are handled by Bass–Serre
  ping-pong, Nielsen transformations and curvature on pictures.

**Trust surface.** Theorem 5.3 is used without a proof in the source.
