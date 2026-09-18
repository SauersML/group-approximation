---
rg: 2
id: rips-segev-cores-have-no-infinite-cyclic-quotient
kind: claim
title: Rips--Segev cores have finite abelianization, so no grading or locally indicable quotient can prove the witness elements on {1,a,b,ab} regular, although any unique-product quotient would
distinct_from:
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this kills one family of approaches (gradings and abelian or locally indicable quotients) and isolates the surviving one (a perfect-abelianization unique-product quotient).
  rips-segev-core-large-gap-two-layer-elements-are-regular: that uses positive relations to prove regularity for large degree gaps; this uses the same positive relations, with both exponent signs, to show that K has no rational character.
  rips-segev-port-data-cannot-exclude-balanced-divisors: that kills arguments from port data; this kills arguments from quotient gradings, which are a different mechanism.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-cores-have-no-infinite-cyclic-quotient-proof`.

**Setting.**  `Gamma` is a generalized Rips--Segev graph whose labelling satisfies `Gr'_*(1/8)`, and
`K = (<a> * <b>)/<<R>>` is its core group.  A *positive relation* is `b a^{n_1} ... b a^{n_L} = 1` in `K`, `L >= 1`.

**Theorem.**
1. **Fiber criterion.**  Let `G` be any group with `a, b in G` such that `a, b, ab, a^{-1}b, b^{-1}ab` have infinite
   order.  If `<a, b>` has a nontrivial homomorphism to a group with the unique product property, then every
   nonzero element of `k[G]` supported on `{1, a, b, ab}` is a non-zero-divisor, for every field `k` and every
   coefficient pattern (balanced or not, rank one or two).  The hypotheses on orders hold in `K` and in every
   generalized Rips--Segev group `G(Gamma)`.
2. **No rational character.**  If `K` has two positive relations with different exponent means `(1/L) sum n_k`,
   then `Hom(K, Q) = 0`.  This holds:
   - whenever every line endpoint position `0, C_i` is both a source and a target of `b`-edges, because the walk
     lemma applied to `Gamma`'s own port configuration gives one relation with all `n_k >= 0` and one with all
     `n_k <= 0`, and `b^L != 1`;
   - for Steenbock's explicit families directly: their `x_2`-cycles give relations with all exponents `>= 99900`,
     their `x_1`-cycles relations with all exponents `<= -10`.
3. **Consequences.**  `H_1(K; Z)` is finite.  `K` has no nontrivial homomorphism to `Z`, to a torsion-free abelian
   group, to a locally indicable group or to a bi-orderable group.  Every homomorphism from a generalized
   Rips--Segev group `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2` to a torsion-free abelian group kills `a` and `b`.

**Calibration.**
- For `Gamma` with no cycles, `K = F_2` has no positive relations and `Hom(F_2, Q) = Q^2`; the fiber criterion then
  reproduces regularity on `{1,a,b,ab}` in `k[F_2]`.
- `Z = <a, b | b a^{-1}>` has one positive relation and a nonzero character, so two different means are needed.
- In `Z x Z/2`, `1 + b` is a zero divisor; the criterion excludes it because `b` has finite order.

**Class killed.**  Proving that the witness elements `c_0 + c_1 a + c_2 b + c_3 ab` are regular in `k[K]` by grading
along a character, or through an abelian, locally indicable or bi-orderable quotient.  This also kills reducing the
Kaplansky problem for `K` to the kernel of a map `K -> Z`.
- **Exact failing step:** there is no nonzero `phi : K -> Q`.  The relation `L phi(b) + phi(a) sum n_k = 0`, applied
  to two positive relations of opposite exponent sign, forces `phi = 0`.
- **Surviving form:** a nontrivial unique-product quotient of `K` whose abelianization is finite.  Torsion-free
  hyperbolic quotients with Delzant's large-translation-length condition would qualify.  None is known.
