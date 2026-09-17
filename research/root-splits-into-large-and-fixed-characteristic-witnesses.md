---
rg: 2
id: root-splits-into-large-and-fixed-characteristic-witnesses
kind: claim
title: Some group is not weakly sofic iff some group has no rank models in large characteristic and some group is linear sofic in no positive characteristic
distinct_from:
  non-weakly-sofic-iff-non-finite-field-linear-sofic-group: that replaces the root by one group failing rank models over all finite fields at once; this splits that failure into a large-characteristic statement and a fixed-characteristic statement, allows two different groups, and proves that a group failing in large characteristic can be linear sofic in only finitely many characteristics.
  simple-group-psl-width-is-finite-field-linear-soficity: that is the width dichotomy for one finitely presented simple group, with fixed-characteristic embeddings mentioned as a variant; this sorts rank ultraproducts by characteristic for arbitrary countable groups and assembles witnesses by free products.
  non-linear-sofic-group: that is failure over one field; this needs failure over all large characteristics for one group and over every fixed prime for another.
---

**ESTABLISHED (2026-09-17, lane `sw-024`, unreviewed)** by `root-splits-into-large-and-fixed-characteristic-witnesses-proof`.

**Setting.** All groups are countable. The rank length on `GL_n(F)` is `rho(A, 1) = rank(A - 1)/n`.
- `L_p` (`p` prime) is the class of groups that embed in a rank ultraproduct `prod_omega GL_(n_i)(F_(q_i)) / N_omega`
  with every `q_i` a power of `p`. This is `F_p`-linear soficity.
- `L_inf` is the class of groups that embed in such an ultraproduct with `char F_(q_i) -> infinity` along `omega`.
- The **characteristic spectrum** of `G` is `S(G) = { p : G in L_p } union { inf : G in L_inf }`.

**Theorem.**
1. **Spectrum.**
   - `G` is linear sofic over finite fields iff `S(G)` is nonempty.
   - `S(G)` shrinks when passing to overgroups. So `S(G_1 * G_2 * ...)` is contained in the intersection of the
     `S(G_k)`.
   - Sofic groups have full spectrum.
2. **Uniform amplification.** In each class, models can be taken over the prime field with separation
   `rho(phi(g), 1) >= 1/4` for `g != 1`, with the same constant in every characteristic.
3. **Finiteness.** If `S(G)` contains infinitely many primes, then `inf` is in `S(G)`. Equivalently, a group that is
   not in `L_inf` is `F_p`-linear sofic for only finitely many primes `p`.
4. **Reduction (both directions).** `non-weakly-sofic-group-exists` holds iff both of the following hold:
   - (a) `non-large-characteristic-linear-sofic-group-exists`: some group `H` is not in `L_inf`;
   - (b) `group-not-linear-sofic-in-any-positive-characteristic-exists`: some group `G` is in no `L_p`.
5. **Economical form.** Fix any `H` not in `L_inf`. Then the root holds iff for each of the finitely many primes
   `p` in `S(H)` some group `G_p` is not `F_p`-linear sofic.
   - The witness is `W = H * G_(p_1) * ... * G_(p_k)`.
   - It can be taken two-generator simple.

**What this changes.**
- The root is a conjunction of two independent problems of different nature.
- Char-`p` stable-finiteness certificates are relevant to the root. If `F_p[G_p]` is not stably finite, then `G_p` is
  not in `L_p` (`linear-sofic-group-algebra-is-stably-finite`). Such a `G_p` supplies the `p`-component of every
  witness.
  - This corrects the reading on `non-finite-field-linear-sofic-group-exists` that the characteristic-two Kaplansky
    route "cannot produce a witness here". It cannot produce one alone, but it supplies the `p = 2` part.
- Component (a) is the metric part. By `c-linear-sofic-iff-bounded-dimension-large-characteristic`, it cannot be
  certified through Sylvester-rank or stable-finiteness arguments. For a group that is not complex-linear sofic, it
  is exactly a statement about unbounded-dimension wild models.

**Calibration.**
- Sofic groups have full spectrum (permutation matrices over every field), so neither component is witnessed by them.
- The finiteness in item 3 needs the uniform constant. Without it the separation could degrade as `p -> infinity`,
  and the diagonal argument fails at exactly that step.

**Credit.** The amplification in item 2 is in the spirit of Arzhantseva--Paunescu (Trans. AMS 369 (2017)); a
self-contained version with explicit constants is in the proof. The spectrum and the free-product assembly are
elementary. The novelty check was bounded, and experts may know the statement.
