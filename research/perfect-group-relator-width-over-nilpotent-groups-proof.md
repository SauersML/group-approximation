---
rg: 2
id: perfect-group-relator-width-over-nilpotent-groups-proof
kind: route
title: Match degree one by exponent sums, then correct each lower central layer through one fixed pair of conjugates per relator
target: perfect-group-relator-width-over-nilpotent-groups
requires: []
---

Notation: `[a, b] = a b a^-1 b^-1`, `gamma_1 = F`, `gamma_(j+1) = [F, gamma_j]`, and
`L_j = gamma_j / gamma_(j+1)`.

**Standard inputs (Magnus--Witt).**
- `L_j` is the degree-`j` component of the free Lie ring on `X`.
- The commutator map `gamma_i x gamma_j -> gamma_(i+j)` induces the Lie bracket `L_i x L_j -> L_(i+j)`.
- The free Lie ring is generated in degree one, so `L_j = [L_1, L_(j-1)]` for `j >= 2`.
- `gamma_j / gamma_(j+1)` is central in `F / gamma_(j+1)`.

**Template.** Fix the word pattern

```text
T = ( r^(sgn n_r) repeated |n_r| times, for each r in R )  followed by  ( r, r^-1 for each r in R ),
```

and write `P(c)` for the product of the conjugates `c_i t_i c_i^-1` of its letters `t_i`, with
conjugators `c = (c_i)` in `F`. It has `K(x)` letters.

**Base, modulo `gamma_2`.** With all `c_i = 1`, `P ≡ prod_r r^(n_r)`. Its exponent vector is
`sum_r n_r e_r = e_x`, so `P ≡ x` modulo `gamma_2`.

**Step, from `gamma_j` to `gamma_(j+1)`, `j >= 2`.** Suppose `P(c) ≡ x` modulo `gamma_j`.
- **The defect.** Let `u in L_j` be the image of `x^-1 P(c)`.
- **Solve in the Lie ring.** `L_1 = span_Z {e_r}` and `L_j = [L_1, L_(j-1)]`. So by bilinearity
  `-u = sum_r [e_r, W_r]` for some `W_r in L_(j-1)`. Pick `d_r in gamma_(j-1)` with image `W_r`.
- **Modify one conjugator per relator.** In the pair `r, r^-1` for `r`, replace the conjugator
  `c''` of `r^-1` by `c'' d_r`:
  ```text
  c'' d_r r^-1 d_r^-1 c''^-1 = ( c'' r^-1 c''^-1 ) · c'' [r, d_r] c''^-1 .
  ```
  - `[r, d_r]` lies in `gamma_j`, with image `[e_r, W_r]` in `L_j`.
  - Conjugation by `c''` does not change that image.
  - `gamma_j` is central modulo `gamma_(j+1)`, so the inserted factor can be moved to the end.
- **Result.** The new product satisfies `P' ≡ P · prod_r [e_r, W_r] ≡ x u (-u) = x` modulo
  `gamma_(j+1)`, and still `P' ≡ P` modulo `gamma_j`.

**Induction.** For each `k`, after `k - 1` steps, `x ≡ P(c^(k))` modulo `gamma_(k+1)`, with the pattern
`T` unchanged and `K(x)` letters.

**Item 1.** A tuple `a` in a nilpotent group `Q` of class `<= k` defines a homomorphism `F -> Q` that
kills `gamma_(k+1)`. Apply it to the identity above. The conjugators map into `<a> <= Q`.

**Item 2.** Bi-invariance and the triangle inequality.

**Item 3.** Let `G` be a nontrivial finitely generated perfect group, let `g != 1` be a word of length
`|g|`, and suppose weak models `a` in nilpotent groups with relator lengths `<= eps` and
`l(g(a)) >= 1`. Item 2 gives `l(a_x) <= K eps` for every generator, so
`l(g(a)) <= |g| K eps`. That is a contradiction for `eps < 1/(|g| K)`, where
`K = max_x K(x)` over the generators. Small multiplicative defect on a finite set containing the
prefixes of the finitely many relators in `R` bounds their lengths by a constant times the defect.
Weak soficity passes to subgroups, so any group containing such a `G` fails as well.
