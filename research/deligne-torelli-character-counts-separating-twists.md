---
rg: 2
id: deligne-torelli-character-counts-separating-twists
kind: claim
title: The Torelli character of Deligne's triple cover is a unit times the separating-twist exponent count mod 3, and hyperlinearity of the cover is one almost-scalar separating twist
distinct_from:
  deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2: that proves the quotient description for an unnamed invariant character c and an arbitrary finite normal generating list of the Torelli group; this evaluates c on the whole Torelli group and reduces the hyperlinearity dictionary to a single separating Dehn twist.
  genus-two-torelli-freely-generated-by-separating-twists: that imports Mess's free basis of separating twists; this uses it, together with the non-vanishing of Deligne's character, to compute the character.
  deligne-central-mark-hs-collapse: that is the one-word collapse for a presentation of the cover itself; this is the one-word Torelli-scalar condition on almost representations of Mod(S_2).
---

**ESTABLISHED** through `deligne-torelli-character-separating-twist-proof`. Unreviewed; no novelty claimed.

**Notation.** As in `deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2`:
- `M = Mod(S_2)`;
- `K = I(S_2)` is the Torelli group;
- `c : K -> Z/3` is the invariant character with `E_3 ~= (M x Z/3)/{(k, -c(k))}`;
- `omega = exp(2 pi i/3)`.

Let `s` be an essential separating simple closed curve in `S_2`, and `t_s` its Dehn twist.

**Statement.**

1. **(ST1) One conjugacy class.** Dehn twists about essential separating curves in `S_2` form a single
   conjugacy class of `M`. It lies in `K`, and `K` is its normal closure in `M`.
2. **(ST2) The character.** `epsilon := c(t_s)` is a unit of `Z/3`, independent of `s`. Every
   `k in K` can be written `k = prod_j g_j t_s^(e_j) g_j^(-1)`, and then
   ```text
   c(k) = epsilon * (sum_j e_j)   mod 3.
   ```
   On Mess's free basis of separating twists `T_x`, this reads
   `c(prod_i T_(x_i)^(f_i)) = epsilon * sum_i f_i mod 3`. In particular `c` is surjective, and `ker c` is
   the subgroup of words whose separating-twist exponent sum is divisible by 3.
3. **(ST3) One-relator presentation.** `E_3 ~= < M, z | z^3, [z, M], t_s z^(-epsilon) >`.
4. **(ST4) One-word hyperlinearity dictionary.** Fix a finite presentation `<S | R>` of `M` and a word for
   `t_s` in `S`. Then `E_3` is hyperlinear iff there are a primitive cube root of unity `zeta` and unitary
   tuples `rho_n : S -> U(d_n)` with
   ```text
   max_(r in R) ||rho_n(r) - I||_(2,d_n) -> 0   and   ||rho_n(t_s) - zeta I||_(2,d_n) -> 0.
   ```
5. **(ST5) Finite-dimensional invisibility.** No finite-dimensional unitary representation of `M` sends a
   separating twist to `omega I` or to `omega^2 I`.

**Reading.**
- The non-hyperlinearity question for Deligne's triple cover, equivalent to the Maslov mod-three
  sector gap by `deligne-sector-gap-is-exactly-nonhyperlinearity`, is exactly this: in vanishing-defect
  almost representations of `Mod(S_2)`, can one separating Dehn twist be almost a primitive cube-root
  scalar?
- (ST5) says it can never be exactly scalar in finite dimensions. A non-hyperlinearity proof must bound
  `||rho(t_s) - zeta I||_2` below uniformly in the dimension, among almost representations with vanishing
  defect.

**What is not claimed.**
- The value of `epsilon` is not determined. For hyperlinearity only `epsilon != 0` matters.
- No identification with Meyer's function is landed here; see the artifact of the proof route for the
  unpinned consistency check.
