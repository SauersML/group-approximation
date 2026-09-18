---
rg: 2
id: resolvent-vacuum-rings-have-no-k0-state
kind: claim
title: A resolvent vacuum forces infinitely many orthogonal copies of the vacuum idempotent, so a simple host with one is not stably finite and has no state on K_0
distinct_from:
  leavitt-tuples-make-rational-scalar-powers-elementary: that shows a Leavitt (1,d)-tuple makes rational scalar powers elementary; this shows that the resolvent mechanism itself, with or without a Leavitt tuple, rules out every stably finite or traced host.
  bounded-harmonic-rings-are-not-finitely-presented: that refutes finite presentation for rings getting Q from bounded harmonic functions over odometers; this concerns rings getting Q from a number operator with a vacuum, and constrains their K_0.
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: that is one ring with the mechanism, R_L; this is a structural consequence shared by R_L, R_Toep, R_k and every future host of this type.
artifacts:
  - research/artifacts/gq-referee-a-resolvent-vacuum-rings-have-no-k0-state.md
  - research/artifacts/gq-referee-b-resolvent-vacuum-rings-have-no-k0-state.md
---

**ESTABLISHED** through `resolvent-vacuum-rings-have-no-k0-state-proof` (lane proof,
elementary; refereed PASS by `gq-referee-a`, proof gaps, `gq-referee-a-resolvent-vacuum-rings-have-no-k0-state.md`, 061bc8d2d, and by `gq-referee-b`, citations and hypotheses,
`gq-referee-b-resolvent-vacuum-rings-have-no-k0-state.md`, 9a2dd39e7).

**Setting (a resolvent vacuum).** A unital ring `R` has a *resolvent vacuum* if it contains
a nonzero idempotent `E`, an element `N`, and, for infinitely many indices `m`, elements
`x_m ∈ R E` and `y_m ∈ E R` with:
- `y_m x_m = E`;
- `N x_m = λ_m x_m` and `y_m N = λ_m y_m`, for integers `λ_m`;
- `λ_m − λ_(m')` a non-zero-divisor in `R` for `m ≠ m'`. This holds whenever `Q ⊆ R` and
  the `λ_m` are distinct.

**Instances.** Each ring below has a resolvent vacuum, with the stated `E`, `x_m`, `y_m`
and `λ_m = m − 1`:
- `R_L` (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`): `E = 1`,
  `x_m = s_1^(m−1) s_2`, `y_m = t_2 t_1^(m−1)`;
- `R_Toep`, the Toeplitz resolvent ring of `q-embeds-in-a-corner-of-a-fp-toeplitz-ring`, in
  its concrete model, which is a `Q`-algebra. It is not the SL_3 Toeplitz harmonic ring
  `R_T` on main, which is tracial and gets `Q` by harmonic elimination, not from a vacuum: `E = 1 − ST`, `x_m = S^(m−1) E`, `y_m = E T^(m−1)`. Here `E` is not full;
  it generates the finitary ideal;
- `R_k` (`rational-function-fields-embed-in-fp-simple-rings`): `E = 1`, with the words
  `n^(m−1) v` in place of `1^(m−1) 2`.

These are exactly the elements through which the resolvent produces `1/m`.

**Statement.**
1. **Orthogonal copies.** The idempotents `P_m = x_m y_m` are pairwise orthogonal, and each
   is equivalent to `E`. Hence `M·[E] <= [1]` in the monoid `V(R)` of idempotent classes,
   for every `M >= 1`.
2. **Full vacuum.** If `E` is full, that is `R E R = R`, and in particular whenever `R` is
   simple, then:
   - (a) `R` is not stably finite: some matrix ring `M_k(R)` is not directly finite;
   - (b) `(K_0(R), V(R), [1])` has no state. There is no additive `f : K_0(R) -> R` with
     `f >= 0` on `V(R)` and `f([1]) = 1`. In particular `R` carries no trace or dimension
     function normalized at `1` that is nonnegative on the idempotents of all matrix
     rings `M_k(R)`. Positivity on those idempotents is what makes it a state.

**Consequences for the design of a group host.**
- **No stably finite model.** A finitely presented simple ring that gets `Q` from a
  resolvent vacuum cannot be stably finite, UHF-like or traced. This excludes the
  suggested stably finite Bratteli or groupoid models with a number operator. It also
  excludes minimal Cantor crossed products with an invariant measure that carry such a
  mechanism, and anything with a faithful dimension function.
- **What the targets become.** "No Leavitt tuple" and "`[1]` of infinite order in `K_0`"
  are compatible with this, since `[1]` of infinite order already excludes any Leavitt
  `(1,d)`-tuple, which would force `(d−1)[1] = 0`. But the host must be stateless. Heuristically it is of the
  type `O_∞ ⊗ UHF_Q`: purely infinite behaviour, with `K_0 ⊇ Q·[1]`.
- **What remains open.** This is recorded in
  `fp-simple-resolvent-ring-with-divisible-unit-class`.
