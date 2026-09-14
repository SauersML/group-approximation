# HNN extensions fold into free coset wreath products

Date: 2026-09-11. Written proof, not a Lean certificate.

## 1. Statement

Let `B` be a group, `phi: C -> C'` an isomorphism between subgroups of `B`, and

    G = < B, t | t^(-1) c t = phi(c)  (c in C) >.

Let `rho: G -> H` be any homomorphism. Put `X = H/rho(C)`, `o = rho(C)`, let
`F_X` be free on `{z_x : x in X}`, and form

    W = F_X rtimes H,       h z_x h^(-1) = z_(h x).

**Theorem A.** The formulas `Phi(b) = rho(b)` and `Phi(t) = z_o rho(t)` define a
homomorphism `Phi: G -> W` with `pi o Phi = rho`, where `pi: W -> H` is the
quotient map. If `rho` is injective on `B`, then `Phi` is injective.

**Theorem B (local form).** Let `E` be a finite subset of `G`. Fix reduced forms
(Britton) of the elements of `E^(-1)E \ {1}`. Suppose that for every inner
syllable `b` of these forms:
* `rho(b)` is not in `rho(C')` when `b` sits between `t` and `t^(-1)`;
* `rho(b)` is not in `rho(C)` when `b` sits between `t^(-1)` and `t`.

Suppose also that `rho(b) != 1` whenever one of these elements is a single
syllable `b` of `B`. Then `Phi` is injective on `E`.

**Corollary C.** `G` is sofic if for every finite `E` some `rho: G -> H`
satisfies Theorem B, `H` is sofic, and `H action H/rho(C)` is a sofic action.
Indeed `W` is then sofic by Gao--Kunnawalkam Elayavalli--Patchell,
arXiv:2401.04945, Theorem 3.7 (free case). A group admitting, for every finite
set, a homomorphism to a sofic group injective on that set is sofic.

## 2. Proof

**Homomorphism.** For `c in C`, `rho(c)` fixes `o`, so `rho(c) z_o rho(c)^(-1) = z_o`.
Hence

    Phi(t)^(-1) Phi(c) Phi(t) = rho(t)^(-1) z_o^(-1) rho(c) z_o rho(t)
                              = rho(t)^(-1) rho(c) rho(t) = rho(phi(c)).

Composing with `pi` kills every `z_x`, so `pi o Phi = rho`.

**Normal form of the image.** Let `g = b_0 t^(e_1) b_1 ... t^(e_k) b_k` with
`e_i = +-1`, and let `P_i = rho(b_0 t^(e_1) ... b_(i-1))`. Moving each `z` letter
to the left with `h z_x = z_(h x) h` gives

    Phi(g) = z_(x_1)^(e_1) ... z_(x_k)^(e_k) rho(g),
    x_i = P_i o                  if e_i = +1,
    x_i = P_i rho(t)^(-1) o      if e_i = -1.

(Induction on `i`: `P z_o rho(t) = z_(P o) P rho(t)`, and
`P rho(t)^(-1) z_o^(-1) = z_(P rho(t)^(-1) o)^(-1) P rho(t)^(-1)`.)

**No cancellation.** Adjacent letters `i, i+1` can cancel only if
`e_(i+1) = -e_i` and `x_(i+1) = x_i`.
* `e_i = +1, e_(i+1) = -1`: `x_(i+1) = P_i rho(t) rho(b_i) rho(t)^(-1) o`, so
  equality means `rho(b_i) in rho(t)^(-1) rho(C) rho(t) = rho(C')`.
* `e_i = -1, e_(i+1) = +1`: `x_(i+1) = P_i rho(t)^(-1) rho(b_i) o`, so equality
  means `rho(b_i) in rho(C)`.

If the form is reduced, then `b_i` is not in `C'` in the first case and not in
`C` in the second. When `rho` is injective on `B` this forbids both equalities,
and under Theorem B's hypotheses they are forbidden directly. So the `z` word is
freely reduced of length `k`.

**Injectivity.** If `Phi(g) = 1`, then `rho(g) = 1` and the reduced `z` word is
empty, so `k = 0` and `g = b_0` with `rho(b_0) = 1`. That forces `g = 1` in
Theorem A, and contradicts the hypothesis on single syllables in Theorem B. So
`Phi(g) != Phi(g')` for distinct `g, g'` in `E`. ∎
