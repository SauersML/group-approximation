---
rg: 2
id: jacobson-mirror-head-swap-kills-ambient-approximations
kind: claim
title: Class-kill for the Jacobson mirror quotient - every approximation of EL_n(J) inherited from a group in which the mirror head is conjugate to the head, including H_bi and all periodic finite models, kills the head
distinct_from:
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that writes EL_n(J) = P/L_- with P inside the LEF group H_bi and notes (MQ5) that no finite normalized kernel exists and that L_- acts faithfully in the periodic models; this shows that no approximation of any overgroup of P containing one finitary wall swap, in particular of H_bi or of any representation of its periodic finite models, can be trivial on L_- and separate the head, so the LEF ambient of (MQ) is unusable in every form, not only through its standard models.
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that audits one-sided finite sections and finds equal boundary and head errors; this concerns bilateral and periodic models without boundary, where the obstruction is conjugacy of the two heads rather than a boundary error.
  fell-models-inherit-walls-from-coefficients: that shows tensoring with the regular representation creates no new walls; this shows that a successful approximation of P must itself carry a wall at the V_+/V_- splitting, since every model that is asymptotically invariant under one swap across it fails.
  carderi-thom-almost-invariant-psd-on-sl-n-is-near-trivial: that is quantitative rigidity for positive definite functions on SL_n(F_q) near one conjugacy class, vacuous at q = 2; this uses only exact conjugacy of two transvections and works over F_2.
---

**ESTABLISHED** (route `jacobson-mirror-head-swap-kill-proof`).

**Notation** (as in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`).
- `W = F_2^(Z x {1..n})`, `V_+ = span{e_(k,i) : k >= 0}`, `V_- = span{e_(k,i) : k < 0}`, `n >= 3`.
- `P = E_+ x_(SL_n(A)) E_-` acts on `W = V_+ (+) V_-`, `P <= H_bi = GL_fin(W) x| EL_n(A)`.
- `pi : P -> E_+ = EL_n(J)` is the projection, with kernel `L_- = GL_fin(V_-)`.
- The head is `w = (x_13(Q), 1) = 1 + e_(0,1) (x) e*_(0,3)` (a transvection of `V_+`).
- The mirror head is `w' = (1, x_13(Q)) = 1 + e_(-1,1) (x) e*_(-1,3)`, in `L_-`, since mirror index 0 is `e'_0 = e_(-1)`.
- `s in GL_fin(W) <= H_bi` is the finitary involution that swaps `e_(0,i)` and `e_(-1,i)` for `i = 1..n` and fixes every other basis vector. So `s w' s = w`.

**(HS) Swap kill.** Let `K` be any group with `P <= K` that contains an element `s` with `s w' s^(-1) = w`. `K = H_bi` qualifies. Let `gamma : K -> U(d)` be any map with `gamma(1) = 1` that is `eps`-multiplicative on the pairs `(s, w' s^(-1))`, `(w', s^(-1))` and `(s, s^(-1))` in the normalized Hilbert-Schmidt norm. Then

```text
|| gamma(w) - 1 ||_2  <=  || gamma(w') - 1 ||_2 + 3 eps.        (HS)
```

**Consequences.**
1. **Ambient approximations kill the head.** Let `alpha_k : E_+ -> U(d_k)` be a hyperlinear approximation of `EL_n(J)`, and let `gamma_k` be asymptotic homomorphisms of such a `K`. Then `||alpha_k(pi(p)) - gamma_k(p)||_2 -> 0` fails for `p in {w, w'}`. Indeed `alpha_k(pi w') = alpha_k(1) = 1`, while `||alpha_k(pi w) - 1||_2 -> sqrt 2`.
   - Permutation (sofic) approximations are included, via `Sym(d) <= U(d)`.
   - Linear-sofic and rank approximations are included through the same unitary-invariance argument with the rank metric.
2. **Periodic finite models.** For the periodic local embeddings `iota_m : H_bi -> GL_(N_m)(F_2)` of `untwisted-bilateral-symbol-enrichment-is-lef`, `iota_m(w)` and `iota_m(w')` are transvections, hence conjugate. So every character, positive definite class function or representation `psi` of `GL_(N_m)(F_2)` has `tr psi(iota_m w) = tr psi(iota_m w')`. No model of the form `psi_m o iota_m | P` is trivial on `L_-` and separates the head.
3. **Normal closure form.** The normal closure of `L_-` in `H_bi` is `GL_fin(W)`, which contains `L_+`. So a model asymptotically invariant under `H_bi` kills `L_- x L_+` and factors, up to `o(1)`, through the symbol group `P/(L_+ x L_-) = SL_n(A)` (MQ1). That group is finitely generated and linear, so it is residually finite (Malcev), and it carries no information about the head.

**Impact.**
- The equivalence recorded on `agent-leavitt-not-bcs-negative-root-corner` makes the Toeplitz survivor class dead iff `EL_20(J)` is hyperlinear. A kill of that class would therefore have to come from approximations of `P`.
- (HS) shows those approximations must be **wall-rigid**: not asymptotically invariant under the single finitary swap `s` across the `V_+/V_-` wall.
- Every approximation of `P` currently in the graph is inherited from `H_bi`. That covers the periodic models and every representation of their finite groups, and all of these are killed.
- So a proof that `EL_20(J)` is hyperlinear must build approximations of `P` that see the wall. A general "LEF modulo locally finite" permanence theorem (Kourovka 21.118 analogue) cannot go through an ambient group where the kernel's normal closure grows.
- The negative direction is unaffected. `non-hyperlinear-group` stays OPEN.

DERIVATION
jacobson-mirror-head-swap-kill-proof
