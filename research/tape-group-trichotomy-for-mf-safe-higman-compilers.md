---
rg: 2
id: tape-group-trichotomy-for-mf-safe-higman-compilers
kind: claim
title: Abelian, metabelian and free tapes each defeat one layer of an MF-safe Higman compiler
distinct_from:
  c-free-aanderaa-rope-is-mf-with-fine-quotients: that isolates the digit-reading edge of the modular-machine compiler; this compares the three natural tape encodings and shows the obstruction moves but never disappears under finite-quotient methods.
---

ESTABLISHED (as an audit of the three encodings; each clause is proved in
the body).  A Higman compiler has three layers: machine steps, reading of
the input word into the machine, and transfer of the machine's verdict to a
free word component that is then evaluated in the target group `C`.
Finite-quotient permanence (synchronized HNN, twisted edges) can close a
layer only if the relevant edge is compatible with finite quotients.

1. **Abelian tape** (modular machines, `Z^2`): machine steps are inner in the
   enlarged base `< t > * (BS(1,m) x BS(1,m))` and the engine is MF
   ([[modular-machine-boone-group-is-mf]]); but reading is by Gödel
   numbers, so in every finite quotient `t_alpha = t_(alpha + N)` while
   `w_alpha(b) != w_(alpha+N)(b)`: the reading edge is not residual.

2. **Metabelian tape** (`W = Z_m wr Z` inside Baumslag's finitely presented
   metabelian group `< a, u, tau | a^m, [a, a^tau], [u, tau], a^u = a a^tau
   >`, head-centered coordinates, one state counter `s` commuting with `W`,
   `[t, tau] = 1`): the base `B = (W~ x <s>) *_<tau> (<tau> x <t>)` is a
   residually finite amalgam over a closed cyclic subgroup, every machine
   step is the restriction of `Ad(tau^-1 . (-(b-a)e_0) . s^(q-q'))` to the
   domain subgroup `< t(a e_0, q), W_0 >` with `W_0 = (+)_(j != 0) Z_m`, and
   the input word is read by the homomorphism `rho : F(A) -> W`, `c_k -> (k
   e_0) tau^-1`, so that `t(input w) = rho(w)^-1 t_0 rho(w)`: the reading
   edge is compatible with the finite quotients of `W` (they induce
   finite-index subgroups `ker(q o rho)` of `F(A)`).  But the transfer edge
   identifies elements of `rho(F(A)) ~= F(A)/ker(rho)` with free words, and
   any HNN letter doing so imposes the laws of `ker(rho) >= F(A)''` on the
   target: the target `C` would have to be metabelian.  More generally the
   twisted-edge condition on the insertion edge would only see the
   quotients of `C` that factor through `rho(F(A))`.

3. **Free tape** (Boone--Britton Turing encodings with free alphabet
   letters): reading and transfer are homomorphic and the word component is
   free, but the domain of a machine step ("the head reads `a`") is not a
   coset of a subgroup of a free group, so the steps are realized through
   the `BS(1,2)` twist on `x` and the state transvections; the base `(*_<x>
   BS(1,2)) * F(Q)` is not residually finite and the instruction edge is a
   basis-to-basis free edge whose corona conjugacy is
   [[boone-base-has-corona-inner-instruction-automorphisms]].

Consequently no compiler built from these encodings can be certified MF by
finite-quotient permanence alone; some layer requires a genuinely
approximate (non-residual) MF permanence theorem for a basis-to-basis edge
between free subgroups.  The candidate smallest instances are the
machine-free group `Gamma^K` of
[[c-free-aanderaa-rope-is-mf-with-fine-quotients]] and the Turing base edge.

## Proofs of the clauses

*(2), inner steps.*  With `t(f, q) = (f s^q)^-1 t (f s^q)` for a tape
function `f in (+)_Z Z_m` (head at `0`) and state `q`, the three
elementary operations are `f -> tau^-1 f tau` (shift, `Ad(tau^-1)` since
`[tau, t] = 1`), `f -> f + c e_0` (write, `Ad((c e_0)^-1)` since `s`
commutes with `W`), and `q -> q'` (`Ad(s^(q-q'))`).  The set of
configurations with head symbol `a` and state `q` is the `W_0`-conjugacy
class of `t(a e_0, q)`, so the domain subgroup is `< t(a e_0, q), W_0 >` and
the step is the restriction of one inner automorphism, whose effect on `W_0`
is the shift onto `(+)_(j != -1) Z_m`.  Simpson's goodness argument uses
only that `T = << t >>` is free on conjugates by coset representatives of
`C(t) cap (W~ x <s>) = < tau >`, which holds in the amalgam.

*(2), reading.*  `rho(c_(k_0) ... c_(k_r)) = (sum_j k_j e_j) tau^(-(r+1))`,
so the tape holding the word with the head just past it is `rho(w)` up to
the state letter, and `t(input w) = s^(-q_0) rho(w)^-1 t rho(w) s^(q_0)`.

*(2), transfer obstruction.*  If a stable letter `y` satisfies `y^-1 rho(c_k)
y = rho(c_k) b_k` with the `b_k` commuting with `rho(F(A))`, then for `u in
ker(rho)`, `1 = y^-1 rho(u) y = rho(u) u(b) = u(b)`, so `u(b) = 1`; the
word component satisfies the laws of `rho(F(A))`, and after evaluation so
does `C`.  Since `W` is metabelian, `ker(rho) >= F(A)''`.

*(1), (3).*  [[c-free-aanderaa-rope-is-mf-with-fine-quotients]] and
[[boone-base-semidirect-product-is-hnn-over-free-subgroups]].
