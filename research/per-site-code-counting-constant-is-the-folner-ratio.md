---
rg: 2
id: per-site-code-counting-constant-is-the-folner-ratio
kind: claim
title: Uniform per-site entropy bounds certify a Bernoulli window code only up to the Følner ratio of its codeword set, and Hall reader fields attain its integer part
distinct_from:
  bernoulli-window-codeword-folner-ratio-bound: that proves k log q <= lambda(F) H(psi) + H(x(1) | y_F) for equivariant configurations; this shows the factor lambda(F) is not an artifact of that proof, since among arguments that see only per-site costs it is optimal up to integer part.
  nonamenable-groups-carry-arrow-shift-strict-automata: that builds strict same-alphabet automata over a doubling arrow shift; this builds injective codes over m-fold reader fields that divide the output site entropy by m, and reads off a barrier for entropy lower-bound proofs.
  bernoulli-witness-information-is-bounded-by-code-reads: that bounds Phi below by log q / m through the read degree of equivariant codes; this bounds what any argument from per-site costs alone can certify, over all site-indexed code families.
  transport-identity-gives-reciprocal-memory-entropy-bound: that shows per-term transport bounds reproduce subadditivity for one automaton; this shows per-site subadditive counting has a provable, attained loss factor on every nonamenable group.
---

**ESTABLISHED (unreviewed)** by `per-site-code-counting-constant-is-the-folner-ratio-proof`.

**Setting.** Let `G` be a countable group, `F <= G` finite and nonempty, and
`lambda(F) = inf_(S finite nonempty) |S F| / |S|`. A **site-code family** with codeword set `F` consists of
- `q >= 2` and `k >= 1`, with `|A| = q`;
- a finite window `E <= G` and a finite output alphabet `B`;
- for each `g in G` a map `psi_g : (A^k)^E -> B`, with no relation between different `g`.

With `x` iid uniform on `(A^k)^G`, put `y_g = psi_g((x(g e))_(e in E))`. The **per-site costs** are

    c = sup_g H(y_g),        d = sup_t H( x(t) | y_(tF) ).

An equivariant configuration `(k, E, F, psi)` is the case `psi_g = psi`, with `c = H(psi(x|_E))` and
`d = H(x(1) | y_F)`. The **per-site constant** is `kappa(F) = sup k log q / (c + d)` over all site-code families
with codeword set `F`.

For an integer `m >= 1`, an **m-fold reader field** for `F` is a map `rho : G -> ([m] x F^(-1)) ∪ {*}` such that for
every `h in G` and `i in [m]` exactly one `g` has `rho(g) = (i, g^(-1) h)`. Such a `g` lies in `hF`. Write `Y_(F,m)`
for the set of these fields. It is a `G`-invariant shift of finite type.

**Theorem.**
1. **Følner count for site-code families.** Every site-code family satisfies `k log q <= lambda(F) c + d`. Hence
   `kappa(F) <= lambda(F)`.
2. **Reader fields.** `Y_(F,m)` is nonempty iff `lambda(F) >= m`.
3. **Hall families attain the integer part.** Suppose `rho in Y_(F,m)`, `n >= 1` and `k = mn`. Then there is a
   site-code family with `E = F^(-1)` and `B = A^n ∪ {*}`, where `psi_g` is determined by `rho(g)`, so at most
   `m|F| + 1` distinct rules occur. Moreover `y` determines `x`, `d = 0` and `c <= n log q + log(1 + q^(-n))`. So
   `floor(lambda(F)) <= kappa(F) <= lambda(F)`.
4. **Group dichotomy.** `kappa(F) = 1` for every `F` iff `G` is amenable. If `G` is nonamenable, the arrow window `S`
   of `nonamenable-groups-carry-arrow-shift-strict-automata` has `Y_(S^r, 2^r)` nonempty. So `kappa(S^r) >= 2^r`
   without the Hall import.
5. **Gate: no invariant reader field.** For `m >= 2`, `Y_(F,m)` carries no `G`-invariant Borel probability measure.
   An invariant random reader field would have expected in-degree `m` at the identity. The mass transport sum equals
   `P(rho(e) != *) <= 1`.

**What this kills.** It kills every argument that certifies a lower bound on the code entropy of a Bernoulli
window configuration from the per-site costs `(c, d)` alone. That includes:
- decoding a finite `S <= G` from `y_(SF)`;
- subadditivity over any finite index set in `G`;
- per-term transport bounds;
- the four-step count `decoding + subadditivity + translation + finite index set` of Section 7 of
  `research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md`.

The Hall families satisfy every hypothesis such an argument uses, including exact decoding, bounded windows and
finitely many local rules. Their costs are `(k log q / m + o(1), 0)`.

**The invariant.** `lambda(F)`, equivalently the largest `m` with `Y_(F,m)` nonempty.

**The step where every member dies.** Subadditivity `H(y_(SF)) <= |SF| c`. On a Hall family `H(y_(SF)) >= |S| k log q`
while `|SF| >= m|S|`. The loss factor is attained, so no choice of index set inside `G` removes it.

**Consequences.**
- Every deficit witness can be enlarged to one with `lambda(F) >= 2^j` for any `j`. Enlarging `F` only lowers `Phi`,
  `lambda` is monotone under inclusion, and `lambda(F^j) >= lambda(F)^j`.
- So on the configurations relevant to `rokhlin-window-transport-is-dominated`, no per-site argument yields
  domination with constant `1`, or with any uniform constant `C`. It therefore cannot yield INF through Corollary 2
  of that artifact, on any nonamenable group. This includes all nonsofic hosts: the binary Leavitt units, Thompson's
  `V` and the fixed tester host.
- A proof must use a property that fails over `Y_(F,m)`. By item 5 the natural candidate is translation invariance of
  the joint law of `(x, y)`, used through a transport identity. The random-order transport identity is such a tool,
  and invariant random orders and ergodic averages are others.
- Automaton counterpart. Over `Y_(F,m)` the Hall family is an injective block code from `(A^k)^G` into
  `(A^(k/m) ∪ {*})^G`, with output site entropy about `(1/m)` of the input. So the single-site entropy normal form
  `injective-ca-images-have-full-single-site-entropy` fails relative to a base of finite type without invariant
  measure. Its per-site proofs die in the same way.

**Scope.** This is a barrier about proof methods, not a statement about Rokhlin entropy. It does not say that any
equivariant configuration has a deficit. The equivariant question is exactly the one left after removing the Hall
families by the gate in item 5.
