---
rg: 2
id: fn-cantor-action-with-covariant-stateless-certificate
kind: claim
title: Some action of a finite-rank free group on the Cantor space has minimal finite-index kernels along a separating chain, no invariant measure, and a transfer-compatible monoid-valued certificate against 2u <= u
distinct_from:
  free-minimal-fn-cantor-action-not-almost-unperforated: that asks for a free action directly; this asks for a possibly non-free action with a covariant certificate, which gives a free one by profinite diagonal extension.
  free-minimal-cantor-action-with-finite-clopen-type: that allows any countable group and asks for a finite clopen class; this asks for a finite-rank free group, minimal kernels and a transfer-compatible certificate.
  topologically-free-minimal-cantor-action-with-finite-clopen-type: that is topologically free with a finite class; this needs every kernel of a separating chain to stay minimal and a certificate that is not invariant under the whole group.
  profinite-diagonal-cantor-type-is-transfer-limit: that is the general extension theorem and its firewall; this is the input action and certificate the extension needs, which that theorem does not supply.
---

**Statement (OPEN).**  For some `n` with `2 <= n < infinity` there are:
* an action of `F_n` on a Cantor space `X`;
* normal subgroups `F_n = N_0 ⊇ N_1 ⊇ ...` of finite index with trivial
  intersection;
* a commutative monoid `M` and finitely additive `N_j`-invariant maps
  `mu_j : Clopen(X) -> M` (additive on disjoint unions, `mu_j(∅) = 0`) with `mu_j = sum_(t in N_j/N_(j+1)) t_* mu_(j+1)`,
  where `(t_* mu)(A) = mu(t^(-1) A)`;
* a clopen `A ⊆ X`.

They must satisfy three conditions.
* Every `N_j` acts minimally on `X`.
* `X` has no `F_n`-invariant Borel probability measure.
* `2 mu_0(A) <= mu_0(A)` fails in the algebraic order of `M`.

By `fn-free-action-via-profinite-diagonal-certificate` this implies
`free-minimal-fn-cantor-action-not-almost-unperforated`.  Freeness is traded
for minimal kernels and a covariant certificate.

## Attempts

* **Invariant certificates die.**  Suppose every `mu_j` is `F_n`-invariant,
  for example `mu_0` divided by the index.
  * `F_n` is minimal on `X` and `X` has no invariant measure, so `[A]` has no
    state and is paradoxical (`kmp-tarski-theorem-preordered-monoids`):
    `(k+1)[A] <= k[A]` for some `k`.
  * Invariance gives `(k+1) mu_j(A) <= k mu_j(A)`, hence
    `(k+i) mu_j(A) <= k mu_j(A)` for all `i`.
  * With `P = [F_n : N_j] >= k` and `mu_0 = P mu_j`, this gives
    `2 mu_0(A) <= k mu_j(A) <= mu_0(A)`.
  * Where it dies: the certificate must use `N_j`-invariant maps that are not
    `F_n`-invariant.
* **Dense subgroups of a Fraïssé automorphism group.**  By item 6 of
  `profinite-diagonal-cantor-type-is-transfer-limit`, if the closures of the
  `N_j` in `Homeo(X)` stabilize, the extension is almost unperforated.  Then
  `fn-free-action-via-profinite-diagonal-certificate` shows that no
  certificate as above exists for that chain.
  * So the closure of `F_n` must have infinitely many strictly shrinking open
    normal subgroups of finite index.
  * Where it dies: for `F_n` dense in Boldrini--Prasad's `Aut(B, mu)`
    (arXiv:2607.01896v1), all finite-index subgroups are dense unless that
    group has a proper open subgroup of finite index.  Whether it has one is
    unverified here.
  * Natural replacement (heuristic, not checked in detail): automorphisms of a
    Boolean algebra with a measure valued in `M`-valued measures on
    `K = lim F_n/N_j`, covering translations of `K`.  Where that dies: tuples preserving a common clopen set whose
    measure is invariant under the letters' translations form an open set.
    It is nonempty as soon as each letter's coset contains one such element.
    This is the generic-pairs obstruction on the root again, so a Baire
    argument over finitely many letters fails.  Such a structure has not been
    built here.
* **A totally minimal letter.**  If one generator has all nonzero powers
  minimal, every `N_j` is minimal, since it contains such a power.  No
  certificate-preserving totally minimal element is known; unexplored.
