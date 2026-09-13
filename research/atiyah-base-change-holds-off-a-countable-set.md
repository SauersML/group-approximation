---
rg: 2
id: atiyah-base-change-holds-off-a-countable-set
kind: claim
title: Strong Atiyah over the algebraic numbers extends to one transcendental coefficient off a countable set, which is empty iff ranks are Galois invariant
distinct_from:
  strong-atiyah-base-change-algebraic-to-complex: that is the open base change to all complex coefficients for all torsion-free groups; this proves integrality group by group for purely transcendental coefficient fields, outside a countable exceptional set in one variable and a null meagre set in several.
  vn-rank-galois-invariant-for-torsion-free-groups: that is the open invariance statement; this shows that in one variable it is equivalent to the emptiness of the countable exceptional set.
  strong-atiyah-base-change-from-galois-invariance: that derives complex Strong Atiyah from invariance through Riemann--Roch and central variables; this gives pointwise integrality off exceptional sets with no invariance hypothesis, and covers only purely transcendental coefficient fields.
artifacts:
  - research/artifacts/atiyah-countable-exceptions-2026-09-12.md
---

**ESTABLISHED** by [[atiyah-base-change-off-countable-set-proof]].

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar`. Then
`D = D_(Qbar[G])` is a skew field. For `A(x)` over `Qbar[G][x]` with `n` columns,
let `r(A)` be its rank over the Ore skew field `D(x)`, and put

```text
E_G = { z in C \ Qbar : dim ker A(z) != n - r(A) for some A over Qbar[G][x] }.
```

1. **Countable.** `E_G` is countable.
2. **Off the set.** For every transcendental `z` outside `E_G`, `x -> z` embeds
   `D(x)` into `U(G)` as the division closure of `Qbar(z)[G]`. So every matrix
   over `Qbar(z)[G]` has integral kernel dimension, independent of `z`.
3. **Invariance.** Kernel dimensions of matrices over `Qbar(z)[G]` are invariant
   under automorphisms of `C` fixing `Qbar` iff `E_G` is empty.
4. **Several variables.** The analogous exceptional set `Sigma_s ⊂ C^s`, for
   families over `Qbar[G][x_1..x_s]`, is a Borel set. Its sections in the last
   variable over algebraically independent tuples are countable, so it is
   Lebesgue-null and meagre. Off it, on algebraically independent tuples,
   `D(x_1..x_s)` is the division closure of `Qbar(z_1..z_s)[G]`.

**What it does not give.** It covers purely transcendental coefficient fields
only. An algebraic extension `F` of `Qbar(z)` needs `D(x) (x) F` to remain a skew
field inside `U(G)`. That is Conjecture 3 of Jaikin-Zapirain--Lopez-Alvarez
(arXiv:1810.12135v4, p. 35) for `G`, and countability does not supply it. So the
root `strong-atiyah-torsion-free` is not reached. The one-variable exceptional
points are exactly what `vn-rank-galois-invariant-for-torsion-free-groups` would
remove.

**Under the determinant conjecture `E_G` is empty**
(`determinant-conjecture-gives-one-variable-atiyah-base-change`, unreviewed).
An earlier and weaker consequence says the exceptional points are badly
approximable by algebraic numbers of every bounded degree
(`determinant-conjecture-excludes-liouville-atiyah-exceptions`).

**Model tests.**
* For `G = Z/2` and `A(x) = x(1 + s)/2`, every `z != 0` gives kernel `1/2`.
  Torsion-freeness is used through the skew field `D`.
* Let `t` be a self-adjoint operator with no algebraic atoms and an atom `1/2`
  at `pi`. Then `D = Qbar(t)` is a skew field of affiliated operators, but `pi`
  is exceptional. So group structure, not the algebra of `D`, must empty the set.
* For sofic `G`, Jaikin-Zapirain's base change gives `E_G = ∅`.

No novelty is claimed for the ingredients: Jacobson's normal form over `D[x]`, and
independence of eigenspaces in `U(G)`.
