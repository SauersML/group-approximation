# Overfold merges on L_j-intransitive levels: no sharing across L_j-orbits

Worker swarm-0917-w16-w16-fp-break (belief breaker), September 19, 2026.
Target: `fpbs-mal-overfold-merges-never-help`, which states
`deep_j(Q) = law_j(Q)`.

## 0. Why this regime

- `law_j(Q) = r(Q^{(j)})` is additive over the `L_j`-orbits of `Q`.
- The earlier exact data (`exact_search.py`, 70 levels) used random
  transitive `Q`, and almost all of those had `L_j` transitive as well.
- On an intransitive level, one overfold pair `(u, v)` of `Γ_{j+1}(Q)` has
  `m(u)` and `m(v)` in different components of `Γ_j(Q)`. Its fold closure
  can make identifications inside two different `L_j`-orbits at once.
- So this is the only obvious way a single non-lawful seed could do the work
  of two lawful ones, which would give `deep < law`. We tested it directly.

## 1. Computation

The script is
`experiments/fpbs-overfold-sharing-2026-09-17/intransitive_exact.py`.
- It samples `L`-transitive `Q` of size `n` whose `L_j`-restriction has at
  least `minorbits` orbits.
- It computes `law_j` and `deep_j` exactly with the partition BFS of
  `exact_search.py`, which it imports.
- It counts the overfold seeds in the minimum `deep` witness it finds.

| file | n | j | L_j-orbits | levels | law = deep values | witnesses using overfold seeds |
|---|---|---|---|---|---|---|
| `run_n5_j1.txt` | 5 | 1 | 2 | 15 | 2 (7), 3 (8) | 3 |
| `run_n8_j1.txt` | 8 | 1 | 2 | 10 | 3 (10) | 0 |
| `run_n6_j1_3orb.txt` | 6 | 1 | 3 | 10 | 3 (6), 4 (4) | 6 |
| `run_n4_j2.txt` | 4 | 2 | 2–3 | 10 | 2 (5), 3 (5) | 5 |
| `run_n5_j2.txt` | 5 | 2 | 2–3 | 8 | 2 (3), 3 (5) | 3 |

**Result:** in all 53 levels, `deep_j = law_j`, and the `FLAG deep<law` line
never fires.

In 17 levels the minimum witness contains overfold seeds, and there is
always a lawful witness of the same size. So overfold seeds occur freely in
minimum witnesses but never lower the count.

The script counts overfold seeds with `m(u) != m(v)`. It does not separate
the cross-orbit ones. Their absence from the count gap follows anyway, since
every overfold choice, cross-orbit or not, is in the `deep` search.

## 2. Bookkeeping

**Lemma A (connectivity count).** For each `L_j`-orbit `O` of `Q`, let `s_O`
be the number of `L_{j+1}`-orbits it contains. These are the components of
`Γ_{j+1}(Q)` lying over the component of `O` in `Γ_j(Q)`. Then every seed
set `S` whose fold closure contains `ker(m)` has

```text
|S|  >=  sum_O (s_O - 1).
```

This holds whether or not `S` contains cross-orbit pairs.

*Proof.*
- Folding never joins components. Only a seed can join two components, and
  a seed joins at most two.
- So the quotient of `Γ_{j+1}(Q)` by the closure of `S` has at least
  `sum_O s_O - |S|` components.
- The closure contains `ker(m)`. So the quotient is a quotient of
  `Γ_{j+1}(Q)/ker(m)`.
- The vertices of `Γ_{j+1}(Q)/ker(m)` biject with those of `Γ_j(Q)` via `m`.
  Since `m` is surjective, every edge of `Γ_j(Q)` is the image of an edge,
  and so it joins the corresponding vertices of the quotient.
- Hence `Γ_{j+1}(Q)/ker(m)` has at most as many components as `Γ_j(Q)`,
  which is `#O`, the number of `L_j`-orbits. The further quotient has at most
  `#O` components as well.
- Hence `sum_O s_O - |S| <= #O`. QED

*Consequence.* Cross-orbit seeds are useless for connectivity. A seed that
joins components over two different `L_j`-orbits spends its one join on a
connection that `ker(m)` does not require. Sharing can only come from the
fold closure's internal identifications, not from connectivity.

*Limitation.* On free profinite towers, `sum_O (s_O - 1) / |Q_m|` tends to
0: an `L_{j+1}`-orbit of an essentially free level is large. So Lemma A is
not a floor. It only explains why the counts never go below the component
count.

**Remark B (not used, not proved).** Summing Euler characteristics over
components suggests `χ(Γ_{j+1}(Q)) = χ(Γ_j(Q))`. Then a lawful collapse would
balance vertex merges against loop collapses. This is not verified here and
gives no inequality between `deep` and `law`.

## 3. What this changes

- **Evidence gained.** The one mechanism that makes `deep < law` plausible,
  a single overfold seed serving two `L_j`-orbit kernels, is now tested
  exactly in the regime where it can act. It never helps.
- **Belief.** Unchanged in direction, and slightly stronger for (O). The
  route `fpbs-mal-depth-floor-from-overfold-domination` still hinges on the
  exchange statement at transitive levels of growing size, where exact
  search is out of reach, and on (W).
- **Not claimed.** Nothing for `n > 8` or `j > 2`. Nothing about the
  asymptotic ratio `deep/law`, which is what the weak form `c > 0` needs.

## 4. A dead end recorded

**Stabilised witnesses.** For a free `Γ_mal`-action `Y`, the witnesses
`X_j = Y ∘ ι_{j+2}` satisfy `X_j^{(j)} = Y ∘ ι_2`. So their lawful density
is constant in `j`.

Using these as a uniform witness for (W) is circular. It asserts exactly that
some free `Γ_mal`-action has promotion cost bounded below, which is the floor
itself. Also, the profinite exactness formula needs `L`-transitive levels,
and restrictions of `Y` need not have them.
