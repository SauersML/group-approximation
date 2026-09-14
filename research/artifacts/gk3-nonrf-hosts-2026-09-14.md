# gk3-nonrf-hosts: famous non-residually-finite Gottschalk hosts (2026-09-14)

Lane `gk3-nonrf-hosts` (Gottschalk team). Scope:
- Radu's BMW lattice `Γ_R`;
- Higman's group `H`;
- Deligne's triple cover `E_3`;
- the Kun--Thom Clifford covers `E_S` and lamp quotients `W/U`;
- the Fournier-Facio torsion-free group.

## 0. Verdict

- **No strict automaton found, so Gottschalk is not decided.**
- **New theorem, landed ESTABLISHED and not independently re-derived:**
  `higman-group-algebras-embed-in-division-rings`.
  - For every division ring `k`, in every characteristic, `k[H]` embeds in a division ring.
  - So `M_n(F_q[H])` is directly finite, and every injective linear automaton on `(F_q^n)^H` is surjective.
  - This refutes `higman-group-algebra-not-stably-finite`: the linear route to a counterexample on Higman's group
    is dead in all characteristics.
- **Ranking and exact gaps:** Sections 2 and 5.

## 1. A dominance principle for the ranking

Sofic groups are surjunctive (Gromov, Weiss). A strict automaton on a host whose soficity is open would also prove
that host nonsofic. For `Γ_R`, `H` and `E_3` that is itself open: Kassabov--Kuperberg--Riley call `H` a candidate
nonsofic group, and `E_3` is tied to the Deligne sector gap.

Main already has hosts that are proved nonsofic:
- the binary Leavitt unit group;
- the Kun--Thom wreath `W` (which is surjunctive);
- the lamp quotients of `W`;
- the Fournier-Facio group.

A counterexample search pays no soficity toll there. So among the hosts in scope, the open-soficity hosts are
better spent on barrier theorems, and a nonlinear search belongs on a known nonsofic host.

The Garden-of-Eden localization (`sofic-radical-localizes-garden-of-eden-windows`) sharpens this: every Garden of
Eden window contains a sofic-invisible difference.
- On `E_3` the only candidate is the centre `z`.
- On `Γ_R`, a radius-two pair must put `δ^4` in the sofic radical
  (`radu-lattice-radius-two-pairs-force-the-mark-into-the-radical`, candidate proof on paper, unverified).

## 2. Host table

| host | known nonsofic? | linear route | nonlinear constraints on main | best live gap |
|---|---|---|---|---|
| `H` (Higman) | open | **dead in every characteristic (this lane)** | memory mixes all four BS pieces through free edge groups; girth five kills Sidon unbalanced designs; copying maps absorbed | a nonlinear strict pair; for `2^n` alphabets it must be non-formalizable by the formal-pair reduction of main (not re-derived here) |
| `Γ_R` (Radu) | open | odd `p` dead (characters); `p = 2` no idempotent starting data, radius ≤ 4 excluded, radius 5 needs H10 | radius-two pairs fold only `(zx)^2 ~ (xz)^2`; Garden of Eden windows have diameter ≥ 8 | H10 finite check; coefficient equations of `D = D^2` at radius 6 over `F_2` |
| `E_3` (Deligne) | open | `p = 3` dead; `p != 3` twisted algebras live | memory group keeps `z` in its finite residual; bijective on `z`-invariant configurations | rank-projective sector gap for the Deligne multiplier |
| `E_S` (Kun--Thom Clifford cover) | weakly sofic; soficity open | binary dead (nilpotent ideal); odd characteristic reduces to the anti-central skew ring | tables must read profinitely invisible adjacency | `clifford-cover-anti-half-skew-ring-not-directly-finite` |
| `W/U` (lamp quotients) | nonsofic | open over `F_2` for non-closed `U` | closed `U` dead; the decoder must read `U` | Example 5.4 of the lamp-quotient artifact (closure test) |
| Fournier-Facio `G` | nonsofic | open | invariant-output designs need torsion; no permanence applies | a design using the compression of the Kazhdan subgroup |

## 3. The Higman theorem

Nodes, all new on main at this landing:
- `fsp-graph-of-rings-and-linnell-extension-imports` and its `-citation`: the characteristic-free imports, read in
  the TeX source of arXiv:2303.08165v4;
- `hughes-free-division-rings-pass-to-directed-unions` and its `-proof`;
- `higman-bs-amalgam-has-hughes-free-division-rings` and its `-proof`;
- `higman-group-algebras-embed-in-division-rings` and its `-proof`.

**The point.** Fisher--Sanchez-Peralta embed `k[H]` in a division ring through `H = G_1 *_(F_ac) G_2` and their
characteristic-free graph-of-rings corollary. They get Hughes-free division rings for the vertex groups
`G_1 = BS(1,2) *_Z BS(1,2)` only through Strong Atiyah, hence only in characteristic zero (their Proposition 3.14).

The new input is a split extension:
```text
G_1 = <a,b,c | b^a = b^2, c^b = c^2> = K ⋊ <a,b>,    K = ker(c -> 1).
```
`K` acts on the Bass--Serre tree of `<a,b> *_<b> <b,c>` with trivial edge stabilizers, and its vertex stabilizers
are trivial or copies of `Z[1/2]`. So `K` is locally free.

**The chain, in any characteristic.**
1. Free groups have Hughes-free rings (Jaikin-Zapirain).
2. Directed unions preserve them, so `K` has one.
3. `D_(kK) * BS(1,2)` is a domain (iterated twisted Laurent rings).
4. Fisher--Sanchez-Peralta `cor:HF_fi` gives a Linnell, hence Hughes-free, embedding of `k[G_1]`.
5. Their `cor:locIndGraphDivRing` then embeds `k[H]` in a division ring.

The linear automaton corollary extends the local rule of the inverse from the image subspace to the whole pattern
space, which gives a left inverse matrix.

**Scope.** The argument uses only the four-piece Higman group. Other members of the `H_k(BS(1,m))` family need
Hughes-free rings for longer chain groups, where the retraction kernel is no longer locally free. Not attempted.

## 4. Why this method stops at the other hosts

Division ring embeddings need a torsion-free group. The Hughes-free and Linnell machinery needs local
indicability of the vertex groups, or an elementary amenable quotient over a locally indicable kernel.
- `Γ_R`: elements of order two, and `(1+a)^2 = 0` in characteristic two.
- `E_3`: central `C_3`.
- `E_S`, `W/U`: 2-torsion.
- Fournier-Facio `G`: torsion-free, but it contains an infinite Kazhdan subgroup with finite abelianization, so no
  locally indicable splitting reaches it (`universal-torsion-free-hosts-not-sofic-or-locally-indicable` records
  the same obstruction for the master host).

So the method kills the linear route on `H` and on nothing else in scope.

## 5. Exact gaps, ranked by leverage

1. **`H`, nonlinear.** A strict automaton on `H` must be nonlinear, must read all four pieces through free edge
   groups, and would prove `H` nonsofic. No design is known.
2. **Known nonsofic hosts first.** For the counterexample direction, the lamp quotients `W/U` and the
   Fournier-Facio group pay no soficity toll. The decisive open items are:
   - the closure test of Example 5.4 (lamp quotients);
   - direct finiteness of `F_2[W/U]` for non-closed `U`;
   - a compression-based design on `G`.
3. **`Γ_R`, `p = 2`.** Run H10 (the Remark 3.6 computation to length ten) and the radius-six coefficient
   equations. This is finite compute and was not run in this session.
4. **`E_3`, `p != 3`.** Rank-projective approximation of the Deligne multiplier, the same problem as the
   hyperlinearity lane's sector gap.
5. **Question 3.? of Fisher--Sanchez-Peralta** (`q:HF`: are graph-of-rings division rings Hughes-free for locally
   indicable graphs of groups?). The split-extension trick answers the vertex-group case needed here. A general
   answer would give division ring embeddings for many more torsion-free hosts in positive characteristic.

## 6. Not done

- No MSI search was run.
- The radius-two template `G_4` on `Γ_R` has memories of size nine: rule tables of 512 bits each, which is not an
  exhaustive search. A structured search using the forced fold and essential coordinates is the only feasible
  design, and it was not built.
- No second lane has re-derived the Higman theorem.
