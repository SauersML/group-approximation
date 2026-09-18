# bh-branch-in-v: sources read, 2026-09-18

Lane bh-branch-in-v. Target: `finitely-generated-weakly-branch-group-embeds-in-thompson-v`, i.e. the Bodart–D'Angeli–Perego–Rodaro question in its finitely generated form. All sources were fetched with the msi wrapper into `/projects/standard/hsiehph/sauer354/gqsrc/bh-branch-in-v/` and read locally from TeX.

## Sources

| Source | File, md5 | What was read |
|---|---|---|
| C. Bodart, D. D'Angeli, D. Perego, E. Rodaro, *A graph-theoretical characterisation of subgroups of Thompson's group V*, arXiv:2608.02111v1 | `src.tar` 288c4c1c…; `sec7_branch.tex` d1cbd586…, `sec6_poly.tex` c6c9881a…, `sec2_equiv.tex` 3b3b8627… | all of §0, §2, §6, §7; §1 through `lem:growth_of_CF_graphs` |
| N. Matte Bon, V. Nekrashevych, T. Zheng, *Commensurating actions and self-similar groups*, arXiv:2607.13776 | `mnz.tar` 4cfdfac4…; `FW_amenable.tex` 76556de6… | introduction; §2 (`l-reduction-transitive`, ends vs commensurated sets); §3 (`t-commensurating-product-discrete`, `l-geometric-argument`); §4 through `t-multi-ended-graphs` and `c-FW` |
| K. Juschenko, *Non-elementary amenable subgroups of automata groups*, arXiv:1504.00610v1 | `jus.tar` a67bc47c…; `main.tex` bb51fa75… | the main theorem; the corollary "Finitely generated branched groups are not elementary amenable"; the Basilica corollary |

## Exact statements used

- **BDPR, §7.**
  - Question (l.133–135): "Does any (weakly) branch group embed in Thompson's V?"
  - Question (l.150–153): do all Schreier graphs of a f.g. branch group have finitely many (or countably many) ends? A positive answer would exclude f.g. branch subgroups of V.
  - The remark before it combines MNZ Theorem B with BDPR's linear-growth context-free graph results (`thm:Houghton_universal`, `thm:elementary_amenable`) to exclude contracting self-replicating branch groups.
- **MNZ `l-commensurating-branch` ("first key step", for branch groups).** For `G` acting faithfully on `G/H` with at least two ends, there is `⊕_{v∈N(ξ)} K_v ≤ H ≤ G_ξ` with each `K_v` of finite index in `rist(v)`. The proof does not need finite germs.
- **MNZ `t-multi-ended-graphs`.** Under finite germs, `H` has finite index in `G_ξ` and `e(Γ̃_ξ) ≥ e(Γ_{G/H})`.
- **MNZ introduction.** For contracting self-similar groups, the groups of germs on `∂T` are all finite.

## Not read at source

- Nekrashevych's book, Thm 3.9.12 (bounded automata generate contracting groups), recalled.
- Bondarenko, Math. Ann. 2012, Thm 1 (polynomial activity gives subexponential orbital Schreier graphs). It is taken from BDPR's citation in the proof of `cor:orbital_Schreier_are_not_CF`.
- The Basilica Schreier-graph study that BDPR cite for "not a quasi-tree".

## Lane results

- `multi-ended-branch-actions-are-boundary-sandwiched`, with proof `multi-ended-weakly-branch-actions-sandwich-proof`. This is MNZ's first key step, extended from branch groups to weakly branch groups with finitely generated `rist(n)`.
- `branch-group-embeddings-in-v-are-boundary-sandwiched`, with proof `branch-group-embeddings-in-v-boundary-sandwich-proof`:
  - f.g. branch `G ↪ V` holds exactly when some subgroup of some `G_ξ` has a context-free Schreier graph;
  - with finite germs, the embedding forces an exponential-growth boundary orbit;
  - so bounded-automaton branch groups never embed in `V`.
