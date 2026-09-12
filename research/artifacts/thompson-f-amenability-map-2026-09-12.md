# Thompson's group F: amenability source map and method obstructions

Lane `thompson-f-amenability`, 2026-09-12. This artifact opens the roots
`thompson-f-is-amenable` and `thompson-f-is-not-amenable` in Cairn. It records
which statements were read from sources, and where each known method dies. It
proves nothing new about amenability.

## Statements imported, with what was read

| Claim | Source | What was read |
|---|---|---|
| `thompson-f-folner-function-exceeds-every-tower` | Moore, arXiv:0905.1118v7, Groups Geom. Dyn. (accepted), Thm 1.1 | theorem and definitions, from the ar5iv render |
| `thompson-f-random-walks-are-not-liouville` | Kaimanovich, arXiv:1602.02971v2; Groups, Graphs and Random Walks (CUP 2017) | abstract |
| `thompson-f-is-not-strongly-amenable` | Hartman–Juschenko–Tamuz–Vahidi Ferdowsi, arXiv:1607.04915v2, ETDS (accepted) | abstract |
| `thompson-f-amenable-iff-group-ring-is-ore` | Kielak appendix to Bartholdi–Kielak, arXiv:1605.09133v2 | abstract, plus the standard left-orderability chain |
| `thompson-f-has-no-free-subgroups` | Brin–Squier, Invent. Math. 79 (1985); Cannon–Floyd–Parry, Enseign. Math. 42 (1996) | classical, not re-read |

Context read at abstract level only:
- Guba, *Amenability problem for Thompson's group F: state of the art*,
  arXiv:2305.07113v4 (2023). The survey covers density estimates for finite
  subgraphs of Cayley graphs of `F` and equations in the group ring.
- Moore, *Amenability and Ramsey theory*, Fund. Math. 220 (2013) 263–280.
- Elder–Rogers, arXiv:1608.06703, a critique of numerical cogrowth methods.

Recorded as not accepted: arXiv:1408.2188 and the Shavgulidze papers (critique
at arXiv:1102.0747).

## Where each method dies

1. **Explicit Følner sets.** By Moore's Theorem 1.1, `C^-n`-Følner sets have at
   least `exp_n(0)` elements. Every family of elementary or fixed-tower size in
   `1/epsilon` fails.
2. **Liouville measures.** Finitely supported strictly non-degenerate measures
   all have non-trivial Poisson boundary (Kaimanovich). Only infinitely
   supported measures remain.
3. **Strong amenability.** It fails for `F`, so arguments through proximal
   actions are excluded.
4. **Ore condition.** Amenability is equivalent to the Ore condition in `K[F]`.
   This is exact, but no structural source of common multiples and no invariant
   ruling them out is known.
5. **Free subgroups and property (T).** `F` has no free subgroups, and it has the
   Haagerup property through `V` (Farley 2003), so neither classical source of
   non-amenability or uniform gaps is available.
6. **Numerics.** Cogrowth sampling (Elder–Rechnitzer–Janse van Rensburg 2015;
   Haagerup–Haagerup–Ramirez-Solano 2015) is reported to lean non-amenable, and
   Elder–Rogers identify two sources of error. Finite data cannot certify an
   asymptotic rate. This lane read no numerical values.
7. **This graph's compression rigidity.** `F ⊂ V` is a-T-menable, so by
   `a-t-menable-groups-have-no-rigid-compression-defect` it carries no rigid
   defect. Those tools are dead for amenability in both directions.

## Not done

- No certified cogrowth or Følner computation. A useful certified quantity would
  be a lower bound on the spectral radius from exact closed-walk counts, but that
  only reproduces known data unless the counts go past the published range.
- The full texts of Guba's survey, Moore's Ramsey paper and Kielak's appendix
  were not read. The web-search budget was exhausted, so PDF extraction on MSI is
  the next step.
