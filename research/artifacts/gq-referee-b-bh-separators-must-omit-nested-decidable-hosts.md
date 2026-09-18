# gq-referee-b: `bh-separators-must-omit-nested-decidable-hosts` (citation and scope lens)

Node as landed at 507f9fabf (lane bh-refute). §§1–3 were passed by gq-referee-a (90752e2d8). Lens: every cited input
read at its source where possible, and every hypothesis checked against its use.

**Verdict: PASS.**
- Every row of the §2 table is supported at source, or by a secondary source read here.
- The Zaremsky quote is verbatim.
- §3's use of `complexity-bounded-host-classes-are-not-universal` matches that node's hypotheses. It needs `T`
  non-decreasing, which should be stated (W2).
- One literature claim, "the hardest known word problem is coNP-complete", is not supported by the cited source
  (W1).
- Miller 1971 remains unpinned, with only a secondary pointer (W3).

## 1. The §2 table

- **`2V`, the torsion problem.** Belk–Bleak, arXiv:1405.0982 (Trans. AMS 369 (2017)). Abstract, read: "we prove that
  the torsion problem for elements of the Brin-Thompson group 2V is undecidable". Also: "2V furnishes the first
  concrete example of such a group", referring to "a finitely presented group with solvable word problem and
  unsolvable torsion problem".
  - So the undecidability holds for words in a finite generating set, which is what the row needs, since `2V` is
    itself a finitely generated subgroup of `2V`. ✓
- **`2V` is finitely presented and simple.** Brin, arXiv:math/0406046 (Geom. Dedicata) and math/0501082 (J. Algebra),
  abstracts read. The second says: "In a previous paper, we ... proved that it is simple, infinite, finitely
  generated ... Here we show that the new group is also finitely presented". So "(Brin 2004, 2005)" is the right
  split. ✓
- **`F_2 ≤ V`.** Bleak–Salazar-Díaz, arXiv:0911.0979, abstract read: the class of free products embeddable in `V`
  "includes ... the countable non-abelian free groups". ✓
- **`V × V ≤ V`.** Elementary. Conjugating by the prefix map `h_0 : w ↦ 0w` carries `V` onto elements supported on
  `0C`, and similarly for `1C`. The node's parenthesis is the proof. ✓ So `F_2 × F_2 ≤ V`.
- **Mihailova (1958).** Pinned through Bogopolski–Ventura, arXiv:0810.0690, p. 1, read:
  - "The important observation made in [11] says that the membership problem for `M(H)` in `F_n × F_n` is solvable
    ... if and only if the word problem for `H` is solvable."
  - "Thus, there also exist finitely generated subgroups of `F_n × F_n` with unsolvable membership problem."
  - Here `n ≥ 2`, and `F_n × F_n ≤ F_2 × F_2`. So `V` fails the hereditary generalized word problem. ✓
- **Miller (1971), conjugacy.** Not pinned. The only secondary pointer read is Bridson–Miller, arXiv:0708.4331, p. 1:
  subdirect products of free groups include "some with unsolvable decision problems [19]". That does not name the
  conjugacy problem. Keep "classical, not re-read" (W3).
- **Subgroup-closure.** The definitional argument in §2 is correct for all three classes. The property "every
  finitely generated subgroup has X" passes to subgroups, and X does not depend on the generating set for these three
  problems. ✓

## 2. §3 and the imported node

- **The Zaremsky quote.** Zaremsky, arXiv:2305.15176v2 (Michigan Math. J.), read at source.
  - p. 3: "a priori there is not any reason to doubt that arbitrarily large, recursive Dehn functions are possible."
    Verbatim. ✓
  - pp. 1–2: "the only finitely presented simple groups where something is known about their Dehn functions are the
    Burger–Mozes groups ..., which have quadratic Dehn function ..., and Thompson's groups T and V, which are known
    to have polynomial Dehn function". The abstract adds: "To the best of our knowledge, these are the first such
    examples known."
  - So "the only superpolynomial Dehn lower bounds known are his" is sourced, as of v2 (July 2024). ✓
- **Birget.** arXiv:1902.03852v2, abstract read: "the word problem of the Brin-Thompson group nV over a finite
  generating set is coNP-complete for every n ≥ 2". ✓ (Zaremsky p. 2 also cites [Bir20]: if `nV` embeds in a
  finitely presented group with polynomial Dehn function then NP = coNP.)
- **`complexity-bounded-host-classes-are-not-universal`.**
  - Its hypothesis: a class `K` of finitely generated groups, each with a word-problem algorithm within
    `C_S·T(C_S·l) + C_S·l + C_S` for some finite generating set.
  - Its conclusion: a two-generated `G` with solvable word problem embeds in no member of `K`.
  - (S2) for `P_T` follows. If `G ∈ P_T`, then `G`, as a finitely generated subgroup of itself, is in `K`, and `G`
    embeds in `G`, a contradiction. So the hypotheses match. ✓
- **"`P_T` separates iff every finitely presented simple group meets `T`."** The direction "each such `S` meets `T`
  ⇒ its finitely generated subgroups do" uses the linear length blow-up `l ↦ C_0 l`. That gives the time bound
  `C·T(C·C_0·l) + …`, which has the required form only if `T` is non-decreasing. The same holds for the remark on
  changing generating sets (W2).

## 3. §4 citations marked "not re-read"

- **Scott 1984, `GL_n(Z)`.** Zaremsky, arXiv:2405.09722, l.117 (TeX read): "every `GL_n(Z)` [scott84]" satisfies the
  conjecture, with [Sco84b] "The embedding of certain linear and abelian groups in finitely presented simple groups",
  J. Algebra 90 (1984). Secondary pin. ✓
- **Röver 1999, Grigorchuk group.**
  - Nekrashevych, arXiv:1312.5654, p. 22: "`V_G/V'_G` is trivial, hence `V_G` is simple. Simplicity of `V_G` was
    proved in [Röv99]".
  - SWZ, arXiv:1712.05361v3, Ex. 7.2: "`V_2(Grig)` is of type `F_∞` [BM16]".
  - So `V_2(Grig)` is a finitely presented simple group containing Grig. Secondary pins. ✓

## Warnings

- **W1.** "the hardest known word problem is coNP-complete (`nV`, Birget arXiv:1902.03852)". Birget proves
  coNP-completeness for `nV`. Neither Birget's abstract nor Zaremsky's survey paragraph says that no finitely
  presented simple group with a harder word problem is known.
  - That is a literature claim I could not check. It is not obvious: finitely presented simple hosts of finitely
    presented self-similar groups (Zaremsky 2405.09722) inherit their subgroups' word problems.
  - Suggest: "the word problem of `nV` is coNP-complete (Birget); we know of no finitely presented simple group
    proved to have a harder one (bounded search)".
- **W2.** State `T` non-decreasing in the definition of `P_T`. It is needed for subgroup inheritance and for
  independence of the generating set. This costs nothing, since any recursive bound can be replaced by its running
  maximum.
- **W3.** Miller 1971: keep "classical, not re-read". Suggested secondary source: C. F. Miller III, *On
  group-theoretic decision problems and their classification*, Ann. of Math. Studies 68 (1971). Not read here.
