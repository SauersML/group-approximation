# gq-referee-b: `hyperbolic-groups-lie-in-the-permutational-class` and `bbmz-oligomorphic-and-twisted-questions-are-pbh-forms` (citation and scope lens)

Nodes and routes as landed at fa1747017 and 6932547c3 (lane bh-typeA-universal). Referee a passed both (2bdad9399).

**Sources.**
- BBMZ, *Hyperbolic groups satisfy the Boone–Higman conjecture*, arXiv:2309.06224. The TeX is local at
  `gq/src/bh-free-03/bbmz2-2309.06224.tex` (2227 lines). This is not the MSI copy the lane read. It contains no
  version marker, so the numbers below are from this file's counters.
- BFFHZ, arXiv:2503.21882, TeX at `gq/src/bh-free-24/bffhz.tex`.

**Verdict: PASS.** Every BBMZ quotation and label checks out verbatim. The counter numbering is confirmed, and I
supply the two numbers the node leaves open.

One scope point: the priority paragraph misses the shortest literature route (W1). BFFHZ Theorem C, (2) ⇒ (1),
together with BBMZ's proof of Proposition 5.1 already gives items 1–2. So the result is a two-line consequence of
printed theorems, and "Why it is not a formality" should be toned down.

## 1. BBMZ labels and numbers (local TeX)

The preamble has `\newtheorem{theorem}{Theorem}[section]` (l.39), and every other environment shares that counter
(l.40–54).

| Node's citation | Label, line | Counter number | Quote check |
|---|---|---|---|
| Theorem 3.1 | `thrm:fin_pres`, l.840 (first environment of §3) | 3.1 ✓ | "Every full, contracting RSG is finitely presented." ✓ |
| Theorem 4.1 | `thrm:hyp_to_contracting`, l.1234 (first of §4) | 4.1 ✓ | "Every hyperbolic group embeds into a full, contracting RSG." ✓ |
| intro lettered theorem | `thrm:hyp_embed`, l.198 | **Theorem E** | The fifth lettered environment of §1, after A `thrm:bh_hyp`, B `thrm:FPTheorem`, C `thrm:rsg_to_simple` and D `cor:ss_embed`. ✓ |
| Prop 5.1 | `prop:contr_to_simple`, l.1752 | 5.1 ✓ | "Every full, contracting RSG embeds into a finitely presented simple group." ✓ |
| Cor 5.2 | `cor:RN_BH`, l.1758 | 5.2 ✓ | ✓ |
| Prop 5.4 | `prop:HighlyTransitiveAction`, l.1776 | 5.4 ✓ | Verbatim, as quoted in the route (b). ✓ |
| `prop:fin_gen_stabs` | l.1815 | **Proposition 5.8** | Verbatim, as in the route (c). ✓ |
| faithfulness (d) | proof of 5.1, l.1833 | — | "Note that S is dense in E, so G acts faithfully on S." ✓ |
| Example `ex:rn` | l.654 (§2.5) | — | "any Röver–Nekrashevych group of a finite-state self-similar group is a full RSG" ✓ |

**How 5.8 is obtained.** §5 contains, in order:
- 5.1 `prop:contr_to_simple`;
- 5.2 `cor:RN_BH`;
- 5.3 `thrm:action_to_simple`, which is [zaremskyTaste, Theorem 4.2];
- 5.4 `prop:HighlyTransitiveAction`;
- 5.5 `prop:CyclicStabilizers`;
- 5.6 and 5.7, two remarks;
- 5.8 `prop:fin_gen_stabs`.

A published version may differ. The label is the safe reference.

**The contracting remark** after Definition `def:contracting` (l.698): "in the special case of Röver–Nekrashevych
groups (see ex:rn) it is equivalent to the underlying self-similar group being contracting." ✓

## 2. Step 2: type (A)

The four conditions come from BBMZ (a)–(d). Two details check at source:
- **Point stabilizers at every point of `S`.** BBMZ l.1785: "the set of rational points in any clopen set
  `E ⊆ Σ_Γ` is stabilized by the action of the rational group `R_(Γ,E)`." So every point of the orbit is rational, and
  Proposition 5.8 applies to it. ✓
- **Proposition 5.4 applies.** It needs `G` to be a "full group of homeomorphisms of `X`", with `X` Hausdorff and with
  a clopen basis. That is `X = E`, and a full RSG is such a group. ✓

## 3. Priority (W1)

The node says BFFHZ "list hyperbolic groups among groups known to satisfy Boone–Higman, not PBH". That is accurate
for l.141: "hyperbolic groups \cite{bbmz_hyp}" is listed under BH.

But BFFHZ contain the general equivalence that yields PBH at once.

**Theorem C** (`thrm:mif_pbhc`, l.206; the third lettered environment, after A `thrm:autfn` and B `cor:autfn_pbhc`).
For finitely generated `G`, the following are equivalent:
- "(1) `G` satisfies the permutational Boone–Higman conjecture";
- "(2) `G` embeds in a finitely presented (simple) twisted Brin–Thompson group";
- two further conditions.

**Also l.185:** "`SV_Γ` is finitely presented if and only if the action of `Γ` on `S` is of type (A)
\cite{zaremsky_fp_tbt}".

**The combination.** BBMZ's proof of Proposition 5.1 shows that `SV_G` is finitely presented for a full contracting
RSG `G`. By l.185, that is a type-(A) action of `G`. By Theorem C, this puts every subgroup of `G` in PBH.

So items 1–2 follow from printed results in two lines. The route's own verification is correct and slightly more
explicit, since it names the actor and the set.

**Suggested priority text:** "Immediate from BBMZ (proof of Prop. 5.1: `SV_G` finitely presented) and BFFHZ l.185 /
Theorem C (2) ⇒ (1). We found no place where the permutational conclusion for hyperbolic groups is stated."

**Suggested change to "Why it is not a formality".** Keep the point that product closure of BH is open. But say that
the combination itself is formal, and that its value is recording it.

## 4. Named-problem bearing

Hermiller–Meier (J. Algebra 171 (1995)) remains not read at source, as the node says. A bounded arXiv search did not
find it (it predates the arXiv). It is used only in the named-problem paragraph, not in items 1–3. ✓

## 5. `bbmz-oligomorphic-and-twisted-questions-are-pbh-forms`

- **Numbering.** BBMZ l.215 has `\setcounter{theorem}{0}`, so the questions of §1.3 (`ssec:open`) are 1.1–1.6.
  - Question 1.5 is the unlabelled question at l.241.
  - Question 1.6 is `quest:always_twisted_bt`, l.247.
  - Both numbers are right, and §1.3 is right. ✓
- **Wording.** Both quotations are verbatim:
  - 1.5: "Does every finitely presented group with solvable word problem embed in a finitely presented oligomorphic
    group with finitely generated stabilizers of finite subsets?"
  - 1.6: "Does every finitely presented simple group embed in a finitely presented (simple) twisted Brin–Thompson
    group?" ✓
- **"Oligomorphic group".** BBMZ use Cameron's notion, "a group of permutations of a set `S` is oligomorphic ..."
  (l.1768). That is a faithful action, as Step 2 of the route uses. ✓
- **The Clapham import.** Step 2 uses `clapham-fp-embedding-preserves-word-problem`: a finitely generated group with
  solvable word problem embeds in a finitely presented group with solvable word problem. This moves the question from
  finitely generated to finitely presented inputs, which is exactly the hypothesis mismatch between PBH and Question
  1.5. The use matches the imported statement. ✓
- **Related text in BBMZ.** Question 1.3 (`quest:all_fp_subgroups_of_rat`, l.229–231) already frames the same
  oligomorphic condition for subgroups of `R_(Γ,E)`. The node could cite it alongside 1.5 (optional).

## Warnings

- **W1.** Priority: cite BFFHZ Theorem C (2) ⇒ (1) and l.185, and describe the result as their immediate combination
  with BBMZ's proof of Prop 5.1. Tone down "not a formality" accordingly.
- **W2.** Supply the numbers: `thrm:hyp_embed` is Theorem E, and `prop:fin_gen_stabs` is Proposition 5.8. Both come
  from the counters of the local TeX, whose version is unmarked. Keep the labels.
