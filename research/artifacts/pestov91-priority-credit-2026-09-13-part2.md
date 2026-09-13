# Pestov 9.1: priority, timeline and credit, part 2 (2026-09-13)

Part 1 (`pestov91-priority-credit-2026-09-13.md`) covers §0–§2. This part covers the timeline, the credit and the rows
for `formalization.yaml`. Lane `pc-priority-credit`, main at `2d7d577ab`.

## 3. Timeline (UTC)

**Sources.**
- **GitHub push:** the timestamp of the push event in `GET /repos/SauersML/group-approximation/activity`.
- **Check-run:** the earliest `started_at` of the commit's check runs.
- **Author dates:** converted from -05:00.

The repository is public (`visibility: public`, created 2026-08-01).

| event | commit | author date | GitHub push | first check-run |
|---|---|---|---|---|
| Root node records the question, read from the arXiv PDF | `453fa69ce` | 09-12 04:14:46 | 09-12 04:14:56 | – |
| Lane `ex-kazhdan-simple-hyperlinear` launched on 9.1 | – | 09-13 02:29:38 (transcript) | – | – |
| Construction first appears in that lane's records | – | 02:38:47 (transcript) | – | – |
| Construction landed (ring, simplicity modulo the centre, LEF Kazhdan group); the 9.1 claim held OPEN for review | `f375478c7` | 03:18:24 | 03:18:28 | 03:18:31 |
| Operator MF does not imply weak quasidiagonality | `56bdeb8d3` | 03:31:03 | 03:31:12 | – |
| Route into the root: simple Kazhdan LEF, so sofic, so hyperlinear | `41e82567c` | 03:43:05 | 03:43:06 | 03:43:09 |
| Review PASS by `ex-verify-groups` | `0efeac410` | 03:48:55 | 03:48:56 | 03:49:01 |
| Independent re-derivation by `isk-hyperlinear-kazhdan` | `5dfab98df` | 04:06:49 | 04:06:51 | – |
| Root established: Pestov 9.1 answered in Cairn | `8b65f0932` | 04:09:24 | 04:09:25 | 04:09:30 |
| Novelty deep pass by `ex-novelty` | `2bbd83a42` | 04:28:40 | – | 04:28:46 |
| Second independent review PASS by `ex-pestov91-harden` | `badc66e2d` | 05:56:33 | 05:56:36 | 05:56:40 |
| The two reviews compared: no disagreement | `80873d2cc` | 06:00:14 | 06:00:16 | 06:00:20 |
| Write-up, part 1 | `a3b946271` | 06:06:09 | – | 06:06:24 |
| First Pestov91 Lean module (session `01Abcd4f`) | `8829513da` | 06:17:22 | 06:17:28 | – |
| Review notes N1–N6 applied as forward corrections | `a6a044212` | 06:29:22 | 06:29:24 | 06:29:29 |
| Palomar surface and witness assembly (session `01Abcd4f`) | `b490bf08d` | 06:53:34 | 06:53:36 | – |

- The first landing postdates the latest versions of both sources: Ozawa v2 (2004-05-10) and Pestov v8 (2008-08-04).
- The hypothesis-free Lean endpoint is not on main at `2d7d577ab`. Its time is added when it lands.
- No public post about this result appears in the repository records.

## 4. Credit

### 4.1 Evidence

**Trailers.**
- 28 commits since 2026-09-11 touch this result's nodes, artifacts or Lean files.
- Two of them are the tree wipe and restore of 2026-09-12 (`becc912bd`, `3f71a3a50`), which touched every path.
- All of the other 26 carry `Co-Authored-By: Claude Code <noreply@anthropic.com>`. None names Codex, GPT or OpenAI.
- Those 26 come from four sessions: `01HaPd2Y` (15), `01Abcd4f` (7), `01UM7nBy` (3), `01PWzwKN` (1).

**Models.**
- A trailer names a session, not a model, so the models come from the transcripts. Every session above has a local
  transcript, matched by its `bridge-session` record (`cse_<id>`) or its `remote_session_change` record.
- Assistant records carry one internal Claude model identifier, except where the table names another. This file does
  not print that identifier. Following the Bowen–Chapman entry of `formalization.yaml`, such runs are credited as
  "Claude (Anthropic)".
- Records whose model is `<synthetic>` are harness placeholders, not model output.

| role | lane | session / transcript | assistant records |
|---|---|---|---|
| chose the problem and briefed the lane | coordinator | `01HaPd2Y` / e26eab2c | 388 |
| **found and proved the construction** | `ex-kazhdan-simple-hyperlinear` | `01HaPd2Y` / subagent | 205 |
| found it independently; second LEF proof | `isk-hyperlinear-kazhdan` | `01UM7nBy` / fork in 829306b2 | 159 |
| first review | `ex-verify-groups` | `01HaPd2Y` / subagent | 370, plus 1 `<synthetic>` |
| novelty pass | `ex-novelty` | `01HaPd2Y` / subagent | 478 |
| second review, comparison, corrections, write-up | `ex-pestov91-harden` | `01HaPd2Y` / subagent | 139, plus 1 `<synthetic>` |
| recorded the question as a root (2026-09-12) | coordinator | `01PWzwKN` / 829306b2 | 2095, plus 4 `<synthetic>` |
| Lean modules on main so far | coordinator and subagents | `01Abcd4f` / 6dbfc571 | see below |
| Lean, this swarm | 19 `pc-*` lanes | `01HaPd2Y` / subagents | internal identifier only |

**The `01Abcd4f` Lean row.**
- The coordinator has 1992 records, plus 1 `<synthetic>`.
- `8829513da` was issued by subagent `p91-kazhdan`, whose records all carry `claude-opus-5`.
- The other six commits were issued by subagents carrying the internal identifier.

**Custom proof tool.** "Astra" occurs twice in the construction lane's transcript: once in injected instructions, once
in a quoted Bowen–Chapman credit decision. No tool call there uses a custom proof tool.

**Human input.** In that window the coordinator transcript holds one user message (02:08:46 UTC), a general mandate with
no mathematical content. The author directed the campaign.

### 4.2 Who did what

- **Mathematics:** Claude (Anthropic), lane `ex-kazhdan-simple-hyperlinear`. The `isk-hyperlinear-kazhdan` fork found
  the same group independently (Part 1 §2.4).
- **Review:** Claude (Anthropic).
  - `ex-verify-groups` and `ex-pestov91-harden` each re-derived the proof, before reading the other's review.
  - `ex-novelty` checked the literature.
- **Lean:** Claude Code fleets in sessions `01Abcd4f` and `01HaPd2Y`. So far that is Claude (Anthropic), plus Claude Opus 5
  (`claude-opus-5`) for one module. Recheck when the endpoint lands.

### 4.3 Literature inputs to acknowledge

| input | source |
|---|---|
| the question | Ozawa, arXiv:math/0306067 (2003); Pestov, arXiv:0804.3968, Open question 9.1 (v8) |
| property (T) of `EL_n(R)`, R finitely generated | Ershov–Jaikin-Zapirain, Invent. Math. 179 (2010), arXiv:0809.4095, Theorem 1.1 |
| periodic approximation giving LEF | Grigorchuk–Medynets, arXiv:1105.0719, Theorem 2.6 |
| simplicity of the ring | Brown–Clark–Farthing–Sims, arXiv:1204.3127 (complex); Clark–Edie-Michell, arXiv:1403.4684, Cor. 4.6; Steinberg, arXiv:1408.6014, Cor. 3.6 |
| nearest earlier object | Thom, arXiv:0810.2180, Theorem 1.4 |
| factorization property | Kirchberg, Math. Ann. 299 (1994), Theorem 1.1 |
| MF convention, the sentence S refutes, Prop. 3.19 | Dadarlat, arXiv:2007.12655v2 |
| LEF implies sofic implies hyperlinear | Elek–Szabó; Ceccherini-Silberstein–Coornaert, Cor. 7.5.11 |

## 5. Rows for `formalization.yaml`

These follow the format of the Bowen–Chapman entry. pc-integrate owns the file and aligns the wording with the landed
Lean statement.

A `sources:` entry:

```yaml
  - title: An infinite simple group with property (T) that is sofic and hyperlinear
    type: original-proof
    relationship: other
    contributors:
      - name: Claude (Anthropic)
        role: >-
          found the construction and its proof, and reviewed it
          independently twice
    note: >-
      The positive answer to Open Question 9.1 of Pestov's "Hyperlinear and
      sofic groups: a brief guide" (arXiv:0804.3968; numbered 8.1 in v1 of
      2008-04-24 and 9.1 in v8 of 2008-08-04), "Let G be an infinite simple
      group with Kazhdan's property (T). Can it be hyperlinear (sofic)?", is
      first presented in this project. Pestov credits the question to Ozawa,
      who asks it in arXiv:math/0306067 v1 of 2003-06-03 (Internat. J. Math.
      15 (2004)): "It is unknown whether there exists a simple property (T)
      group Γ which is hyperlinear." The witness is EL_3(LC(X, F_q) ⋊ Z)
      modulo its centre, for an infinite minimal subshift X. It was committed
      to this public repository on 2026-09-13 at 03:18:24 UTC (f375478c7),
      passed independent review at 03:48:55 UTC (0efeac410), was established
      in the research graph at 04:09:24 UTC (8b65f0932), and passed a second
      independent review at 05:56:33 UTC (badc66e2d). That postdates the
      latest versions of both sources, Ozawa's v2 of 2004-05-10 and Pestov's
      v8 of 2008-08-04. No earlier or independent answer was found in print;
      the latest expert list of known examples, Alekseev and Thom
      (arXiv:2608.05362, 2026), names no simple one.
```

An `automation.methods` entry:

```yaml
    - method: agent
      models: [Claude (Anthropic), Claude Opus 5]
      framework: Claude Code
      tool_setup: >-
        Claude Code agent fleets for the mathematics, its two independent
        reviews and the Lean development, with remote batch compilation.
```

An `automation.notes` paragraph:

```yaml
    The Pestov 9.1 problem was solved by Claude (Anthropic), in a Claude Code
    agent fleet under the author's direction. The construction first appears
    in the records of the lane that landed it, nine minutes after that lane
    was given the question, and a lane in a second session found the same
    group independently three minutes later. Two further lanes reviewed the
    proof independently. The Lean formalisation was produced by Claude
    (Anthropic) and Claude Opus 5 agents. No custom proof tool, Codex or GPT
    agent worked on that result.
```

A `review.notes` sentence:

```yaml
    Two independent reviews of the Pestov 9.1 mathematics, each re-deriving
    the proof, are recorded at
    research/artifacts/ex-review-groups-2026-09-12-part1.md and
    research/artifacts/ex-pestov91-second-review-2026-09-13.md; the priority
    and credit evidence is at
    research/artifacts/pestov91-priority-credit-2026-09-13.md.
```
