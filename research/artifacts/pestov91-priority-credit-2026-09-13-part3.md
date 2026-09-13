# Pestov 9.1: priority, timeline and credit, part 3: the formalization (2026-09-13)

Lane `pc-priority-credit`, main at `517188c31`.
- Part 1 covers §0–§2: who asked first, earlier answers, parallel discovery.
- Part 2 covers §3–§5: the discovery timeline and credit.
- This part covers §6, the formalization timeline and credit trail, and §7, the final rows. §7 supersedes Part 2 §5.

Evidence standard as in Part 1. A commit's issuer is the transcript whose tool call carries the commit subject. The
internal model identifier is not printed.

## 6. Formalization

### 6.1 Campaigns

**fz swarm.** Coordinator session 6dbfc571, trailer `01Abcd4fUYaLXqZuLgyTuRf3`. It owns the Pestov 9.1 formalization
and its Palomar integration.
- **User order, 05:42:08 UTC:** "get massive agne tswar m to formaliz everything we have discovered". The pasted status
  names Pestov 9.1 as "The biggest live result".
- **User order, 06:16:24 UTC:** stop using Claude Opus 5 agents. The order is paraphrased here because its wording names
  the internal identifier.
- **First wave.** Eleven `p91-*` lanes started 06:07:34–06:09:16 UTC. Their records carry only `claude-opus-5`.
- **Second wave.** The same lane names were relaunched 06:20:36–06:21:23 UTC. Their records carry only the internal
  identifier.

**PC swarm.** This session, e26eab2c, trailer `01HaPd2YJDm2EQdhXtMepr2X`: 19 `pc-*` lanes, all with the internal
identifier.

### 6.2 Timeline (UTC)

Times are GitHub push events where fetched, otherwise the first check-run start (`cr`). Author dates are converted from
-05:00.

| commit | content | author | GitHub | issuer (session) | model record |
|---|---|---|---|---|---|
| `8829513da` | property (T) for `EL_n` of finitely generated rings modulo the centre (`Kazhdan.lean`) | 06:17:22 | 06:17:28 | `p91-kazhdan`, first wave (01Abcd4f) | `claude-opus-5` |
| `5f444f257` | property (T) for the witness, complex-unitary form | 06:32:09 | 06:32:16 | `p91-kazhdan` (01Abcd4f) | internal |
| `e3200c6c2` | LEF groups are hyperlinear | 06:37:06 | 06:37:11 | `p91-lef-hyperlinear` (01Abcd4f) | internal |
| `03c0f1a39` | centre of `EL_n(R)`; `EL_n(R)/Z` infinite | 06:40:21 | 06:40:23 | `p91-infinite-centre` (01Abcd4f) | internal |
| `f3b198106` | `EL_3(LC(X,K) ⋊ Z)/Z` infinite, no hypotheses | 06:53:28 | 06:53:30 | `p91-infinite-centre` (01Abcd4f) | internal |
| `b490bf08d` | Palomar surface and witness assembly | 06:53:34 | 06:53:36 | `p91-palomar` (01Abcd4f) | internal |
| `89448ad3b` | `LC(X,K) ⋊ Z` simple for a free minimal system | 06:55:09 | 06:55:11 | `p91-ring-simple` (01Abcd4f) | internal |
| `8f4501419` | assembly takes infiniteness as a hypothesis; crossed-product and `EL_3` forms | 07:03:38 | cr 07:03:45 | `p91-palomar` (01Abcd4f) | internal |
| `d946a358a` | `EL_n(R)` simple from ring simplicity and split annihilators | 07:06:13 | cr 07:06:19 | `p91-alt` (01Abcd4f) | internal |
| `21147debe` | crossed product `A ⋊ Z` defined, finitely generated | 07:14:30 | cr 07:14:36 | `p91-ring-fg` (01Abcd4f) | internal |
| `764023101` | Pestov 9.1 and FFWZ 5.8 Palomar pairs gated as pending | 07:22:49 | cr 07:22:57 | `fz-integrate` (01Abcd4f) | internal |
| `622570981` | `LC(X, ZMod 2) ⋊ ℤ` finitely generated | 07:29:58 | 07:29:59 | `pc-ring-fg` (01HaPd2Y) | internal |
| `8443d297e` | central elements of `LC(X, F_2) ⋊ Z` are 0 and 1 | 07:36:39 | 07:36:41 | `p91-palomar` (01Abcd4f) | internal |
| `4a9981630` | Pestov 9.1 literature in `formalization.yaml` | 07:46:36 | 07:46:37 | `pc-integrate` (01HaPd2Y) | internal |
| `c3cfee844` | `EL_n(R)/Z` simple for simple rings with local annihilation | 07:54:02 | 07:54:04 | `p91-simple-mod-centre` (01Abcd4f) | internal |

**State at `517188c31`.**
- **Modules.** 13 modules under `GroupApproximation/Pestov91/`. Seven are root-imported: Assembly, CrossedProductFG,
  KazhdanUnitary, LEFHyperlinear, RingFinitelyGenerated, RingSimple, SplitSimplicity.
- **Palomar.** The surface is present, gated as pending since `764023101`. The comparator workflow's header comment says
  `Palomar/Pestov91Solution.lean` still assumes an infinite simple LEF group. So the surface is conditional, and the
  hypothesis-free endpoint has not landed.
- **The Opus module.** `Kazhdan.lean` on the tip is still the blob of `8829513da`, and `Assembly.lean` and
  `KazhdanUnitary.lean` import it. So the one Claude Opus 5 module is in the chain today.

### 6.3 Credit trail

- **Trailers.** All 15 commits above carry `Co-Authored-By: Claude Code <noreply@anthropic.com>`. 12 are session
  `01Abcd4f` and 3 are `01HaPd2Y`. None names Codex, GPT or OpenAI.
- **Issuers.** Only `p91-kazhdan`'s first wave carries `claude-opus-5`. Every other issuer carries the internal
  identifier, credited as Claude (Anthropic). Of the first wave, only `8829513da` landed.
- **Human direction.** The two user orders in 6dbfc571, quoted in §6.1.
- **Recheck when the endpoint lands.**
  - Modules and prose landed after `517188c31`.
  - Whether `Kazhdan.lean` has been replaced. If so, Claude Opus 5 leaves the credit.

## 7. Final rows

The file is `research/artifacts/pestov91-priority-credit-2026-09-13-rows.yaml`, also at
`$PC/lanes/pc-priority-credit/pestov91-credit.yaml`. It holds four things:
- a `sources:` original-proof row with the UTC discovery timeline, placeholders for the Lean endpoint and the Palomar
  surface, the latest version of every source checked, and the bound of that check;
- an `automation.methods` entry: `models: [Claude (Anthropic), Claude Opus 5]`, `framework: Claude Code`;
- an `automation.notes` paragraph;
- a three-sentence README credit paragraph.

**Astra or Claude?** The README and yaml precedent reads "The problem was solved by Astra, using a custom proof tool".
It does not apply here. No custom proof tool appears in the records; the construction first appears in the reasoning of
lane `ex-kazhdan-simple-hyperlinear` (Part 2 §4.1). The rows say "solved by Claude (Anthropic) under the author's
direction, with no custom proof tool".
