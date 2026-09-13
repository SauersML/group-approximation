
## 40. w7-hexagon-closing follow-up and route (767ec353f4)

Sources: the diff of `767ec353f4`, read in full. It changes:
- the artifact (blob `2531cb49`);
- the claim (blob `7cd9eb6b`);
- the entry on `binary-complement-corner-has-no-weakly-finite-image` (blob `2b207bda`);
- the new route `stage-models-cannot-close-the-leavitt-hexagon-proof` (blob `ba6d5b55`).

**Verdict: PASS.** The advisories of 38.5 are applied and no mathematical statement changed. One residual rename
remains (advisory 1 below), and there is one optional advisory on the status line.

- **Advisories of 38.5.**
  1. **The `C_n` clash.**
     - The centralizer is now `Z_n` in the Summary, Proposition 1.1, proof step (4) and Remark 1.2.
     - Residual: artifact line 119 (Corollary 2.4, last sentence) still reads `id ∉ π_n^0 C_n`, where the coset of
       Proposition 1.1 is meant. It should read `π_n^0 Z_n`, as the route already does. This is wording only: the
       coset is defined in Proposition 1.1, and the argument of 38.2 is unaffected.
  2. **The colimit.** The Summary and Remark 2.5 now say "the six-piece colimit `C_n` of finite pieces".
  3. **The ternary inputs.**
     - The route requires all three: the prime-field host, d-ary nonsoficity and projective nonsoficity.
     - Point 3 of the claim now lists `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`.
     - Section 8 of the artifact matches the route.
  4. **The rank bullet.** The entry now says `> 0` when `rk(σ(x_12(1)) − 1) > 0`, with the uniform `ε_p` over the
     Theorem 1.1 models. The corner claim stays OPEN.
  5. **The attribution.** Section 7 now says it is from memory and unchecked.

  The `distinct_from` entry for `leavitt-regular-atlas-asymptotic-permutation-cover` is added.
- **Route requirements, checked on main at `cbaef238a3`.** All ten nodes exist.
  - `steinberg-group-is-glued-over-the-permutohedron` (the (SPG2) source used in Section 34) is ESTABLISHED.
  - `leavitt-unit-group-finitely-presented` is ESTABLISHED (literature import).
  - `leavitt-unit-groups-have-no-unstable-k2-at-rank-three`, `graphs-of-locally-finite-groups-carry-regular-rank-models`
    and `monomial-rank-models-are-hamming-models` are ESTABLISHED.
  - `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` is ESTABLISHED, conditional on its import.
  - `binary-leavitt-unit-group-is-simple`, `openai-leavitt-unit-nonsofic`,
    `d-ary-leavitt-groups-nonsofic-over-finite-fields` and `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`
    each have a route, which I did not re-check.

  No requirement is missing: the argument of 38.1–38.4 uses exactly these, together with Elek–Szabó and Malcev
  (literature).
- **Route body.** It summarizes 38.1–38.4 correctly:
  - the letter and the coset `π_n^0 Z_n`;
  - no exact closing, through finite presentation, no finite quotients, Malcev, Łoś and per-stage colimits;
  - no rank-null closing, through the Hamming comparison, a kernel that is `1` or lies in `Z`, and Elek–Szabó;
  - the uniform `ε_p` from `rank(π − I) >= |supp π|/2` and relator error `4L/k`;
  - the ternary transfer.

  The lane wrote the verdict line in the verifier's format, citing Section 38. I replace it here with the line citing
  Sections 38 and 40.
- **Optional advisory on the status line.** The claim reads "**Proof verified.**". The escape-set claims (Section 39)
  use `**ESTABLISHED**` with their routes cited. A matching line here would say that the claim is ESTABLISHED, and
  for `p = 3` conditional on the import of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`.
- **Scope.** Unchanged from 38.5. Still OPEN: `binary-complement-corner-has-no-weakly-finite-image`,
  `binary-leavitt-unit-group-is-f2-linear-sofic`, the gate and Plan 1.
