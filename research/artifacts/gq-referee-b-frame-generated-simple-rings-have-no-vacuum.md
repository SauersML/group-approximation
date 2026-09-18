# Referee report (gq-referee-b, citation/scope lens): frame-generated simple rings have no vacuum

**Reviewed.** Both from lane gq-infinite-primes, a863176f1, read on origin/main (eb9a7edce):
- `frame-generated-simple-rings-have-no-vacuum` and its `-proof`;
- Attempts 9 and 10 of `fp-simple-resolvent-ring-with-divisible-unit-class`.

**Verdict: PASS.** Items 1–4 are correct. There is no external citation; the Toeplitz/compacts sentence is
motivation only. Both internal inputs are used within their range. Three scope fixes, W1–W3, all in the Consequences
section.

## Internal inputs

- **Item 1 of the isometric-frame node, over any `B`.** Its proof uses only `st = 1` and `ts = p`, so `[1_R] = [p]_R`
  for any unital `B`. Here `[p]_R` is the image of `φ_*[1_B]`, because `φ : B → pM_k(B)p` is unital. **Match.**
- **The `R_L` presentation.** Per `leavitt-resolvent-ring-is-fp-simple-of-char-zero`, it has generators
  `s_i, t_i, N, A` and relations including `N s_1 = s_1(N+1)`, `N s_2 = 0` and `A = (N+1)^(-1)`.
  - `φ(f) = diag(f(N+1), f(0))`: resolvents are transported as `(N+c)^(-1) s_1 = s_1 (N+1+c)^(-1)` and
    `(N+c)^(-1) s_2 = c^(-1) s_2`.
  - `φ` is injective, since `N ↦ N+1` is an automorphism of `Q(N)` preserving `B`.
  - `p = I_2`.
  - (T2) follows from (T1) once `st = 1`.
  - **Match.**

## Steps checked

- **Item 1.**
  - `φ(b)φ(b') = tb(st)b's = tbsφ(b') = tbb's`.
  - `be = sφ(b)t = eb`.
  - `qs = 0` and `tq = 0`.
  - The normal form `s_α b t_β` comes from the rewriting rules `b s_i = Σ_j s_j φ(b)_(ji)` and
    `t_i b = Σ_j φ(b)_(ij) t_j`.
  - The Gram recursion is `P^(m+1)_((β,j),(α,i)) = φ(P^(m)_(βα))_(ji)`.
- **Item 2.**
  - `RqR = span{s_α q b t_δ}`.
  - `E_m s_α = s_α` by induction, using `e s_j = s_j` and `eb = be`.
  - `q t_β s_α q = δ_(|β||α|) P q`, so the `G_m` are orthogonal idempotents.
  - *Truncation.* If `1 = GyG` then `G = 1`. So `s_α = G s_α = 0` for `|α| = n+1`.
  - With `φ` injective, `P^(n+1) = 0` descends to `p = 0`, and then `s = t = 0`. Correct.
- **Item 3.**
  - `ker φ` is a proper ideal of a simple `B`.
  - Directed unions of simple rings along unital maps are simple.
  - If `φ` is injective and `B ≠ 0`, then `p = φ(1) ≠ 0` automatically. So `RqR = R` is impossible, and a simple `R`
    has `q = 0`.
- **Item 4.** Concatenating the frames is correct.

## Scope

- **W1 ("A nonzero full vacuum needs generators outside the base and the frame").** This is correct only with an
  injective left action `φ`, for instance `B` simple. Without injectivity, item 2 gives only `s_α = 0` for long words.
  - Attempt 9 carries the hypothesis ("the left action is injective"), but the node's Consequences bullet drops it.
    Add it there.
- **W2 ("Filling a vacuum with further isometries ... falls under the isometric-frame dichotomy").** The dichotomy
  needs more than item 1 gives.
  - It needs a matricial base, and a grading when the index is `1`.
  - Over a general `B`, such as `R_L`'s `Q[N][(N+c)^(-1)]`, only item 1 applies: `[1] = φ_*[1]`. That already gives
    `[1] = 0` for `R_L`.
  - Suggested wording: "falls under item 1 of the isometric-frame node, and over matricial bases under its
    dichotomy".
- **W3 ("That is the gate's remaining room").** This says the only room is `K_0(B)` of infinite rank. Two
  corrections:
  - The finite-rank case is not closed. It is the parked multi-type gap (gate Attempt 10), which is open.
  - The whole "Where room remains" paragraph depends on the Pimsner sequence (P) of
    `resolvent-register-units-give-rational-symbols`. Say so explicitly.

  Attempt 9 states it correctly: "It must have infinite rank, as in Attempt 1, or face the gap below." Use that
  wording in the node.

## The requested scope sentences

- **"A nonzero full vacuum needs generators outside the base and the frame".** Correct with W1's qualifier.
- **"The room must come from `K_0(B)` of infinite rank".** It does not follow in that form. It is correct as Attempt 9
  words it, with the alternative "or face the gap below" and conditional on (P). W3 aligns the node with it.
- **Attempt 10.** Correctly parked and labelled conditional on (P). Its open question, whether the lifts lie in the
  image of `K_2(N, R)`, is stated accurately.
