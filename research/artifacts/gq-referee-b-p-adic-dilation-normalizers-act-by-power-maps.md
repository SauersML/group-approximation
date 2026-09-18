# Referee report (gq-referee-b, citation lens): p-adic dilation normalizers act by power maps

**Reviewed.** `p-adic-dilation-normalizers-act-by-power-maps` and its `-proof` (lane gq-ring-fp-simple, dee7ac8ab), read
on origin/main.

**Verdict: PASS.** The p-adic six exponentials theorem is established, and its hypotheses hold at the point of use. I
pinned it to a primary source, read at source (below). The scope claim that the two-relation chain needs the
four exponentials case, which is open, is confirmed by two sources.

## The p-adic six exponentials theorem, pinned

**Source.** J.-P. Serre, *Dépendance d'exponentielles p-adiques*, Séminaire Delange–Pisot–Poitou (Théorie des nombres),
7e année, 1965/66, exposé n° 15, pp. 15-01 to 15-14 (28 March 1966). Open access on Numdam: `SDPP_1965-1966__7_2_A4_0`.
I read it at source, pages 15-01 to 15-03.

**Setting, §1.1, p. 15-01.**
- `k` is complete for a real valuation `v`, of characteristic 0 and residue characteristic `p`.
- `E` is the domain of convergence of `exp`: "l'ensemble des z ∈ k tels que v(z) > v(p)/(p − 1)".

**Statement, p. 15-02, verbatim.**
> "On se donne : (i) Un sous-groupe A de k, libre de rang fini a ≥ 2 sur Z. (ii) Des éléments b_i (i = 1, ..., b) de
> k. On pose : e_i(z) = exp(b_i z). On suppose que les e_i convergent sur A, i. e. que b_i A ⊂ E pour tout i [...]
> THÉORÈME 1. – Supposons que tous les e_i(x), x ∈ A, 1 ≤ i ≤ b, soient algébriques sur Q. Alors, si b > a/(a − 1),
> les b_i sont linéairement dépendants sur Q."

**Remark 1°, same page.**
> "Si a = 2, le théorème s'applique pour b ≥ 3 ; si a ≥ 3, il s'applique pour b ≥ 2. On ignore ce qui se passe pour
> a = b = 2."

**Attribution.** The introduction, p. 15-01, credits Lang ("Sa démonstration vaut aussi bien dans le cas réel ou
complexe que dans le cas p-adique"), and §1 reproduces Lang's proof in the p-adic case. So cite:
- Serre, Théorème 1, as the p-adic statement;
- Lang 1966 for the method.

The lane's pointer to Waldschmidt 2000 without a number can be dropped.

**Hypothesis match in Step 4.**

| Serre | Step 4 | Check |
|---|---|---|
| `k` | `Q_p` | Complete, characteristic 0, residue characteristic `p`. |
| `A`, free of rank 3 | `Z y_0 + Z y_1 + Z y_2` with `y_j = log(u_j^M)` | `log` is an injective homomorphism on the torsion-free `W ⊆ E`, and the `u_j` are multiplicatively independent. So the `y_j` are `Q`-independent, and `a = 3`. |
| `b_1, b_2` | `1, α` | `b = 2 > 3/2`. |
| `b_i A ⊂ E` | `A`, `αA` | `A ⊆ p^2 Z_p` (`8Z_2` when `p = 2`), and `αA ⊆ log(E)` because `α y_j = log β(u_j^M)`. Both satisfy `v > v(p)/(p−1)`. |
| `e_i(x)` algebraic | | `e_1(Σ n_j y_j) = ∏ u_j^(M n_j)` and `e_2(Σ n_j y_j) = ∏ β(u_j)^(M n_j)` are rational. |

The conclusion is that `1, α` are `Q`-dependent, that is, `α ∈ Q`, as used.

## Scope of item 3 (confirmed)

**The chain case.** For `q_0 → q_1 → q_2`, Steps 1–3 give `y_1 = α y_0` and `y_2 = α y_1`. Excluding irrational `α`
here is exactly Serre's case `a = b = 2`. His Remark 1° says: "On ignore ce qui se passe pour a = b = 2".

**It is still open.** M. Waldschmidt, *The Four Exponentials Problem and the Schanuel Conjecture* (preprint dated
26 May 2022, Festschrift C. Byrne), abstract: "These questions are open both in the complex case and in the p-adic
case."

**The 2-cycle case.** It is correctly handled without transcendence: `α^2 = 1`.

**The single relation.** It is correctly left unexcluded.

## Other steps (checked)

- **Step 1.** Injectivity of `c` gives injectivity of `β`, and `c(0) = 0`.
- **Step 2.** `β(u) = c(u z_0)/c(z_0)` is continuous, and it extends to the closure. `W` is open in the compact
  `Q̄_0`, so `[Q_0 : Q_1] < ∞`.
- **Step 3.** `log(W) = p^k Z_p`, and a continuous additive map is `Z_p`-linear. So `α ∈ Q_p`.
- **Step 5.** `log` is injective on `E`, and unique factorization gives `β(q) = ± q^(a/b)`.
  - Under the three relations `β` is the shift on the rank-three group `⟨q_0, q_1, q_2⟩`.
  - The relations hold on a ball around 0, which is all that is used, so the argument covers germs.

## Consequences (scope)

- "Cannot obtain infinitely many `d_q` as `c^n d_(q_0) c^(-n)`" holds because such an orbit supplies three distinct
  primes `q_0, q_1, q_2` with `β(q_i) = q_(i+1)`.
- "Nor from any element normalizing a rank-three group of dilations" is accurate. Such an element sends `d_q` to
  `d_(±q^(a/b))`, so it produces no new primes.
