# Bell's free abelian circle-action theorem: primary-source audit (2026-08-30)

## Source and version

Jamie Bell, *Crossed product C-star algebras associated with non-minimal
actions on the circle*,
[arXiv:2604.18410v2](https://arxiv.org/abs/2604.18410v2), revised
2026-07-07 and listed as forthcoming in the *Journal of Operator Theory*.

The numbered result imported here is Theorem 3.14, also summarized as
Theorem A(iii).  Before this import, a search of the claim, route, artifact,
and notes corpus for the arXiv identifier, exact title, author, and theorem
wording found no Cairn representation of this result.

## Exact hypothesis match

| Cairn wording | Bell, Theorem 3.14 |
| --- | --- |
| `G` countably infinite | countably infinite |
| `G` discrete abelian | discrete abelian group |
| `G` acts freely on `T` | free action on the circle |
| `C(T) rtimes G` is quasidiagonal | literal conclusion |

The source writes the full crossed product.  Its preliminaries identify full
and reduced crossed products for amenable acting groups; abelian `G` is
amenable.  Thus the imported statement is valid for either convention
without changing any action hypothesis.

The paper's title emphasizes non-minimal actions, but Theorem 3.14 itself does
not assume non-minimality.  Its proof splits into the minimal case and the
non-minimal case.  In the latter it uses the extension

```text
0 -> J -> C(T) rtimes G -> C(Y) rtimes G -> 0,
J = direct_sum_i C_0(R) tensor K(l2(G)),
```

and the vanishing boundary map `K_1(C(Y) rtimes G) -> K_0(J)=0` to apply the
Brown--Dadarlat quasidiagonal-extension theorem.  This is exactly the
non-simple extension regime not covered merely by a faithful trace on the
ambient crossed product.

## Boundary against STW Problem XI

For `G=Z^d`, `d>=2`, Bell's theorem supplies an exact positive subclass of
`stw99-problem-xi-zd-crossed-stably-finite-qd`: every free circle action has a
quasidiagonal crossed product, without separately assuming stable finiteness.
It does not settle arbitrary compact metrisable coefficient spaces, actions
with stabilizers, or the AF-embeddability half.

That last boundary is source-explicit.  Remark 3.15 says Bell was unable to
verify AF embeddability for the non-minimal crossed products and records it as
the expected stronger statement.  Cairn therefore imports Theorem 3.14 only;
it does not infer AF embeddability from quasidiagonality and does not relabel
the universal STW root.
