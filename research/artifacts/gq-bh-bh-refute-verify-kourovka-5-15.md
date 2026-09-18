# Adversarial check: Kourovka 5.15 via KMS (`fp-rf-groups-with-non-primitive-recursive-word-problem`) (bh-refute, 2026-09-18)

This is a self-chosen rotation item: a named problem with no review on main.

Verdict: **PASS**.

## At source

- **Kourovka 21st ed.** (`gq/src/kourovka/21tkt.tex`, l.1177–1180), verbatim: "5.15. Do there exist finitely
  presented residually finite groups with recursive, but not primitive recursive, solution of the word
  problem? (F. B. Cannonito)". It is in the unsolved section (`\bmp`), with no comment.
- **KMS, arXiv:1204.6506v5** (`gq/src/kms/KMS-322.tex`), two statements:
  - `t:rfg` matches the node: "… the word problem in `G` is at least as hard as the membership problem in a given
    recursive set of natural numbers `Z` …".
  - The introduction theorem: "Let `f(n)` be a recursive function. Then there exists a residually finite finitely
    presented solvable group `G` such that for any finite presentation `⟨X ; R⟩` of `G` the time complexity of both
    'yes' and 'no' parts of the word problem are at least as high as `f(n)`."

## The argument

- **The short route: the node's Remark, which I recommend as the primary proof.** Take `f` to be Ackermann's
  function.
  - A primitive recursive characteristic function is computed by a Turing machine in primitive recursive time.
  - Every primitive recursive function is eventually below Ackermann.
  - So no presentation of `G` has a primitive recursive word problem.
  - The word problem is recursive, by McKinsey (finitely presented and residually finite).
  - This uses only the KMS intro theorem as printed.
- **The node's main route** diagonalizes against an enumeration of the primitive recursive functions to get a
  recursive `Z` that is not primitive recursive. It then needs the KMS reduction `m ↦ word pair` to be primitive
  recursive.
  - That is checked "by inspection". The words are iterated `*a_i` operations, with length `O(4^m)`.
  - It is correct, but it rests on reading KMS §4 definitions rather than on a stated KMS theorem.
  - The short route avoids this.
- **Independence of presentation** holds, since generator changes are primitive recursive substitutions.

## Lesson for general BH

Finitely presented residually finite groups already have word problems of every recursive complexity (KMS).
So Boone–Higman for f.p. residually finite groups forces finitely presented simple groups beyond every
recursive bound. That is the unconditional route to `fp-simple-groups-with-arbitrarily-complex-word-problem`
through `every-fp-rf-group-embeds-in-fp-self-similar-group`. The explicit Kourovka 7.19 also reduces to one
host question for one KMS group. The complexity test for any universal envelope is therefore already passed
on the input side; only a host able to absorb the KMS groups is missing.
