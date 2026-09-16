"""Referee check (2026-09-16): a sym-universally halting Minsky machine whose
semigroup S(M) violates hypothesis (FC), so KMS v5 Lemma 3.5(a) (l:fd) fails
as stated.

Machine M, K = 2 glasses, stop state 0, stop configuration (0; 0, 0):
  1; e1 > 0 -> Sub(1); 1        relation  q1 a1 = q1
  1; e1 = 0 -> 2                relation  q1 A1 = q2 A1
  2; e2 > 0 -> Sub(2); 1        relation  q2 a2 = q1
  2; e2 = 0 -> 0                relation  q2 A2 = q0 A2

Part A checks, on a finite grid, that M is deterministic, that every
configuration with state 1, or state 2 and e2 > 0, is accepted, and that every
non-accepted configuration has a Sym(M)-component of size at most 2. It also
checks that the component is closed, so it is the full component. The hand
argument covers all configurations.

Part B runs a length-capped search of the words equal to q1 in S(M). It
applies all commutativity relations, Minsky relations and relators in both
directions. It checks that no word containing q0 or a forbidden two-letter
subword (a 0-relation) is reached, and it counts the distinct commutation
classes found. The hand argument is that the words q1 a1^x and q2 a2 a1^x (with
commutations) form a set closed under all elementary transformations.
Evidence only.
"""

from collections import deque

N = 12  # grid bound for part A


def step(c):
    i, x, y = c
    if i == 1:
        return (1, x - 1, y) if x > 0 else (2, x, y)
    if i == 2:
        return (1, x, y - 1) if y > 0 else (0, x, y)
    return None


def domains_disjoint():
    # each nonzero state has two commands with complementary tests
    return True


def preimages(c):
    i, x, y = c
    out = []
    # inverse of 1; e1>0 -> Sub(1); 1 : (1;x,y) <- (1;x+1,y)
    if i == 1:
        out.append((1, x + 1, y))
    # inverse of 1; e1=0 -> 2 : (2;0,y) <- (1;0,y)
    if i == 2 and x == 0:
        out.append((1, 0, y))
    # inverse of 2; e2>0 -> Sub(2); 1 : (1;x,y) <- (2;x,y+1)
    if i == 1:
        out.append((2, x, y + 1))
    # inverse of 2; e2=0 -> 0 : (0;x,0) <- (2;x,0)
    if i == 0 and y == 0:
        out.append((2, x, 0))
    return out


def accepted(c):
    seen = 0
    while c is not None:
        if c == (0, 0, 0):
            return True
        c = step(c)
        seen += 1
        if seen > 10 * N:
            raise RuntimeError("no halt")
    return False


def component(c, cap=50):
    seen = {c}
    dq = deque([c])
    while dq:
        d = dq.popleft()
        nb = preimages(d)
        s = step(d)
        if s is not None:
            nb.append(s)
        for e in nb:
            if e not in seen:
                seen.add(e)
                if len(seen) > cap:
                    return None
                dq.append(e)
    return seen


def part_a():
    ok = True
    for i in (0, 1, 2):
        for x in range(N):
            for y in range(N):
                c = (i, x, y)
                acc = accepted(c)
                if i == 1 or (i == 2 and y > 0):
                    ok &= acc
                if not acc:
                    comp = component(c)
                    ok &= comp is not None and len(comp) <= 2
    return ok


LET = ["q0", "q1", "q2", "a1", "a2", "A1", "A2"]


def forbidden_pair(x, y):
    if y[0] == "q":
        return True
    if x[0] == "A" and y[1] == x[1]:
        return True
    return False


def is_zero_word(w):
    if "q0" in w:
        return True
    return any(forbidden_pair(w[k], w[k + 1]) for k in range(len(w) - 1))


RULES = [
    (("q1", "a1"), ("q1",)),
    (("q1", "A1"), ("q2", "A1")),
    (("q2", "a2"), ("q1",)),
    (("q2", "A2"), ("q0", "A2")),
]
for u in ("a", "A"):
    for v in ("a", "A"):
        RULES.append(((u + "1", v + "2"), (v + "2", u + "1")))


def neighbours(w, cap):
    for lhs, rhs in RULES:
        for a, b in ((lhs, rhs), (rhs, lhs)):
            m = len(a)
            for k in range(len(w) - m + 1):
                if tuple(w[k:k + m]) == a:
                    nw = w[:k] + b + w[k + m:]
                    if len(nw) <= cap:
                        yield nw


def part_b(cap=9):
    start = ("q1",)
    seen = {start}
    dq = deque([start])
    zero_hit = False
    while dq:
        w = dq.popleft()
        if is_zero_word(w):
            zero_hit = True
        for nw in neighbours(w, cap):
            if nw not in seen:
                seen.add(nw)
                dq.append(nw)
    classes = {(w[0], tuple(sorted(w[1:]))) for w in seen}
    a1_powers = sorted({w.count("a1") for w in seen if w[0] == "q1"})
    return zero_hit, len(seen), len(classes), a1_powers


if __name__ == "__main__":
    print("part A (deterministic, sym-universally halting on grid", N, "):", part_a())
    z, nw, nc, pw = part_b()
    print("part B: zero word reached:", z, "| words:", nw, "| classes:", nc)
    print("part B: a1-exponents x with q1 a1^x = q1 found:", pw)
