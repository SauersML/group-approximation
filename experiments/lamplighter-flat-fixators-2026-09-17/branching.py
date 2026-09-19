"""Doubly branching a-words.  For a cyclically reduced word n in the A-letters,
Fix_b(n) and Fix_c(n) are the subtrees of T_b, T_c fixed by n (they contain the
base vertex).  The pruned sphere sizes are computed from the finite automaton
whose states are A-words of length |n| (push-through preserves length).
Ends(Fix) is infinite iff the pruned sphere sizes are unbounded.  Exact test
(ends_infinite): in the pruned automaton graph reachable from the start, the
path counts are unbounded iff some node lying on a cycle has >= 2 successors
(every successor is alive, so an extra edge off a cycle either stays in a
non-simple SCC or leaves it towards another cycle; both give unbounded growth,
and if every cyclic node has out-degree 1 the counts are eventually constant).
Usage: python3 branching.py sol.jsonl idx Lmax [F=A]"""
import sys
from lattice import load

def ends_infinite(C, lam, Y):
    succ, start = C.pruned(lam, Y)
    if start is None:
        return False
    reach = set(); todo = [start]
    while todo:
        v = todo.pop()
        if v not in reach:
            reach.add(v); todo += succ[v]
    def on_cycle(v):
        seen = set(); todo = list(succ[v])
        while todo:
            w = todo.pop()
            if w == v:
                return True
            if w not in seen:
                seen.add(w); todo += succ[w]
        return False
    return any(len(succ[v]) >= 2 and on_cycle(v) for v in reach)

def ends_class(C, lam, Y):
    G = C.fix_graph(lam, Y)
    depth = 2 * len(G) * (C.n[Y] + 1) + 4
    cnt = C.fix_counts(lam, Y, depth)
    if cnt[-1] == 0:
        return 'finite', cnt
    tail = cnt[len(cnt) // 2:]
    if max(tail) <= 2 and len(set(tail)) == 1:
        return f'{tail[0]}-ended', cnt
    return 'branching', cnt

def exact_class(C, lam, Y):
    succ, start = C.pruned(lam, Y)
    if start is None:
        return 'finite'
    return 'branching' if ends_infinite(C, lam, Y) else 'finitely-ended'


if __name__ == "__main__":
    path, idx, Lmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    F = sys.argv[4] if len(sys.argv) > 4 else 'A'
    others = [Y for Y in 'ABC' if Y != F]
    C = load(path, idx)
    stats = {}
    hits = []
    for L in range(1, Lmax + 1):
        for w in C.cyc_reduced(F, L):
            r = tuple(exact_class(C, w, Y) for Y in others)
            stats[(L,) + r] = stats.get((L,) + r, 0) + 1
            if r == ('branching', 'branching'):
                hits.append(w)
    for k in sorted(stats):
        print(k, stats[k])
    print("doubly branching words:", len(hits))
    for w in hits[:10]:
        print("  ", ''.join(f"{l[0].lower()}{l[1]}" for l in w))
