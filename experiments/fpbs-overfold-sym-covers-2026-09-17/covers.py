"""Exact test of (O) / (O|B) on finite covers of the Sym bases B_j.

B_j is the Cayley (right-regular) level of Sym(j+2) with a -> (0 1) and
b -> (0 1 ... j+1), as in fpbs-mal-sym-levels-embed-orbits-at-every-depth.
A k-sheeted cover is given by permutation voltages in Sym(k) on the a- and
b-edges of the Schreier graph of B_j, gauge-fixed to be trivial on a BFS
spanning tree.  For each transitive cover Q we check property (E) (every
component of Gamma_j(Q) maps injectively to Q), export the depth-j instance
(../fpbs-overfold-exact-c-2026-09-17/export.py) and run ./rel (copied from
experiments/fpbs-overfold-midn-2026-09-17/rel.c on main): an output line
VIOLATION is an exact certified counterexample deep_j < law_j.

Usage:
  python3 covers.py j k all  smax timeout workers REL        (k = 2 only)
  python3 covers.py j k rand count seed smax timeout workers REL
"""
import itertools
import os
import random
import re
import subprocess
import sys
import tempfile
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-exact-c-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-relative-rank-2026-09-17'))
from export import instance_text  # noqa: E402
from foldlib import depth_graphs  # noqa: E402
from struct_search import cayley  # noqa: E402


def base(j):
    d = j + 2
    al = tuple([1, 0] + list(range(2, d)))
    be = tuple(list(range(1, d)) + [0])
    return cayley(al, be, 10 ** 6)


def tree_edges(PA, PB):
    """BFS spanning tree of the Schreier graph, as a set of (gen, point)."""
    n = len(PA)
    seen, order, tree = {0}, [0], set()
    IA = {PA[x]: x for x in range(n)}
    IB = {PB[x]: x for x in range(n)}
    i = 0
    while i < len(order):
        p = order[i]
        i += 1
        for g, P, I in (('a', PA, IA), ('b', PB, IB)):
            q = P[p]
            if q not in seen:
                seen.add(q); order.append(q); tree.add((g, p))
            q = I[p]
            if q not in seen:
                seen.add(q); order.append(q); tree.add((g, q))
    return tree


def lift(PA, PB, volt, k):
    """volt[(g, p)] in Sym(k) as a tuple; cover point (p, s) -> p*k + s."""
    n = len(PA)
    CA, CB = [0] * (n * k), [0] * (n * k)
    for p in range(n):
        for s in range(k):
            CA[p * k + s] = PA[p] * k + volt[('a', p)][s]
            CB[p * k + s] = PB[p] * k + volt[('b', p)][s]
    return CA, CB


def transitive(PA, PB):
    n = len(PA)
    seen, st = {0}, [0]
    IA = {PA[x]: x for x in range(n)}
    IB = {PB[x]: x for x in range(n)}
    while st:
        p = st.pop()
        for q in (PA[p], PB[p], IA[p], IB[p]):
            if q not in seen:
                seen.add(q); st.append(q)
    return len(seen) == n


def canon(PA, PB):
    """Canonical form of a transitive F(a,b)-set: least BFS relabelling."""
    n = len(PA)
    IA = {PA[x]: x for x in range(n)}
    IB = {PB[x]: x for x in range(n)}
    best = None
    for s in range(n):
        lab, order = {s: 0}, [s]
        i = 0
        while i < len(order):
            p = order[i]
            i += 1
            for q in (PA[p], PB[p], IA[p], IB[p]):
                if q not in lab:
                    lab[q] = len(order); order.append(q)
        key = (tuple(lab[PA[p]] for p in order), tuple(lab[PB[p]] for p in order))
        if best is None or key < best:
            best = key
    return best


def property_E(PA, PB, j):
    """Every component of Gamma_j(Q) maps injectively to Q."""
    Gj, _, _ = depth_graphs(PA, PB, j)
    comp = [-1] * Gj.V
    for v0 in range(Gj.V):
        if comp[v0] >= 0:
            continue
        comp[v0] = v0
        st, pts = [v0], set()
        while st:
            v = st.pop()
            if Gj.over[v] in pts:
                return False
            pts.add(Gj.over[v])
            for w in Gj.nb[v].values():
                if comp[w] < 0:
                    comp[w] = v0; st.append(w)
    return True


def job(args):
    PA, PB, j, smax, timeout, rel = args
    tag = f'PA {PA} PB {PB}'
    if not property_E(PA, PB, j):
        return f'{tag} E-FAILS'
    fd, path = tempfile.mkstemp(suffix='.txt')
    with os.fdopen(fd, 'w') as f:
        f.write(instance_text(PA, PB, j))
    try:
        out = subprocess.run([rel, path, '0'], capture_output=True, text=True,
                             timeout=timeout).stdout
        m = re.search(r'law (\d+)', out)
        law = int(m.group(1)) if m else None
        if law is None or law <= 1:
            return f'{tag} law {law} trivial'
        tail = ''
        try:
            out = subprocess.run([rel, path, str(min(smax, law - 1))],
                                 capture_output=True, text=True,
                                 timeout=timeout).stdout
        except subprocess.TimeoutExpired as e:
            out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or '')
            tail = ' TIMEOUT'
        res = ' | '.join(ln for ln in out.splitlines()
                         if ln.startswith('s ') or ln.startswith('VIOLATION'))
        exact = 'EXACT' if law - 1 <= smax and not tail else f'partial s<={smax}'
        return f'{tag} law {law} {exact} :: {res}{tail}'
    except subprocess.TimeoutExpired:
        return f'{tag} law-timeout'
    finally:
        os.unlink(path)


def main():
    j, k, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    PA, PB = base(j)
    n = len(PA)
    free = sorted({(g, p) for g in 'ab' for p in range(n)} - tree_edges(PA, PB))
    perms = list(itertools.permutations(range(k)))
    ident = tuple(range(k))
    covers = []
    if mode == 'all':
        smax, timeout, workers, rel = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
        for choice in itertools.product(perms, repeat=len(free)):
            volt = {(g, p): ident for g in 'ab' for p in range(n)}
            volt.update(zip(free, choice))
            covers.append(lift(PA, PB, volt, k))
    else:
        count, seed = int(sys.argv[4]), int(sys.argv[5])
        smax, timeout, workers, rel = int(sys.argv[6]), int(sys.argv[7]), int(sys.argv[8]), sys.argv[9]
        rng = random.Random(seed)
        while len(covers) < count:
            volt = {(g, p): ident for g in 'ab' for p in range(n)}
            for e in free:
                volt[e] = rng.choice(perms)
            covers.append(lift(PA, PB, volt, k))
    covers = [c for c in covers if transitive(*c)]
    if '--dedupe' in sys.argv:
        uniq = {}
        for c in covers:
            uniq.setdefault(canon(*c), c)
        covers = list(uniq.values())
    if '--minlaw' in sys.argv:
        # rerun only the covers listed in a previous output with law >= minlaw
        i = sys.argv.index('--minlaw')
        minlaw, prev = int(sys.argv[i + 1]), sys.argv[i + 2]
        want = set()
        for ln in open(prev):
            m = re.match(r'PA (\[.*?\]) PB (\[.*?\]) law (\d+)', ln)
            if m and int(m.group(3)) >= minlaw:
                want.add(canon(eval(m.group(1)), eval(m.group(2))))
        covers = [c for c in covers if canon(*c) in want]
    print(f'# covers j {j} k {k} mode {mode} base n {n} free {len(free)} '
          f'transitive covers {len(covers)} smax {smax} timeout {timeout}', flush=True)
    print(f'# base E holds: {property_E(PA, PB, j)}', flush=True)
    with Pool(workers) as pool:
        for line in pool.imap_unordered(job, [(a, b, j, smax, timeout, rel) for a, b in covers]):
            print(line, flush=True)


if __name__ == '__main__':
    main()
