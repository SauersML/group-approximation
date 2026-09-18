#!/usr/bin/env python3
"""Driver for binary_hier.py (lane bh-free-18): trace, orbit statistics, exhaustive certificate, fill search.

  python3 bh_run.py trace STATE STEPS [SEED]     space-time diagram on a zero tape (SEED: cells 'i:c,...')
  python3 bh_run.py orbit STEPS                  Y statistics from every state on the zero tape
  python3 bh_run.py cert [FILL]                  R/E/T/C/P/P-1/I certificate (FILL = 15 digits: pi0 pi1 pi2)
  python3 bh_run.py search NPROC                 all fills with pi1 = pi2, filters in order, first failure only
"""
import sys
import time
from itertools import permutations
import binary_hier as B

L = 20001


def zero_cfg(state, seed=""):
    t = [0] * L
    h = L // 2
    for item in filter(None, seed.split(",")):
        i, c = item.split(":")
        t[h + int(i)] = int(c)
    return B.Cfg(t, h, state, 2)


def show(c, lo, hi):
    out = []
    for i in range(lo, hi + 1):
        ch = ".ab"[c.t[i]]
        out.append("[" + ch + "]" if i == c.h else " " + ch + " ")
    return "".join(out)


def trace(state, steps, seed=""):
    M = B.machine(B.DEFAULT)
    c = zero_cfg(state, seed)
    h0 = c.h
    for n in range(steps):
        if c.ph == 2:
            y = "Y" if B.inY(c, {}) else " "
            a = "A" if B.inA(c, {}) else " "
            print("%5d %s%s %-3s %4d %s" % (n, y, a, c.s, c.h - h0, show(c, h0 - 14, h0 + 14)))
        B.F(M["tab"], c, {})


def orbit(steps, fill=None):
    M = B.machine(fill or B.DEFAULT)
    for q in B.NAMES:
        c = zero_cfg(q)
        h0 = c.h
        last = 0
        ny = 0
        gap = 0
        lo = hi = 0
        rep = []
        nxt = 1
        for n in range(1, steps + 1):
            B.F(M["tab"], c, {})
            lo, hi = min(lo, c.h - h0), max(hi, c.h - h0)
            if c.h < 5 or c.h > L - 6:
                rep.append("EDGE at %d" % n)
                break
            if B.inY(c, {}):
                gap = max(gap, n - last)
                last = n
                ny += 1
                if ny == nxt:
                    rep.append("Y=%d t=%d gap=%d range=[%d,%d]" % (ny, n, gap, lo, hi))
                    nxt *= 2
        print("%s: Y=%d maxgap=%d range=[%d,%d]" % (q, ny, gap, lo, hi))
        for r in rep:
            print("    " + r)


def body_rev(M):
    def body(s, ph, asg):
        c = B.fresh(s, ph)
        c0 = c.copy()
        B.F(M["tab"], c, asg)
        B.Finv(M["tab"], M["inv"], c, asg)
        if not B.same(c, c0, asg):
            return "Finv F != id"
        B.Finv(M["tab"], M["inv"], c, asg)
        B.F(M["tab"], c, asg)
        return B.same(c, c0, asg) or "F Finv != id"
    return body


CHECKS = [("R", B.ALL, body_rev), ("E", B.ALL, B.body_entry), ("T", B.PH2, B.body_tower),
          ("C", B.PH2, B.body_cover), ("P", B.PH2, B.body_phi), ("P-1", B.PH2, B.body_phiinv),
          ("I", B.PH2, B.body_identity)]


def parse_fill(s):
    d = [int(x) for x in s]
    return {0: tuple(d[0:5]), 1: tuple(d[5:10]), 2: tuple(d[10:15])}


def cert(fill, stop=False, verbose=True):
    try:
        M = B.machine(fill)
    except B.Fail as e:
        return "build: %s" % e
    B.STATS["entry"] = B.STATS["ret"] = 0
    for name, sts, mk in CHECKS:
        leaves, fails, first = B.exhaust(sts, mk(M), stop=stop)
        if verbose:
            print("  %-4s leaves=%-7d fails=%-6d %s" % (name, leaves, fails, first[:2] if fails else "PASS"))
        if fails:
            return "%s fails=%d first=%s" % (name, fails, first[:1])
    if verbose:
        print("  max entry %d, max return %d" % (B.STATS["entry"], B.STATS["ret"]))
    return True


def job(pp):
    p0, p1 = pp
    fill = {0: p0, 1: p1, 2: p1}
    r = cert(fill, stop=True, verbose=False)
    return (p0, p1, r if r is True else r.split(" ")[0])


def search(nproc):
    from multiprocessing import Pool
    from collections import Counter
    perms = list(permutations(range(5)))
    jobs = [(a, b) for a in perms for b in perms]
    cnt = Counter()
    passes = []
    t0 = time.time()
    with Pool(nproc) as pool:
        for i, (p0, p1, r) in enumerate(pool.imap_unordered(job, jobs, chunksize=20)):
            cnt[r] += 1
            if r is True:
                passes.append((p0, p1))
            if i % 2000 == 0:
                print("  %d/%d %.0fs %s" % (i, len(jobs), time.time() - t0, dict(cnt)), flush=True)
    print("DONE", dict(cnt), "%.0fs" % (time.time() - t0))
    for p in passes[:50]:
        print("PASS", p)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "trace":
        trace(a[1], int(a[2]), a[3] if len(a) > 3 else "")
    elif a[0] == "orbit":
        orbit(int(a[1]))
    elif a[0] == "cert":
        f = parse_fill(a[1]) if len(a) > 1 else B.DEFAULT
        t0 = time.time()
        print("cert", a[1] if len(a) > 1 else "default", cert(f), "%.1fs" % (time.time() - t0))
    elif a[0] == "search":
        search(int(a[1]))


def oid(steps, state="A>", fill=None):
    """Concrete checks along the zero-tape orbit: tower alternation and phi U^2 = U phi at each y in A."""
    M = B.machine(fill or B.DEFAULT)
    c = zero_cfg(state)
    ok = bad = 0
    firsts = []
    pattern = []
    for n in range(steps):
        B.F(M["tab"], c, {})
        if B.inY(c, {}):
            a = B.inA(c, {})
            if len(pattern) < 60:
                pattern.append("A" if a else "-")
            if a:
                try:
                    lhs = c.copy()
                    B.U(M, lhs, {})
                    B.U(M, lhs, {})
                    B.phi(lhs, {})
                    rhs = c.copy()
                    B.phi(rhs, {})
                    B.U(M, rhs, {})
                    good = B.same(lhs, rhs, {})
                except B.Fail as e:
                    good = False
                    rhs = lhs = None
                if good:
                    ok += 1
                else:
                    bad += 1
                    if len(firsts) < 4:
                        h = c.h
                        firsts.append("n=%d %s %s" % (n, c.s, show(c, h - 8, h + 8)))
    print("oid %s: tower pattern %s" % (state, "".join(pattern)))
    print("identity ok=%d bad=%d" % (ok, bad))
    for f in firsts:
        print("  BAD " + f)


if __name__ == "__main__" and sys.argv[1] == "oid":
    oid(int(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else "A>")
if __name__ == "__main__" and sys.argv[1] == "certall":
    M = B.machine(B.DEFAULT)
    for name, sts, mk in CHECKS:
        leaves, fails, first = B.exhaust(sts, mk(M), stop=False)
        print("  %-4s leaves=%-7d fails=%-6d %s" % (name, leaves, fails, first[:3] if fails else "PASS"))


def used_entries(M, s, ph, asg, nsteps=120):
    """Replay a configuration; return the list of reading-rule inputs used, marked spec/fill."""
    c = B.fresh(s, ph)
    used = []
    for n in range(nsteps):
      try:
        if c.ph == 1:
            q = c.s
            cc = B.val(c, c.h, asg)
            mq = q if q in B.GROUP_R else B.mir_state(q)
            key = (mq, cc)
            if key in (("T<", 0), ("S>", 2)):
                nb = B.val(c, c.h + 1 if q in B.GROUP_R else c.h - 1, asg)
                spec = (key == ("T<", 0) and nb != 0) or (key == ("S>", 2) and nb == 0)
            else:
                spec = key in B.SPEC_R
            used.append((q, cc, "spec" if spec else "FILL"))
        B.F(M["tab"], c, asg)
      except (B.Need, B.Fail):
        break
    return used


if __name__ == "__main__" and sys.argv[1] == "why":
    M = B.machine(B.DEFAULT)
    fails = []

    def body(s, ph, asg):
        r = B.body_entry(M)(s, ph, asg)
        return r
    # collect all E failures
    for (s, ph) in B.ALL:
        stack = [{}]
        while stack:
            asg = stack.pop()
            try:
                body(s, ph, asg)
            except B.Need as e:
                for cval in range(3):
                    a2 = dict(asg)
                    a2[e.k] = cval
                    stack.append(a2)
                continue
            except B.Fail as e:
                fails.append((s, ph, asg, str(e)))
    nofill = []
    for (s, ph, asg, why) in fails:
        try:
            u = used_entries(M, s, ph, asg, 81)
        except (B.Need, B.Fail):
            u = None
        if u is not None and all(x[2] == "spec" for x in u):
            nofill.append((s, ph, asg, why, u))
    print("E failures %d, using no fill entry %d" % (len(fails), len(nofill)))
    for (s, ph, asg, why, u) in nofill[:4]:
        print(s, ph, sorted(asg.items()), why)
        print("   ", sorted(set((x[0], x[1]) for x in u)))


def job_full(p0):
    from collections import Counter
    from itertools import permutations as P
    cnt = Counter()
    passes = []
    for p1 in P(range(5)):
        for p2 in P(range(5)):
            r = cert({0: p0, 1: p1, 2: p2}, stop=True, verbose=False)
            k = r if r is True else r.split(" ")[0]
            cnt[k] += 1
            if r is True or k not in ("E",):
                passes.append((p0, p1, p2, k))
    return cnt, passes


if __name__ == "__main__" and sys.argv[1] == "full":
    from multiprocessing import Pool
    from collections import Counter
    tot = Counter()
    far = []
    t0 = time.time()
    with Pool(int(sys.argv[2])) as pool:
        for i, (cnt, passes) in enumerate(pool.imap_unordered(job_full, list(permutations(range(5))))):
            tot.update(cnt)
            far.extend(passes)
            print("  %d/120 %.0fs %s" % (i + 1, time.time() - t0, dict(tot)), flush=True)
    print("DONE", dict(tot))
    for p in far[:100]:
        print("BEYOND-E", p)


def body_cover2(M):
    """For every z in Y: U^-1 z is bounded, and lies in A exactly when z does not (tower both ways)."""
    def body(s, ph, asg):
        c = B.fresh(s, ph)
        if not B.inY(c, asg):
            return None
        za = B.inA(c, asg)
        B.U(M, c, asg, inverse=True)
        pa = B.inA(c, asg)
        if za and pa:
            raise B.Fail("z in A and U^-1 z in A")
        if not za and not pa:
            raise B.Fail("z, U^-1 z not in A")
        return True
    return body


# The renormalization criterion needs only R, T, C2, P, P-1, I (no global entry bound E).
CHECKS2 = [("R", B.ALL, body_rev), ("T", B.PH2, B.body_tower), ("C2", B.PH2, body_cover2),
           ("P", B.PH2, B.body_phi), ("P-1", B.PH2, B.body_phiinv), ("I", B.PH2, B.body_identity)]


def cert2(fill, stop=True, verbose=False):
    try:
        M = B.machine(fill)
    except B.Fail as e:
        return "build: %s" % e
    B.STATS["entry"] = B.STATS["ret"] = 0
    for name, sts, mk in CHECKS2:
        leaves, fails, first = B.exhaust(sts, mk(M), stop=stop)
        if verbose:
            print("  %-4s leaves=%-7d fails=%-6d %s" % (name, leaves, fails, first[:3] if fails else "PASS"))
        if fails:
            return "%s fails=%d first=%s" % (name, fails, first[:1])
    if verbose:
        print("  max return %d" % B.STATS["ret"])
    return True


def job2(p0):
    from collections import Counter
    from itertools import permutations as P
    cnt = Counter()
    good = []
    for p1 in P(range(5)):
        for p2 in P(range(5)):
            r = cert2({0: p0, 1: p1, 2: p2})
            k = r if r is True else r.split(" ")[0]
            cnt[k] += 1
            if r is True or k in ("I", "P-1", "P"):
                good.append((p0, p1, p2, k))
    return cnt, good


if __name__ == "__main__" and sys.argv[1] == "cert2":
    f = parse_fill(sys.argv[2]) if len(sys.argv) > 2 else B.DEFAULT
    print("cert2", cert2(f, stop=False, verbose=True))
if __name__ == "__main__" and sys.argv[1] == "full2":
    from multiprocessing import Pool
    from collections import Counter
    tot = Counter()
    good = []
    t0 = time.time()
    with Pool(int(sys.argv[2])) as pool:
        for i, (cnt, g) in enumerate(pool.imap_unordered(job2, list(permutations(range(5))))):
            tot.update(cnt)
            good.extend(g)
            print("  %d/120 %.0fs %s" % (i + 1, time.time() - t0, dict(tot)), flush=True)
    print("DONE", dict(tot))
    for p in good[:200]:
        print("LATE", p)
