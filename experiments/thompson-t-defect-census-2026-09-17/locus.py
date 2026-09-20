"""Many-start search on the SL(2,Z) locus A^2 = -1 (profile m = (0, a, 0, n-a)),
where r_1 = 1 identically and the pair represents Z4 *_{Z2} Z6.  For each n and
each B-profile k satisfying the determinant condition k1 + 2 k2 = 0 mod 3
(needed for exact (BA)^5 = 1 only; all k are run), `seeds` random eigenbases,
fixed-profile L-BFGS (lbfgs.optimise) with Schatten schedule to p = 256.

usage: python3 locus.py nmin nmax seeds out.jsonl [workers]
"""
import json, sys, time
import multiprocessing as mp


def comps(n, parts):
    import itertools
    for c in itertools.combinations(range(n + parts - 1), parts - 1):
        b = [-1] + list(c) + [n + parts - 1]
        yield tuple(b[i + 1] - b[i] - 1 for i in range(parts))


def job(a):
    import torch
    torch.set_num_threads(1)
    from lbfgs import optimise
    n, m, k, seed = a
    t = time.time()
    try:
        D, d, K, A, B = optimise(m, k, seed, ("r1", "r2", "rP"), ps=(2, 8, 32, 96, 256), iters=150, rounds=3)
    except Exception as e:
        return {"n": n, "m": m, "k": k, "seed": seed, "error": repr(e)}
    return {"n": n, "m": m, "k": k, "seed": seed, "D": D, "parts": d, "sec": round(time.time() - t, 1)}


if __name__ == "__main__":
    nmin, nmax, seeds, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    w = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    tasks = []
    for n in range(nmin, nmax + 1):
        for a in range(0, n // 2 + 1):  # m=(0,a,0,n-a) ~ (0,n-a,0,a) by conjugation
            m = (0, a, 0, n - a)
            for k in comps(n, 3):
                if k[0] == n:
                    continue
                for s in range(seeds):
                    tasks.append((n, m, k, 7919 * s + 13))
    print(len(tasks), "tasks", flush=True)
    with mp.Pool(w) as pool, open(out, "a") as f:
        for r in pool.imap_unordered(job, tasks):
            f.write(json.dumps(r) + "\n")
            f.flush()
