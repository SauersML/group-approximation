"""Driver for perturb_dsum.py over a fixed list of direct-sum starts (n = 2..7).
Writes out_perturb_dsum.jsonl.  usage: python3 run_perturb.py [workers]"""
import json, sys
import multiprocessing as mp

CONFIGS = [(1, []), (2, []), (3, []), (1, [(0, 0)]), (1, [(1, 1)]), (1, [(2, 0)]), (1, [(0, 1)]),
           (1, [(3, 2)]), (1, [(1, 0)]), (1, [(0, 0), (0, 0)]), (1, [(1, 1), (3, 2)]),
           (2, [(0, 0)]), (2, [(1, 1)]), (2, [(0, 0), (1, 1), (2, 2)])]
EPS = [0.02, 0.1, 0.4]
SEEDS = 3


def job(a):
    import torch
    torch.set_num_threads(1)
    from perturb_dsum import run, DELTA2
    copies, chars, eps, seed = a
    try:
        D, d = run(copies, chars, eps, seed)
    except Exception as e:
        return {"copies": copies, "chars": chars, "eps": eps, "seed": seed, "error": repr(e)}
    return {"copies": copies, "chars": chars, "n": 2 * copies + len(chars), "eps": eps, "seed": seed, "D": D,
            "parts": d, "beats_delta2": D < DELTA2 - 1e-9}


if __name__ == "__main__":
    w = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    tasks = [(c, ch, e, s) for c, ch in CONFIGS for e in EPS for s in range(SEEDS)]
    with mp.Pool(w) as pool, open("out_perturb_dsum.jsonl", "a") as f:
        for r in pool.imap_unordered(job, tasks):
            f.write(json.dumps(r) + "\n")
            f.flush()
