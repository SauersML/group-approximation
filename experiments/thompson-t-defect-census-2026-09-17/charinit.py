"""Start at a direct sum of one-dimensional characters (A = i^p_j, B = w^q_j on
coordinate j), perturb the eigenbasis of B by exp(eps*(K - K^H)), and
minimise the Schatten-p surrogate of the three-relator defect.

The one-dimensional characters have r_1 = r_2 = 1 and ||r_P - 1|| = |z^5 - 1|,
z = i^p w^q, so the start has D = max_j |z_j^5 - 1|.  The question is whether
hybridising characters lowers D below the one-dimensional value 2 sin(pi/12).

usage: python3 charinit.py "p:q,p:q,..." eps seeds [ps]
"""
import json, math, sys, time
import torch
from census import relators, exact_defect


def run(chars, eps, seed, ps=(2, 8, 32, 96, 256), iters=200, rounds=4):
    n = len(chars)
    da = torch.tensor([complex(math.cos(math.pi * p / 2), math.sin(math.pi * p / 2)) for p, q in chars],
                      dtype=torch.complex128)
    db = torch.tensor([complex(math.cos(2 * math.pi * q / 3), math.sin(2 * math.pi * q / 3)) for p, q in chars],
                      dtype=torch.complex128)
    g = torch.Generator().manual_seed(seed)
    K = (eps * (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g))).to(torch.complex128)
    K.requires_grad_(True)
    eye = torch.eye(n, dtype=torch.complex128)

    def build():
        Y = torch.matrix_exp(K - K.conj().T)
        return torch.diag(da), Y @ torch.diag(db) @ Y.conj().T

    for p in ps:
        opt = torch.optim.LBFGS([K], lr=1, max_iter=iters, history_size=50, line_search_fn="strong_wolfe",
                                tolerance_grad=1e-14, tolerance_change=1e-17)

        def closure():
            opt.zero_grad()
            A, B = build()
            rs = relators(A, B)
            if p == 2:
                loss = sum(((R - eye).abs() ** 2).sum() for R in rs.values())
            else:
                ss = torch.cat([torch.linalg.svdvals(R - eye) for R in rs.values()])
                loss = (ss ** p).sum() ** (2.0 / p)
            loss.backward()
            return loss

        for _ in range(rounds):
            opt.step(closure)
    with torch.no_grad():
        Y = torch.matrix_exp(K - K.conj().T)
        Q, R = torch.linalg.qr(Y)
        A = torch.diag(da).numpy()
        B = (Q @ torch.diag(db) @ Q.conj().T).numpy()
    d = exact_defect(A, B)
    return max(d.values()), d, A, B


if __name__ == "__main__":
    chars = [tuple(int(t) for t in c.split(":")) for c in sys.argv[1].split(",")]
    eps = float(sys.argv[2])
    seeds = int(sys.argv[3])
    ps = tuple(int(x) for x in sys.argv[4].split(",")) if len(sys.argv) > 4 else (2, 8, 32, 96, 256)
    best = None
    for s in range(seeds):
        t = time.time()
        D, d, A, B = run(chars, eps, s, ps)
        print(json.dumps({"chars": chars, "eps": eps, "seed": s, "D": D, "parts": d,
                          "sec": round(time.time() - t, 1)}), flush=True)
        if best is None or D < best[0]:
            best = (D, s)
    print("BEST", best)
