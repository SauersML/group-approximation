"""Minimal repro: does QR + diagonal-phase fix return a near-identity
matrix for a near-identity input, on this backend?

Run 3 of the stage-2 probe (V100, torch 2.2.2+cu121, complex64) logged
w_minus_identity = 1.9993 after ONE +-2e-4 Adam step from a 1e-4 warm
start, with the deviation concentrated in diagonal phases (block-diag
distance 0.053, monomial distance 0.0014).  Mathematically the
phase-fixed QR factor is phase-covariant and must be near I; this
script isolates the retraction from everything else.
"""

import sys

import torch


def report(tag, w, n):
    eye = torch.eye(n, dtype=w.dtype, device=w.device)
    dist = float(torch.linalg.norm(w - eye) / (n ** 0.5))
    tr = complex(torch.diagonal(w).mean().cpu())
    unit = float(torch.linalg.norm(w.conj().T @ w - eye) / (n ** 0.5))
    offd = w - torch.diag_embed(torch.diagonal(w))
    print("%s: |W-I|/sqrt(n)=%.4f  tr(W)/n=%.4f%+.4fi  "
          "unitarity=%.2e  offdiag_mass=%.4f"
          % (tag, dist, tr.real, tr.imag, unit,
             float(torch.linalg.norm(offd) / (n ** 0.5))), flush=True)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2048
    dev = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.manual_seed(11)
    print("torch", torch.__version__, "device", dev, "n", n, flush=True)

    w = torch.eye(n, dtype=torch.complex64, device=dev)
    w += 1e-4 * (torch.randn(n, n, dtype=torch.complex64, device=dev)
                 - torch.randn(n, n, dtype=torch.complex64,
                               device=dev).conj().T)

    # init retraction, as in the stage-2 script (original QR form)
    q, r = torch.linalg.qr(w)
    report("qr(init), raw Q", q, n)

    # one Adam-like signed step, as at iteration 0
    step = 2e-4 * (torch.sign(torch.randn(n, n, device=dev))
                   + 1j * torch.sign(torch.randn(n, n, device=dev))
                   ).to(torch.complex64)
    x = q + step

    q2, r2 = torch.linalg.qr(x)
    report("qr(post-step), raw Q", q2, n)
    d = torch.diagonal(r2)
    q2f = q2 * (d / d.abs().clamp_min(1e-12)).unsqueeze(0)
    report("qr(post-step), phase-fixed", q2f, n)
    ph = (d / d.abs().clamp_min(1e-12)).cpu()
    print("diag(R) phase stats: mean=%.4f%+.4fi  |mean|=%.4f "
          "(1.0 = coherent, 0.0 = random)"
          % (complex(ph.mean()).real, complex(ph.mean()).imag,
             abs(complex(ph.mean()))), flush=True)

    # Newton-Schulz polar, the replacement retraction
    y = x
    for _ in range(4):
        y = 1.5 * y - 0.5 * (y @ (y.conj().T @ y))
    report("newton-schulz(post-step)", y, n)


if __name__ == "__main__":
    main()
