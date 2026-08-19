"""Search the relative chart unitary for the two-S3 covariance trade-off.

Loads the frozen packet of `atlas_asc_packet_build.py` and runs projected
gradient descent on one unitary `U in U(20160 k)` for

    defect(U) = max_(s in packet) ||pi_U(s)-1||_2,
    cov(U)    = a^2+b^2,   a = ||U lambda(h_a) U^* - lambda(h_a)||_2,

with `pi_U` the canonical regular-A8 relative-unitary model of
`leavitt-regular-atlas-hyperlinearity-criterion`:

    pi_U(h) = lambda(h) (x) I_k          (h in K_1),
    pi_U(h) = U (lambda(h) (x) I_k) U^*  (h in K_2).

Modes:
  descend   minimize the packet defect alone and watch where cov goes;
  escape    minimize it subject to cov >= tau (hinge), tau = 1/40 default,
            the floor `raw-swap-forces-two-s3-covariance-energy` proves for
            any model that keeps the compiled raw source word;
  collapse  push cov down explicitly (control for the escape runs).

A low-defect point with cov >= 1/40 refutes (ASC) numerically; a trade-off
curve whose defect floor rises with tau is evidence for (ASCq) and measures
C >= tau/defect^2.

Speed, because the naive loop is ~100x slower than this one:

  * K1 syllables are permutations of the regular basis -- a gather, never a
    matmul.  Only K2 syllables touch U.
  * Words are bucketed by exact syllable pattern and evaluated in lockstep,
    so every U-application is ONE GEMM over (words x probes) columns.  U is
    3.2 GiB at k=1; reading it once per depth rather than once per word is
    the whole game.
  * U is carried as a real pair (Re,Im) and complex products are issued as
    real GEMMs, so TF32 tensor cores apply: ~10x over cuBLAS cgemm on A100.
    Training runs TF32, evaluation re-runs in strict fp32.
  * All gather index tensors are precomputed per (bucket, chunk, depth).
  * Newton-Schulz polar retraction is the only O(N^3) work and is amortized
    over --retract-every steps.

Evidence only, never proof: a local search over one chart unitary at one
finite multiplicity.  `research/atlas-two-s3-covariance-collapse` records an
exact characteristic-two countermodel showing the boundary half of the
packet does not force the collapse by itself.
"""

import argparse
import json
import math
import time

import numpy as np
import torch

ORDER = 20160


# --------------------------------------------------------- complex as real
# U is a real tensor (2, N, N): theta[0] = Re U, theta[1] = Im U.  States are
# real tensors (2, rows, cols).  Every product below is four real GEMMs
# issued as two batched matmuls, which is what puts them on tensor cores.

def apply_u(theta, state):
    """U @ state."""
    left = torch.matmul(theta, state)                    # [Ar xr, Ai xi]
    cross = torch.matmul(theta, state.flip(0))           # [Ar xi, Ai xr]
    return torch.stack((left[0] - left[1], cross[0] + cross[1]))


def apply_u_h(theta, state):
    """U^* @ state, with U^* = Ar^T - i Ai^T."""
    transposed = theta.transpose(1, 2)
    left = torch.matmul(transposed, state)               # [Ar^T xr, Ai^T xi]
    cross = torch.matmul(transposed, state.flip(0))      # [Ar^T xi, Ai^T xr]
    return torch.stack((left[0] + left[1], cross[0] - cross[1]))


def spectral_norm(theta, iters=6):
    """Power iteration for sigma_max, so Newton-Schulz stays in its basin."""
    vector = torch.randn(2, theta.shape[1], 1, device=theta.device)
    vector = vector / vector.norm()
    value = 1.0
    for _ in range(iters):
        moved = apply_u_h(theta, apply_u(theta, vector))
        value = float(moved.norm())
        if value == 0.0:
            return 0.0
        vector = moved / value
    return math.sqrt(value)


def to_complex(pair):
    return torch.complex(pair[0], pair[1])


def to_pair(matrix):
    return torch.stack((matrix.real.contiguous(), matrix.imag.contiguous()))


@torch.no_grad()
def geodesic_step(theta, grad, rank, lr, generator):
    """Exactly unitary descent step, with no O(N^3) work anywhere.

    The Riemannian direction is the skew part A = U^* G - G^* U.  Its
    dominant rank-r subspace is captured by one random sketch, and on that
    subspace the geodesic is an r x r matrix exponential:

        U <- U exp(-eta Q S Q^*) = U + (U Q)(exp(-eta S) - I) Q^*,

    which is exact because Q^*Q = I.  Every product is (N x N)(N x r), so a
    step costs about a percent of the objective evaluation, and U stays on
    the manifold to floating point -- no retraction, no drift, no collapse
    of U toward zero (which is what projected steps did here: defect 1.0 and
    cov 2.0 are the U = 0 signature).
    """
    n = theta.shape[1]
    omega = torch.randn(2, n, rank, device=theta.device, generator=generator)
    sketch = (apply_u_h(theta, apply_u(grad, omega))
              - apply_u_h(grad, apply_u(theta, omega)))
    basis, _ = torch.linalg.qr(to_complex(sketch))
    basis = to_pair(basis)
    moved = (apply_u_h(theta, apply_u(grad, basis))
             - apply_u_h(grad, apply_u(theta, basis)))
    small = to_complex(apply_u_h(basis, moved))
    small = 0.5 * (small - small.conj().t())
    size = float(torch.linalg.matrix_norm(small, ord=2))
    if size == 0.0 or not math.isfinite(size):
        return 0.0
    step = torch.matrix_exp(small * (-lr / size))
    step = step - torch.eye(step.shape[0], dtype=step.dtype,
                            device=step.device)
    turned = apply_u(theta, basis)                       # (2, n, r)
    turned = to_pair(to_complex(turned) @ step)
    # rank-r update U += W Q^*, in the real pair form
    theta[0].addmm_(turned[0], basis[0].t())
    theta[0].addmm_(turned[1], basis[1].t())
    theta[1].addmm_(turned[1], basis[0].t())
    theta[1].addmm_(turned[0], basis[1].t(), alpha=-1.0)
    return lr


_WORKSPACE = {}


def workspace(theta, count=4):
    """Four reusable (N,N) buffers: the retraction must not allocate.

    A naive Newton-Schulz on a (2,N,N) parameter builds ~7 full copies and
    OOMs a 40 GiB card at N = 20160; every product below therefore goes
    through addmm_ into a buffer that is allocated once per process.
    """
    n = theta.shape[1]
    key = (n, theta.device, theta.dtype)
    if key not in _WORKSPACE:
        _WORKSPACE[key] = [torch.empty(n, n, device=theta.device,
                                       dtype=theta.dtype)
                           for _ in range(count)]
    return _WORKSPACE[key]


@torch.no_grad()
def polar_retract(theta, steps=1):
    """Newton-Schulz toward the nearest unitary, in place, no allocation.

    NS converges only for sigma_max < sqrt(3), and an Adam step or a noisy
    init can leave that basin -- hence the rescale, which costs six matvecs.
    """
    scale = spectral_norm(theta)
    if scale > 1.0:
        theta.div_(scale)          # in place: callers rely on the parameter

    real, imag = theta[0], theta[1]
    mr, mi, nr, ni = workspace(theta)
    for _ in range(steps):
        # M = U^* U
        torch.mm(real.t(), real, out=mr)
        mr.addmm_(imag.t(), imag)
        torch.mm(real.t(), imag, out=mi)
        mi.addmm_(imag.t(), real, alpha=-1.0)
        # N = U M, then U <- 1.5 U - 0.5 N
        torch.mm(real, mr, out=nr)
        nr.addmm_(imag, mi, alpha=-1.0)
        torch.mm(real, mi, out=ni)
        ni.addmm_(imag, mr)
        real.mul_(1.5).add_(nr, alpha=-0.5)
        imag.mul_(1.5).add_(ni, alpha=-0.5)
    return theta


@torch.no_grad()
def unitarity_drift(theta, probes=32):
    """||U^*U - I||_2 estimated on probes -- forming U^*U costs 3 GiB."""
    n = theta.shape[1]
    vector = torch.randn(2, n, probes, device=theta.device)
    vector = vector / math.sqrt(probes)
    moved = apply_u_h(theta, apply_u(theta, vector)) - vector
    return float(moved.norm() / math.sqrt(2.0 * n))


# ------------------------------------------------------------------ packet

class Packet:
    """Words bucketed by syllable pattern with gather indices on device."""

    def __init__(self, path, k, device, include, word_batch):
        data = np.load(path, allow_pickle=True)
        names = [str(name) for name in data["names"]]
        offsets, factors = data["offsets"], data["flat_factor"]
        elements = data["flat_element"]

        words, kept = [], []
        for index, name in enumerate(names):
            if name.split(":")[0] not in include:
                continue
            lo, hi = int(offsets[index]), int(offsets[index + 1])
            words.append([(int(f), int(e))
                          for f, e in zip(factors[lo:hi], elements[lo:hi])])
            kept.append(name)

        self.k, self.n, self.device = k, ORDER * k, device
        self.gathers = torch.from_numpy(
            np.ascontiguousarray(data["gathers"])).to(device).long()
        ha, hb = (int(value) for value in data["cov_elements"])
        self.packet_words = len(words)
        words += [[(2, ha), (1, ha)], [(2, hb), (1, hb)]]
        kept += ["cov:a", "cov:b"]
        self.names, self.words = kept, words

        buckets = {}
        for position, word in enumerate(words):
            buckets.setdefault(tuple(f for f, _ in word), []).append(position)

        # fixed chunks with their gather indices materialized once; a training
        # step then costs GEMMs and nothing else
        self.chunks = []
        for pattern, positions in sorted(buckets.items()):
            for start in range(0, len(positions), word_batch):
                group = positions[start:start + word_batch]
                self.chunks.append((tuple(group), pattern,
                                    self._index(group, pattern)))
        self.by_position = {}
        for index, (group, _pattern, _idx) in enumerate(self.chunks):
            for position in group:
                self.by_position[position] = index

    def _index(self, group, pattern):
        width = len(group)
        stack = []
        for depth in range(len(pattern)):
            elements = [self.words[position][depth][1] for position in group]
            base = self.gathers[torch.tensor(elements, device=self.device)]
            base = base.t()                                # (ORDER, words)
            if self.k > 1:
                base = base.unsqueeze(1).expand(ORDER, self.k, width) * self.k
                base = base + torch.arange(
                    self.k, device=self.device).view(1, self.k, 1)
                base = base.reshape(self.n, width)
            flat = base * width + torch.arange(
                width, device=self.device).view(1, -1)
            stack.append(flat.reshape(self.n * width).contiguous())
        return stack


def chunk_defects(packet, chunk, theta, probe):
    """||pi(w)-1||_2^2 for every word of one precomputed chunk."""
    group, pattern, index = chunk
    width, n, b = len(group), packet.n, probe.shape[2]
    base = probe.unsqueeze(2).expand(2, n, width, b).reshape(2, n * width, b)
    state = base
    for depth in reversed(range(len(pattern))):
        if pattern[depth] == 1:
            state = state.index_select(1, index[depth])
        else:
            state = apply_u_h(theta, state.view(2, n, width * b))
            state = state.view(2, n * width, b).index_select(1, index[depth])
            state = apply_u(theta, state.view(2, n, width * b))
            state = state.view(2, n * width, b)
    residual = (state - base).view(2, n, width, b)
    return (residual * residual).sum(dim=(0, 1, 3)) / (n * b)


def probes_of(n, b, device, generator):
    bits = torch.randint(0, 2, (n, b), device=device, generator=generator,
                         dtype=torch.int8).float()
    return torch.stack((2.0 * bits - 1.0, torch.zeros_like(bits)))


# --------------------------------------------------------------------- run

def evaluate_all(packet, theta, probes, device, generator, tf32):
    previous = torch.backends.cuda.matmul.allow_tf32
    torch.backends.cuda.matmul.allow_tf32 = bool(tf32)
    out = {}
    with torch.no_grad():
        probe = probes_of(packet.n, probes, device, generator)
        for chunk in packet.chunks:
            values = chunk_defects(packet, chunk, theta, probe)
            for position, value in zip(chunk[0], values.tolist()):
                out[packet.names[position]] = max(value, 0.0)
    torch.backends.cuda.matmul.allow_tf32 = bool(previous)
    return out


def summarize(values):
    body = {name: value for name, value in values.items()
            if not name.startswith("cov:")}
    worst = max(body.items(), key=lambda item: item[1])
    return {
        "max_defect": math.sqrt(worst[1]),
        "worst_word": worst[0],
        "mean_defect_sq": float(np.mean(list(body.values()))),
        "boundary_max_defect": math.sqrt(max(
            [value for name, value in body.items()
             if not name.startswith("interior")] or [0.0])),
        "interior_defect": math.sqrt(values.get("interior:19243", 0.0)),
        "cov_sq": values.get("cov:a", 0.0) + values.get("cov:b", 0.0),
    }


def run(args):
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.manual_seed(args.seed)
    generator = torch.Generator(device=device)
    generator.manual_seed(args.seed)

    packet = Packet(args.npz, args.k, device, set(args.packet.split(",")),
                    args.word_batch)
    n = packet.n
    cov_chunks = sorted({packet.by_position[packet.names.index("cov:a")],
                         packet.by_position[packet.names.index("cov:b")]})
    train_chunks = [index for index, chunk in enumerate(packet.chunks)
                    if all(position < packet.packet_words
                           for position in chunk[0])]

    scale = 1.0 / math.sqrt(n)
    if args.init == "identity":
        theta = torch.stack((torch.eye(n, device=device),
                             torch.zeros(n, n, device=device)))
    elif args.init == "perturbed":
        # exp of a small skew part, to first order: I + S has all singular
        # values near 1, which is where Newton-Schulz actually converges
        noise = torch.randn(2, n, n, device=device, generator=generator) * (
            0.5 * args.init_scale * scale)
        skew = torch.stack((noise[0] - noise[0].t(), noise[1] + noise[1].t()))
        theta = torch.stack((torch.eye(n, device=device),
                             torch.zeros(n, n, device=device))) + skew
        theta = polar_retract(theta, 4)
    else:
        # a Haar-ish start needs a real factorization, not Newton-Schulz: a
        # Gaussian has singular values down at zero and NS crawls there
        block = torch.randn(n, n, dtype=torch.complex64, device=device,
                            generator=generator) * scale
        factor, upper = torch.linalg.qr(block)
        phase = torch.diagonal(upper)
        factor = factor * (phase / phase.abs()).conj().unsqueeze(0)
        theta = torch.stack((factor.real.contiguous(),
                             factor.imag.contiguous()))
        del block, factor, upper
    theta.requires_grad_(True)

    # A unitary has entries of size 1/sqrt(N) = 0.007 at N = 20160, so an
    # elementwise optimizer with any usual learning rate walks straight off
    # the manifold (measured: drift 0.83 after 100 Adam steps at lr 3e-3).
    # The default step is therefore scale-free: a fixed RELATIVE displacement
    # ||dU||_F / ||U||_F = lr along momentum, retracted every few steps.
    optimizer = None
    if args.optimizer == "geodesic":
        optimizer = None
    elif args.optimizer == "adam":
        optimizer = torch.optim.Adam([theta], lr=args.lr, foreach=False)
    elif args.optimizer == "sgd":
        optimizer = torch.optim.SGD([theta], lr=args.lr, momentum=0.9,
                                    foreach=False)
    velocity = None
    started = time.time()
    log = open(args.out, "a", buffering=1) if args.out else None

    def emit(record):
        record["elapsed_s"] = round(time.time() - started, 1)
        line = json.dumps(record, sort_keys=True)
        print(line, flush=True)
        if log:
            log.write(line + "\n")

    emit({"event": "start", "n": n, "k": args.k, "mode": args.mode,
          "packet": args.packet, "words": packet.packet_words,
          "chunks": len(packet.chunks), "tau": args.tau, "lam": args.lam,
          "probes": args.probes, "word_batch": args.word_batch,
          "init": args.init, "lr": args.lr, "optimizer": args.optimizer,
          "tf32": args.tf32, "device": torch.cuda.get_device_name(0)
          if device.type == "cuda" else "cpu"})
    emit({"event": "baseline",
          **summarize(evaluate_all(packet, theta.detach(), args.eval_probes,
                                   device, generator, args.tf32))})

    torch.backends.cuda.matmul.allow_tf32 = bool(args.tf32)
    picker = np.random.RandomState(args.seed)
    best = {"max_defect": float("inf")}
    deadline = started + args.time_limit if args.time_limit else None
    for step in range(1, args.iterations + 1):
        if optimizer is not None:
            optimizer.zero_grad(set_to_none=True)
        else:
            theta.grad = None
        probe = probes_of(n, args.probes, device, generator)
        index = train_chunks[picker.randint(len(train_chunks))]
        defects = chunk_defects(packet, packet.chunks[index], theta, probe)
        loss = (args.mean_weight * defects.mean()
                + torch.logsumexp(defects * args.beta, dim=0) / args.beta)

        cov = sum(chunk_defects(packet, packet.chunks[which], theta,
                                probe).sum() for which in cov_chunks)
        if args.mode == "escape":
            loss = loss + args.lam * torch.clamp(args.tau - cov, min=0.0)
        elif args.mode == "pin":
            # two-sided: the hinge stops pushing the moment cov clears tau,
            # so the Pareto point at a GIVEN covariance needs an equality
            loss = loss + args.lam * (cov - args.tau) ** 2
        elif args.mode == "collapse":
            loss = loss + args.lam * cov

        loss.backward()
        if optimizer is not None:
            optimizer.step()
            optimizer.zero_grad(set_to_none=True)
            if step % args.retract_every == 0:
                polar_retract(theta.detach(), args.retract_steps)
        else:
            with torch.no_grad():
                if velocity is None:
                    velocity = torch.zeros_like(theta)
                velocity.mul_(args.momentum).add_(theta.grad)
            geodesic_step(theta.detach(), velocity, args.rank, args.lr,
                          generator)
            if step % args.retract_every == 0:      # float hygiene only
                polar_retract(theta.detach(), 1)
        theta.grad = None

        if step % args.report_every == 0:
            emit({"event": "progress", "step": step,
                  "loss": float(loss.detach()),
                  "batch_max_defect": math.sqrt(
                      max(float(defects.max().detach()), 0.0)),
                  "cov_sq": float(cov.detach()),
                  "pattern": "".join(str(f)
                                     for f in packet.chunks[index][1])})

        if args.eval_every and step % args.eval_every == 0:
            drift = unitarity_drift(theta.detach())
            fresh = polar_retract(theta.detach(), 1)
            values = summarize(evaluate_all(packet, fresh, args.eval_probes,
                                            device, generator, args.tf32))
            values["drift"] = drift
            emit({"event": "eval", "step": step, **values})
            if values["max_defect"] < best["max_defect"]:
                best = dict(values, step=step)
                if args.save_unitary:
                    torch.save(fresh.detach().cpu().clone(),
                               args.save_unitary)
        if deadline and time.time() > deadline:
            emit({"event": "time_limit", "step": step})
            break

    fresh = polar_retract(theta.detach(), 2)
    exact = evaluate_all(packet, fresh, args.final_probes, device, generator,
                         False)
    emit({"event": "final_fp32", **summarize(exact), "best_seen": best,
          "per_word": {name: round(math.sqrt(value), 6)
                       for name, value in sorted(exact.items())}})
    if log:
        log.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--npz", default="experiments/atlas-asc-packet.npz")
    parser.add_argument("--packet",
                        default="certified,boundary,phase,interior")
    parser.add_argument("--mode", default="escape",
                        choices=("descend", "escape", "pin",
                                 "collapse"))
    parser.add_argument("--k", type=int, default=1)
    parser.add_argument("--tau", type=float, default=1.0 / 40.0)
    parser.add_argument("--lam", type=float, default=8.0)
    parser.add_argument("--beta", type=float, default=40.0)
    parser.add_argument("--mean-weight", type=float, default=1.0)
    parser.add_argument("--probes", type=int, default=16)
    parser.add_argument("--eval-probes", type=int, default=32)
    parser.add_argument("--final-probes", type=int, default=64)
    parser.add_argument("--word-batch", type=int, default=48)
    parser.add_argument("--iterations", type=int, default=1500)
    parser.add_argument("--lr", type=float, default=0.05)
    parser.add_argument("--optimizer", default="geodesic",
                        choices=("geodesic", "nsgd", "adam", "sgd"))
    parser.add_argument("--rank", type=int, default=64)
    parser.add_argument("--momentum", type=float, default=0.9)
    parser.add_argument("--init", default="perturbed",
                        choices=("identity", "perturbed", "random"))
    parser.add_argument("--init-scale", type=float, default=0.3)
    parser.add_argument("--retract-every", type=int, default=200)
    parser.add_argument("--retract-steps", type=int, default=1)
    parser.add_argument("--report-every", type=int, default=25)
    parser.add_argument("--eval-every", type=int, default=250)
    parser.add_argument("--time-limit", type=float, default=0.0)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--tf32", type=int, default=1)
    parser.add_argument("--out", default="")
    parser.add_argument("--save-unitary", default="")
    run(parser.parse_args())


if __name__ == "__main__":
    main()
