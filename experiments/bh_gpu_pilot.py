"""Bounded GPU proof proposals for the Boone–Higman construction audit.

Run only on a CUDA machine. This produces proposals, never proof certificates.
The immutable statements in PROBES must be checked independently with Lean.
"""

import argparse
import json
import time
from pathlib import Path


LEAN_IMPORTS = "import Mathlib.Algebra.Group.Subgroup.Lattice\n"


PROBES = {
    "commuting_control": {
        "role": "known true control",
        "statement": """theorem bh_probe {G : Type} [Group G] (H K : Subgroup G)
    (hdis : H ⊓ K = ⊥)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x y a b : G} (hx : x ∈ K) (hy : y ∈ K)
    (ha : a ∈ H) (hb : b ∈ H) (heq : y = a * x * b) : x = y := by""",
    },
    "normalizer_extension": {
        "role": "construction filter; independently Lean-checked, not an open conjecture",
        "statement": """theorem bh_probe {G : Type} [Group G] (H K : Subgroup G)
    (hdis : H ⊓ K = ⊥)
    (hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    {x y a b : G} (hx : x ∈ K) (hy : y ∈ K)
    (ha : a ∈ H) (hb : b ∈ H) (heq : y = a * x * b) : x = y := by""",
    },
    "missing_hypothesis_control": {
        "role": "known false control: H=C2 and K=C3 in S3",
        "statement": """theorem bh_probe {G : Type} [Group G] (H K : Subgroup G)
    (hdis : H ⊓ K = ⊥)
    {x y a b : G} (hx : x ∈ K) (hy : y ∈ K)
    (ha : a ∈ H) (hb : b ∈ H) (heq : y = a * x * b) : x = y := by""",
    },
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--revision", required=True)
    args = parser.parse_args()
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer

    if not torch.cuda.is_available():
        raise RuntimeError("This experiment requires CUDA; no CPU execution path")
    torch.set_num_threads(4)
    torch.manual_seed(20260908)
    model_id = "deepseek-ai/DeepSeek-Prover-V2-7B"
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "probes.json").write_text(json.dumps(PROBES, indent=2) + "\n")
    tokenizer = AutoTokenizer.from_pretrained(model_id, revision=args.revision)
    tokenizer.padding_side = "left"
    tokenizer.pad_token = tokenizer.eos_token
    started = time.monotonic()
    model = AutoModelForCausalLM.from_pretrained(
        model_id, revision=args.revision, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa", device_map="cuda", trust_remote_code=False,
    ).eval()
    metadata = {
        "model": model_id, "revision": args.revision,
        "gpu": torch.cuda.get_device_name(), "torch": torch.__version__,
        "load_seconds": time.monotonic() - started, "seed": 20260908,
        "max_new_tokens": 2048, "temperature": 0.8, "top_p": 0.95,
    }
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    with (args.output / "proposals.jsonl").open("w") as log:
        for name, probe in PROBES.items():
            prompt = (
                "Complete the Lean 4 theorem below, using Mathlib. Give a brief proof plan, "
                "then a fenced lean4 block containing ONLY the tactic body following := by. "
                "Do not change the statement or add assumptions. No sorry, admit, axiom, "
                "native_decide or external code. If false, explain a counterexample instead.\n\n"
                + LEAN_IMPORTS + "\n" + probe["statement"]
            )
            chat = tokenizer.apply_chat_template(
                [{"role": "user", "content": prompt}], tokenize=False,
                add_generation_prompt=True,
            )
            # Eight independent neural proposals share one dense GPU forward pass.
            # Two batches per probe keep the pilot bounded at 48 proposals.
            for batch in range(2):
                inputs = tokenizer([chat] * 8, return_tensors="pt", padding=True).to("cuda")
                torch.cuda.synchronize()
                tick = time.monotonic()
                with torch.inference_mode():
                    output = model.generate(
                        **inputs, max_new_tokens=2048, do_sample=True,
                        temperature=0.8, top_p=0.95, pad_token_id=tokenizer.pad_token_id,
                    )
                torch.cuda.synchronize()
                elapsed = time.monotonic() - tick
                tokens = output[:, inputs.input_ids.shape[1]:]
                for sample, (text, row) in enumerate(zip(tokenizer.batch_decode(tokens, skip_special_tokens=True), tokens)):
                    log.write(json.dumps({
                        "probe": name, "batch": batch, "sample": sample,
                        "text": text, "batch_seconds": elapsed,
                        "tokens": int((row != tokenizer.pad_token_id).sum()),
                    }) + "\n")
                log.flush()
                print(json.dumps({"probe": name, "batch": batch, "seconds": elapsed,
                                  "peak_gpu_gb": torch.cuda.max_memory_allocated() / 2**30}), flush=True)


if __name__ == "__main__":
    main()
