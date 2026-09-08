"""One A100 pilot, controlled from MSI, with deletion after at most 45 minutes.

API key is read from stdin and held in memory only. Run directory must be on
MSI shared storage outside the repository. Only resources created by this run
are deleted. No resizing, retries of instance creation, or replacement hosts.
"""

import argparse
import json
import math
import os
from pathlib import Path
import signal
import shlex
import subprocess
import sys
import time
import urllib.error
import urllib.request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", type=Path)
    parser.add_argument("gpu_script", type=Path)
    args = parser.parse_args()
    root = args.run_dir.resolve()
    if not str(root).startswith("/projects/standard/"):
        raise ValueError("Run from MSI using shared project storage")
    root.mkdir(mode=0o700, parents=True, exist_ok=False)
    token = sys.stdin.readline().strip()
    if not token:
        raise ValueError("API key required on stdin")
    hostname = "bh-pilot-" + str(int(time.time()))
    region = "lon1"
    started = time.time()
    deadline = started + 45 * 60
    state = {"hostname": hostname, "region": region, "started": started,
             "deadline": deadline, "hourly_usd": 1.09, "total_cap_usd": 20,
             "pilot_max_base_usd": 1.09, "instance_id": None, "sshkey_id": None}

    def save():
        (root / "state.json").write_text(json.dumps(state, indent=2) + "\n")

    def api(method, path, data=None):
        url = "https://api.civo.com/v2/" + path
        url += ("&" if "?" in url else "?") + "region=" + region
        req = urllib.request.Request(url, method=method,
            headers={"Authorization": "bearer " + token, "Content-Type": "application/json"},
            data=None if data is None else json.dumps(data).encode())
        try:
            with urllib.request.urlopen(req, timeout=25) as response:
                body = response.read()
                return json.loads(body) if body else {}
        except urllib.error.HTTPError as error:
            # Do not dump responses: report only the API's diagnostic fields.
            try:
                detail = json.loads(error.read(8192))
                reason = "; ".join(str(detail[k]) for k in ("code", "reason", "message") if k in detail)
            except (ValueError, TypeError):
                reason = "No structured diagnostic"
            raise RuntimeError("Civo " + method + " " + path + " HTTP " + str(error.code)
                               + ": " + reason.replace(token, "[redacted]")) from None

    def cleanup():
        # Exact unique hostname also reconciles an ambiguous POST response.
        instances = api("GET", "instances?per_page=100")["items"]
        for instance in instances:
            if instance["hostname"] == hostname:
                state["instance_id"] = instance["id"]
                api("DELETE", "instances/" + instance["id"])
        remaining = api("GET", "instances?per_page=100")["items"]
        if any(item["hostname"] == hostname for item in remaining):
            return False
        for key in api("GET", "sshkeys"):
            if key["name"] == hostname:
                api("DELETE", "sshkeys/" + key["id"])
        (root / "deleted.json").write_text(json.dumps({"confirmed_at": time.time(),
            "hostname": hostname, "instance_absent": True}) + "\n")
        return True

    save()
    # Independent, negligible-CPU watchdog survives loss of the controller's SSH
    # session. It receives the key by forked memory, never a credential file.
    watcher = os.fork()
    if watcher == 0:
        signal.signal(signal.SIGHUP, signal.SIG_IGN)
        os.setsid()
        with (root / "watchdog.log").open("a") as log:
            os.dup2(log.fileno(), 1)
            os.dup2(log.fileno(), 2)
            while time.time() < deadline:
                if (root / "deleted.json").exists():
                    os._exit(0)
                time.sleep(10)
            for _ in range(120):
                try:
                    if cleanup():
                        os._exit(0)
                except Exception as error:
                    print(type(error).__name__, flush=True)
                time.sleep(15)
            os._exit(1)
    state["watchdog_pid"] = watcher
    save()

    def interrupted(signum, frame):
        raise TimeoutError("Pilot interrupted or reached wall-time limit")

    for sig in (signal.SIGHUP, signal.SIGTERM, signal.SIGINT, signal.SIGALRM):
        signal.signal(sig, interrupted)
    signal.alarm(43 * 60)

    def run(argv, timeout, output_name):
        print(json.dumps({"step": output_name, "time": time.time()}), flush=True)
        with (root / output_name).open("w") as output:
            subprocess.run(argv, stdout=output, stderr=subprocess.STDOUT,
                           timeout=timeout, check=True)

    try:
        # Recheck the advertised shape against actual account quota before POST.
        sizes = api("GET", "sizes")
        size = next(s for s in sizes if s["name"] == "g4g.40.small" and s["type"] == "Instance")
        quota = api("GET", "quota")
        if not size["selectable"] or size["gpu_count"] != 1:
            raise RuntimeError("Selected single A100 is unavailable")
        for resource, amount in (("cpu_core", size["cpu_cores"]),
                                 ("ram_mb", size["ram_mb"]), ("disk_gb", size["disk_gb"]),
                                 ("instance_count", 1)):
            if quota[resource + "_usage"] + amount > quota[resource + "_limit"]:
                raise RuntimeError("Insufficient " + resource + " quota")
        keyfile = root / "ssh_key"
        run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(keyfile)], 10, "keygen.log")
        key = api("POST", "sshkeys", {"name": hostname, "public_key": keyfile.with_suffix(".pub").read_text()})
        state["sshkey_id"] = key["id"]
        save()
        instance = api("POST", "instances", {
            "hostname": hostname, "size": size["name"], "region": region,
            "network_id": "20e5bcf6-39fb-410e-953f-bc531473c5bc",
            "template_id": "4889c672-3d3c-4e8d-853a-34cabf32e135",
            "initial_user": "root", "ssh_key_id": key["id"],
            "public_ip": "create", "tags": "bh-gpu-pilot", "count": 1,
        })
        state["instance_id"] = instance["id"]
        save()
        print(json.dumps({"created": instance["id"], "size": size["name"]}), flush=True)
        for _ in range(36):
            instance = api("GET", "instances/" + state["instance_id"])
            if instance["status"] == "ACTIVE" and instance.get("public_ip"):
                break
            if instance["status"] in ("ERROR", "FAILED"):
                raise RuntimeError("Instance failed to start")
            time.sleep(10)
        else:
            raise TimeoutError("Instance did not become active within six minutes")
        state["public_ip"] = instance["public_ip"]
        save()
        sshopts = ["-i", str(keyfile), "-o", "BatchMode=yes", "-o", "ConnectTimeout=8",
                   "-o", "StrictHostKeyChecking=accept-new", "-o", "UserKnownHostsFile=" + str(root / "known_hosts")]
        target = "root@" + instance["public_ip"]
        ssh = ["ssh", *sshopts, target]
        for _ in range(18):
            try:
                run([*ssh, "nvidia-smi"], 15, "gpu-preflight.log")
                break
            except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
                time.sleep(10)
        else:
            raise TimeoutError("GPU SSH preflight failed")
        run(["scp", *sshopts, str(args.gpu_script), target + ":/root/bh_gpu_pilot.py"], 30, "upload.log")
        setup = ("set -e; cloud-init status --wait; "
                 "apt-get update -qq; apt-get install -y -qq python3-venv; "
                 "python3 -m venv /opt/bh-prover; "
                 "/opt/bh-prover/bin/pip install --quiet torch==2.7.1 transformers==4.55.4 accelerate==1.10.1")
        run([*ssh, "timeout 600 bash -c " + shlex.quote(setup)], 630, "setup.log")
        command = ("timeout 1200 /opt/bh-prover/bin/python -u /root/bh_gpu_pilot.py /root/bh-output "
                   "--revision a8d9e14432b2e8dd9df2a4d4e70f1ba9bc8d9b7b")
        try:
            run([*ssh, command], 1230, "inference.log")
        finally:
            run(["scp", *sshopts, "-r", target + ":/root/bh-output", str(root / "output")], 60, "download.log")
        state["outcome"] = "proposals_downloaded"
    except Exception as error:
        state["outcome"] = "failed"
        state["error"] = str(error).replace(token, "[redacted]")
        print(json.dumps({"error": state["error"]}), flush=True)
    finally:
        signal.alarm(0)
        for _ in range(12):
            try:
                if cleanup():
                    state["deletion_confirmed"] = True
                    break
            except Exception as error:
                print(json.dumps({"cleanup_error": type(error).__name__}), flush=True)
            time.sleep(5)
        state["finished"] = time.time()
        state["base_cost_upper_estimate_usd"] = (
            math.ceil((state["finished"] - started) / 3600) * 1.09 if state["instance_id"] else 0)
        save()
        print(json.dumps(state), flush=True)
        if state.get("deletion_confirmed"):
            for name in ("ssh_key", "ssh_key.pub"):
                path = root / name
                if path.exists():
                    path.unlink()
        if state.get("outcome") != "proposals_downloaded" or not state.get("deletion_confirmed"):
            raise SystemExit(1)


if __name__ == "__main__":
    main()
