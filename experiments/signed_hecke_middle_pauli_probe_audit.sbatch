#!/bin/bash
#SBATCH --job-name=hecke-pauli-probe
#SBATCH --partition=sioux
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:10:00
#SBATCH --output=signed-hecke-middle-pauli-probe-%j.out

set -euo pipefail
repository_root="${1:?usage: sbatch signed_hecke_middle_pauli_probe_audit.sbatch REPOSITORY_ROOT}"
cd "$repository_root/experiments"
/usr/bin/python3.11 signed_hecke_middle_pauli_probe_audit.py
