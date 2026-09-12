#!/bin/bash
#SBATCH --job-name=hecke-literal-pauli
#SBATCH --partition=sioux
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --output=signed-hecke-literal-pauli-probe-%j.out

set -euo pipefail
repository_root="${1:?usage: sbatch signed_hecke_literal_pauli_probe_audit.sbatch REPOSITORY_ROOT}"
cd "$repository_root/experiments"
/usr/bin/python3.11 signed_hecke_literal_pauli_probe_audit.py
