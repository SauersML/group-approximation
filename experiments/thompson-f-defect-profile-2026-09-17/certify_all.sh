#!/bin/sh
# Exact certificates C_n(F) >= B for the saved witnesses (see certify_ratio.py).
# Output: certify.out (n = 16, 32, 64) and certify_n128.out (n = 128, about 25 minutes).
cd "$(dirname "$0")"
{
  python3 certify_ratio.py wit_F_n16_tau1.8.npy --den 65536 --bound 3.536
  python3 certify_ratio.py wit_F_n32_warm_noise0.05.npy --den 65536 --bound 3.98
  python3 certify_ratio.py wit_F_n64_warm_noise0.08.npy --den 65536 --bound 4.23
} > certify.out
python3 certify_ratio.py wit_F_n128_warm_noise0.05.npy --den 16384 --bound 4.45 > certify_n128.out
