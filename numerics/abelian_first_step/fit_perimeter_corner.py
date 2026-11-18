"""Fit E_f(n) = alpha * P + beta to the stored results, P = 4 n L fine units.

    python3 fit_perimeter_corner.py

kappa_C = exp(-(g^2/2) E_f) = exp(-delta_m P) z_c^4   =>
    delta_m * eps = (g^2/2) alpha,        log z_c = -(g^2/8) beta .
The slope between consecutive loop sizes is printed so that convergence in n is visible.
"""
import glob
import json
import os

here = os.path.dirname(os.path.abspath(__file__))
E = {}
for f in sorted(glob.glob(os.path.join(here, 'results', 'd4_L*_K*_n*.json'))):
    j = json.load(open(f))
    for k, v in j['E'].items():
        g, n = k.split(':')
        E[(g, j['L'], j['K'], int(n))] = v

for g in ('landau', 'xi1', 'total'):
    for L in sorted({k[1] for k in E}):
        # use the largest torus available for each n
        best = {}
        for (gg, LL, K, n), v in E.items():
            if gg == g and LL == L and (n not in best or K > best[n][0]):
                best[n] = (K, v)
        ns = sorted(best)
        if len(ns) < 2:
            continue
        print(f"gauge {g}, L={L}")
        for n in ns:
            print(f"   n={n} (P={4*n*L:3d}, K={best[n][0]:2d}): E_f = {best[n][1]:.6f}")
        for a, b in zip(ns, ns[1:]):
            P = 4 * L * (b - a)
            alpha = (best[b][1] - best[a][1]) / P
            beta = best[b][1] - alpha * 4 * L * b
            print(f"   slope n={a}->{b}: alpha = {alpha:.5f}   beta = {beta:.5f}   "
                  f"(delta_m*eps/g^2 = {alpha/2:.5f}, log z_c/g^2 = {-beta/8:.5f})")
