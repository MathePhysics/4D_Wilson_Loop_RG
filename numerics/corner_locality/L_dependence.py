"""How do the perimeter and corner constants depend on the block size L?  (the programme needs L odd and larger than 11)

`../abelian_first_step` fixes L = 3.  Its operators accept any odd L, so the same squares are run here at L = 5 (K = 4 blocks per side,
torus side 20; squares of side nL for n = 1, 2) and compared with the published L = 3 values.  From two sizes, E_f = alpha P + beta gives
alpha (energy per fine link) and beta (intercept, four corners).  The numbers are stored in `results/`; the run took 20 minutes
(building the L = 5 averaging operator alone takes over a minute) and is skipped when the stored file exists.

What to expect and what not.  Dimensionally alpha is a fine-lattice quantity, so a change with L says how the constants depend on the blocking
factor in this analogue, not that they converge to a limit: two L values cannot show a trend, and L = 5 is far from L > 11.  The pair (n = 1, 2)
is a poor estimate of the constants even at L = 3: it gives alpha = 0.1724 and beta = -0.213, against 0.1707 and -0.17 to -0.18 from the
larger sizes, so differences of that size between the two L values are within the pair's own scatter.  The torus (side 20, with the n = 2 square
of side 10 spanning half of it) was not checked for finite-size effects at L = 5; at L = 3 such effects were below 1e-3.  Numeric, U(1)
analogue, landau gauge, no bound or proof tested.

    python3 L_dependence.py              prints the table (computes L = 5 if results/d4_L5_K4_landau.json is missing)
    python3 L_dependence.py --no-show --save-dir figures
"""
import json
import os
import sys
import time

import numpy as np

_HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(_HERE, "..", "abelian_first_step"))
import abelian_first_step as af  # noqa: E402

PUBLISHED_L3 = {1: 1.855780, 2: 3.924427, 3: 5.970860, 4: 8.022657, 5: 10.071188}      # ../abelian_first_step/README.md, landau, K = 10 (n <= 3), 8
RESULT = os.path.join(_HERE, "results", "d4_L5_K4_landau.json")


def compute_L5(path=RESULT, ns=(1, 2), K=4):
    if os.path.isfile(path):
        return json.load(open(path))
    t = time.time()
    r = af.loop_energies(4, 5, K, ns, gauges=("landau",))
    out = dict(d=4, L=5, K=K, n=list(ns), gauge="landau", seconds=time.time() - t, E={str(n): float(r[("landau", n)]) for n in ns})
    os.makedirs(os.path.dirname(path), exist_ok=True)
    json.dump(out, open(path, "w"), indent=1)
    return out


def alpha_beta(L, E):
    """alpha, beta from the first two sizes: E = alpha P + beta with P = 4 n L."""
    n1, n2 = sorted(E)[:2]
    P1, P2 = 4 * n1 * L, 4 * n2 * L
    a = (E[n2] - E[n1]) / (P2 - P1)
    return a, E[n1] - a * P1


def table():
    r5 = compute_L5()
    E5 = {int(k): v for k, v in r5["E"].items()}
    a3, b3 = alpha_beta(3, {1: PUBLISHED_L3[1], 2: PUBLISHED_L3[2]})
    a5, b5 = alpha_beta(5, E5)
    return dict(L3=dict(E={1: PUBLISHED_L3[1], 2: PUBLISHED_L3[2]}, alpha=a3, beta=b3), L5=dict(E=E5, alpha=a5, beta=b5, K=r5["K"]))


def figure(save=None, show=True):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    t = table()
    fig, ax = plt.subplots(1, 2, figsize=(11, 4.4))
    for key, L, col in (("L3", 3, "tab:blue"), ("L5", 5, "tab:red")):
        n = sorted(t[key]["E"])
        P = np.array([4 * k * L for k in n])
        ax[0].plot(P, [t[key]["E"][k] for k in n], "o", color=col, label="L = %d: alpha %.4f, beta %.3f" % (L, t[key]["alpha"], t[key]["beta"]))
        pp = np.linspace(0, max(P) * 1.1, 10)
        ax[0].plot(pp, t[key]["alpha"] * pp + t[key]["beta"], "-", color=col, lw=0.8)
    ax[0].set_xlabel("perimeter P (fine links)")
    ax[0].set_ylabel("E_f")
    ax[0].legend(fontsize=8)
    ax[0].set_title("squares of side nL, n = 1, 2 (landau)", fontsize=9)
    ax[1].bar([0, 1], [t["L3"]["alpha"] * 3, t["L5"]["alpha"] * 5], color=["tab:blue", "tab:red"])
    ax[1].set_xticks([0, 1])
    ax[1].set_xticklabels(["L = 3", "L = 5"])
    ax[1].set_ylabel("alpha x L  (energy per block length)")
    ax[1].set_title("same data, per block side instead of per fine link", fontsize=9)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    t = table()
    for key, L in (("L3", 3), ("L5", 5)):
        print("L = %d: E_f(n) = %s   alpha = %.4f   beta = %.4f   (4 b = beta)" % (L, ", ".join("%d: %.5f" % kv for kv in sorted(t[key]["E"].items())), t[key]["alpha"], t[key]["beta"]))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "L_dependence.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
