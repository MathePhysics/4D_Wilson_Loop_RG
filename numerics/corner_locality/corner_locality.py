"""Is E_f "perimeter plus corners"?  Fit E_f = alpha P + b c over rectangles, L-shapes and loops spanning three directions.

The abelian check of `../abelian_first_step` fits E_f = alpha P + beta for squares, where every loop has four corners of one type, so beta/4
is the only corner constant it can see.  This script asks whether that constant is *local*: whether one number per corner predicts the
energy of other shapes.  Results (K = 6, L = 3, landau gauge; numbers printed by the run):

  Numeric   with every feature at least 2L = 6 fine units wide, E_f = alpha P + b c holds: alpha ~ 0.171 per link, b ~ -0.044 per corner
            (4b ~ -0.18, the fork's square fit gives beta between -0.17 and -0.18), leave-one-out error below 0.01.
  Numeric   with a feature one block (3 units) wide, E_f lies 0.02 to 0.04 below that fit.
  Exact     squares reproduce the published K = 10 values to 2e-3 (finite-K difference); the energy is invariant under permuting axes,
            reversing the loop, and translating by L.

Tolerances were set after seeing the numbers (a first guess of 0.005 for the leave-one-out error was too tight; the largest miss is 0.006).
The hypercubic action sees every turn between different axes as a 90 degree corner; 60 and 120 degree corners are not tested.  This is a
sanity check in U(1); it does not test any bound or proof of the programme.

    python3 corner_locality.py                 run the loops, print the table, make the figure
    python3 corner_locality.py --no-show --save-dir figures
"""
import os
import sys

import numpy as np

from loop_energy import energies, fit, loo_errors, counts, rect, skew, lshape, reverse, permute

THICK = {"sq6": rect(6, 6), "sq9": rect(9, 9), "rec6x9": rect(6, 9), "rec6x12": rect(6, 12),
         "L9_6": lshape(9, 9, 6, 6), "skew666": skew(6, 6, 6), "skew669": skew(6, 6, 9)}
THIN = {"rec3x6": rect(3, 6), "rec3x12": rect(3, 12), "L6_3": lshape(6, 6, 3, 3), "L9_3": lshape(9, 9, 3, 3)}
SYM = {"sq3": rect(3, 3), "sq3_p02": rect(3, 3, (0, 2)), "sq3_p23": rect(3, 3, (2, 3)), "sq6_rev": reverse(rect(6, 6)),
       "sq6_shiftL": (rect(6, 6), (3, 0, 0, 0)), "sq6_perm": permute(rect(6, 6), (2, 0, 3, 1))}

_CACHE = {}


def run(K=6):
    """{name: dict(E, P, c, group)} for all loops (about 30 s at K = 6)."""
    if K not in _CACHE:
        allv = {}
        for g, d in (("thick", THICK), ("thin", THIN), ("sym", SYM)):
            for n, v in d.items():
                allv[n] = (v, g)
        names = list(allv)
        E = energies([allv[n][0] for n in names], K)
        info = {}
        for n, e in zip(names, E):
            v = allv[n][0]
            steps = v[0] if isinstance(v[0], list) else v
            P, c = counts(steps)
            info[n] = dict(E=float(e), P=P, c=c, group=allv[n][1])
        _CACHE[K] = info
    return _CACHE[K]


def thick_fit(info):
    names = list(THICK)
    P = [info[n]["P"] for n in names]
    c = [info[n]["c"] for n in names]
    E = [info[n]["E"] for n in names]
    a, b = fit(P, c, E)
    return a, b, loo_errors(P, c, E)


def figure(save=None, show=True, K=6):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Patch
    info = run(K)
    a, b, loo = thick_fit(info)
    groups = [("every feature >= 2L (fit set)", list(THICK), "tab:blue"), ("a feature one block (3 units) wide", list(THIN), "tab:orange")]
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.8))
    xs, lab, col = [], [], []
    for _, ns, cl in groups:
        for n in ns:
            xs.append(info[n]["E"] - (a * info[n]["P"] + b * info[n]["c"]))
            lab.append(n)
            col.append(cl)
    ax[0].bar(range(len(xs)), xs, color=col)
    ax[0].set_xticks(range(len(xs)))
    ax[0].set_xticklabels(lab, rotation=75, fontsize=7)
    ax[0].axhline(0, color="k", lw=0.7)
    ax[0].set_ylabel("E_f - (alpha P + b c)")
    ax[0].set_title("alpha = %.4f per link, b = %.4f per corner (K = %d, landau)" % (a, b, K), fontsize=9)
    ax[0].legend(handles=[Patch(color=cl, label=t) for t, _, cl in groups], fontsize=7)
    for t, ns, cl in groups:
        ax[1].scatter([info[n]["P"] for n in ns], [info[n]["E"] for n in ns], color=cl, label=t)
    pp = np.linspace(10, 64, 50)
    ax[1].plot(pp, a * pp + 4 * b, "k--", lw=0.8, label="alpha P + 4b (four corners)")
    ax[1].plot(pp, a * pp + 6 * b, "k:", lw=0.8, label="alpha P + 6b (six corners)")
    ax[1].set_xlabel("number of links P")
    ax[1].set_ylabel("E_f")
    ax[1].legend(fontsize=7)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    info = run()
    a, b, loo = thick_fit(info)
    print("%-11s %4s %3s %9s %9s" % ("loop", "P", "c", "E_f", "E - fit"))
    for n, r in info.items():
        print("%-11s %4d %3d %9.5f %+9.4f" % (n, r["P"], r["c"], r["E"], r["E"] - (a * r["P"] + b * r["c"])))
    print("fit on %d loops: alpha = %.4f, b = %.4f, 4b = %.3f, max leave-one-out %.4f" % (len(THICK), a, b, 4 * b, abs(loo).max()))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "corner_locality.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
