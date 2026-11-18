"""How wide must a feature be before the corner term is local?  (plan item P2)

Rectangles of fixed length ell = 12 and widths w = 3, 6, 9, 12 are compared with the additive prediction E_f = alpha P + b c, with
(alpha, b) fitted on the seven loops of `corner_locality.THICK` at the same K.  The deviation d(w) = E_f - (alpha P + b c) is
printed and plotted against w.  Two torus sizes are used, K = 6 (side 18) and K = 8 (side 24), to show how much of d(w) is finite size.

Reading the result.  The fit set contains rectangles of width 6, 9 and 12, so d(w) for w >= 6 is partly fitted by construction; the
informative point is how large d(3) is next to them, and whether d(w) is a decreasing function of w.  The block side is L = 3, so if the
failure of locality has range L the deviation should vanish from w = 2L = 6 on, to within the oscillation of 0.006 already seen in the
leave-one-out errors.  If not, this script shows it.  Numeric only; U(1) analogue; no bound or proof is tested.

    python3 width_scan.py                  K = 6 and K = 8 (about 3 minutes)
    python3 width_scan.py --no-show --save-dir figures
"""
import os
import sys

import numpy as np

from loop_energy import energies, fit, counts, rect
import corner_locality as cl

ELL = 12
WIDTHS = {6: (3, 6, 9), 8: (3, 6, 9, 12)}
_CACHE = {}


def run(K):
    """dict with alpha, b, and for each width the (P, c, E, deviation) at torus size K."""
    if K not in _CACHE:
        names = list(cl.THICK)
        scan = [rect(ELL, w) for w in WIDTHS[K]]
        E = energies([cl.THICK[n] for n in names] + scan, K)
        Et, Es = E[:len(names)], E[len(names):]
        P = [counts(cl.THICK[n])[0] for n in names]
        c = [counts(cl.THICK[n])[1] for n in names]
        a, b = fit(P, c, Et)
        out = dict(alpha=a, b=b, widths=WIDTHS[K], rows=[])
        for w, e, s in zip(WIDTHS[K], Es, scan):
            Pw, cw = counts(s)
            out["rows"].append(dict(w=w, P=Pw, c=cw, E=float(e), dev=float(e - (a * Pw + b * cw))))
        _CACHE[K] = out
    return _CACHE[K]


def figure(save=None, show=True):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(6.5, 4.6))
    for K, col in ((6, "tab:blue"), (8, "tab:red")):
        r = run(K)
        ax.plot([x["w"] for x in r["rows"]], [x["dev"] for x in r["rows"]], "o-", color=col,
                label="K = %d (torus side %d); fit alpha = %.4f, b = %.4f" % (K, 3 * K, r["alpha"], r["b"]))
    ax.axhspan(-0.006, 0.006, color="0.85", label="size of the oscillation (leave-one-out, K = 6)")
    ax.axhline(0, color="k", lw=0.7)
    ax.axvline(3, color="0.5", ls=":", lw=0.8)
    ax.text(3.1, ax.get_ylim()[0] * 0.2, "w = L", fontsize=7)
    ax.set_xlabel("width w of the rectangle (fine units), length %d" % ELL)
    ax.set_ylabel("E_f - (alpha P + b c)")
    ax.set_title("Deviation from perimeter-plus-corners against width (U(1) analogue)", fontsize=9)
    ax.legend(fontsize=7)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    for K in (6, 8):
        r = run(K)
        print("K = %d: fit alpha = %.4f, b = %.4f" % (K, r["alpha"], r["b"]))
        for x in r["rows"]:
            print("   rectangle %dx%-2d  P = %2d  c = %d  E_f = %.5f  deviation %+.4f" % (ELL, x["w"], x["P"], x["c"], x["E"], x["dev"]))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "width_scan.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
