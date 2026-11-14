# Bridge figures: the Spectre outline, the hexagonal lift and the abelian first-step energy

Figures that connect [`../../GEOMETRY_BRIDGE.md`](../../GEOMETRY_BRIDGE.md) to the numerics of this repository. They read geometry from
[`spectre-monotile-py`](https://github.com/brentharts/spectre-monotile-py) (`lift4d.py`, `spectre_patch.py`; nothing is copied from it) and
the loop energies of [`../corner_locality`](../corner_locality/README.md).

**Nothing here tests a bound, estimate or proof of the programme.** Like the rest of the repository it was written with LLM assistance and has not been independently
reviewed. Labels: *Exact* = a finite enumeration or identity, checked by a test that can fail; *Numeric* = a computed number.

## Setup

```
make install            # in the repository root: clones spectre-monotile-py next to this repository
                        # or set SPECTRE_DIR=/path/to/spectre-monotile-py
```

## Files

| File | What it shows | Run time |
|---|---|---|
| `spectre_path.py` | finds the clone (`$SPECTRE_DIR`, else `../spectre-monotile-py`) | – |
| `spectre_contour_corners.py` | corner types of a Spectre outline on the hexagonal lattice; figure `spectre_contour_corners.png` | seconds |
| `lift_to_z4.py` | the same outline as links of Z⁴, two ways of writing the diagonals, and its energy against the perimeter-plus-corner prediction; figure `lift_to_z4.png` | 1 min |
| `scope_map.py` | the programme's own status labels (from `STATUS_MAP.md`) beside what the numerics compute; figure `scope_map.png` | seconds |
| `test_bridge_figs.py` | the checks below | 1 min (`--no-energy`: seconds) |

## Results

**B1. The corner types of a Spectre outline (Exact).** In the patch of level 2 (71 tiles), every tile outline has 14 edges and corners 7 × 60°, 6 × 90° and 1 straight pass. The edge colours (red:
even multiples of 30°, green: odd) split 8 + 6 for 63 tiles and 6 + 8 for the other 8, which are turned by an odd multiple of 30°, so the colour split is *not* the same for every tile; the corner counts are. A
corner between a red and a green edge is always 90°; between two edges of the same colour it is 60° or straight. A Spectre-shaped contour therefore has 60° corners, which the hypercubic action of
`../corner_locality` cannot represent (every turn between different axes is 90° there).

**B2. Written in Z⁴, the outline is not additive (Exact for the loops, Numeric for the energies).** One tile outline, written with each edge as one link or, for the diagonal hexagonal edges, two links, is a closed loop
of 18 links with 13 corners if the diagonals are written in increasing axis order and 17 in decreasing order. Their energies at the aligned placement (K = 6, L = 3, landau) are 2.797 and 2.649.
Against `E_f = αP + b c` with `α = 0.1709`, `b = −0.0444` (the seven thick loops of `corner_locality`) the deviations are +0.30 and +0.33; for dilations 2 and 3 they are +0.64, +0.66 and +0.31. The diagonals become staircases whose
corners are one link apart, and the additive form was only shown for corners at least three links apart. This is a statement about the hypercubic imitation of the outline, not about a hexagonal action; it says that the corner constant cannot be read off a Spectre-shaped
contour with the action available here. (The placement of the loop against the blocks also moves `E_f` by 0.3 to 0.9, see `../corner_locality/README.md` R3; only the aligned placement was used here.)

**B3. Scope (a chart, no result).** `scope_map.py` draws the label counts of `STATUS_MAP.md` and lists what each numerical study computes. It states, and does not test, that none of them touches a bound or proof.

## What this does not do

- No hexagonal action: the 60° corners of B1 are not given an energy anywhere in this repository. That needs a U(1) action and a block-averaging map on a triangular lattice (open problem P1 of `GEOMETRY_BRIDGE.md`).
- One tile, one placement, L = 3. The energies of B2 are for tile 0 of the patch; the other tiles have the same corner counts but were not run.
- The embedding of the lift lattice into E8 (`GEOMETRY_BRIDGE.md`, C2) is not used here; only the planar geometry is.
