# Is the corner term local?  Loops other than squares in the abelian first-step check

A companion to [`../abelian_first_step`](../abelian_first_step/README.md). That check fits `E_f = αP + β` for square Wilson loops, where every loop has
four corners of one kind, so `β/4` is the only corner constant it can see. The first RG step of the programme treats a corner as a local object with its
own factor `z_c`. These scripts test the weakest version of that in the U(1) Gaussian analogue: whether **one constant per corner** predicts the energy of
rectangles, L-shapes and loops spanning three directions, and how the answer depends on where the loop sits against the blocks.

**This is a sanity check of structure in the abelian analogue, not a test of any bound or proof in the repository.** Like the rest of the repository
it was written with LLM assistance and has not been independently reviewed. Labels: *Exact* = identity or symmetry checked to rounding, *Numeric* = a
computed number, with tolerances chosen after seeing the data where stated, *Hypothesis* = not shown.

All numbers: 4-torus, block side `L = 3`, `K = 6` blocks per side (18⁴ fine sites) unless stated, `landau` gauge, `g = 1`. `P` is the number of links and
`c` the number of corners (places where consecutive links change direction).

## Files

| File | Purpose | Run time |
|---|---|---|
| `loop_energy.py` | `E_f` for any closed loop, and its split over the loop's links, importing the operators of `../abelian_first_step` (no momentum folding) | – |
| `corner_locality.py` | fits `E_f = αP + b c` on rectangles, L-shapes, three-direction loops; figure `corner_locality.png` | 40 s |
| `width_scan.py` | rectangles of length 12 and widths 3, 6, 9, 12 against the fit, at K = 6 and 8 | 3 min |
| `offset_average.py` | every loop at all 81 positions modulo the block period; figure `offset_average.png` | 3 min |
| `contour_map.py` | splits `E_f` over the links of a loop and over its corners; figure `contour_map.png` | 3 min |
| `gauge_compare.py` | landau against xi1 for the same loops and for a shifted square; figure `gauge_compare.png` | 2 min |
| `L_dependence.py` | the same squares at L = 5 (K = 4) against the published L = 3; stored in `results/`; figure `L_dependence.png` | 20 min once, then instant |
| `test_corner_locality.py` | the checks below (`--full` adds the 81-offset study) | 8 min, 11 min with `--full` |

```
python3 test_corner_locality.py --full
python3 corner_locality.py --save-dir figures
python3 width_scan.py --save-dir figures
python3 offset_average.py --save-dir figures
python3 contour_map.py --save-dir figures
python3 gauge_compare.py --save-dir figures
python3 L_dependence.py --save-dir figures       # recomputes L = 5 only if results/ is empty
```

## Results

**R1. At the offset used by the square fits, the corner term is local when features are at least two blocks wide (Numeric).**
Loops: squares of side 6 and 9, rectangles 6×9 and 6×12, an L-shape (9×9 with a 6×6 corner removed), and two loops spanning three directions.
With the loop's corner at the origin (a block centre, offset `(0,0,0,0)`), `E_f = αP + b c` fits with `α = 0.1709` per link and `b = −0.0444` per corner
(`4b = −0.178`; the published square fit is `α = 0.1707`, `β` between −0.17 and −0.18). Each loop left out is predicted to 0.006 or better. The
tolerance in the test is 0.01: a first guess of 0.005 was too tight. Squares reproduce the published K = 10 values to 2e-3, and `E_f` is unchanged to 1e-9
under permuting axes, reversing the loop and translating by `L`. *Exact* symmetries, *Numeric* fit.

**R2. At that offset a feature one block wide breaks it, and the range is `L` (Numeric).**
Rectangles of length 12 have deviation `E_f − (αP + b c)` of −0.037 at width 3, +0.003 at 6, 0.000 at 9 and 0.000 at 12 (K = 6 and K = 8 agree to 0.001).
The squares of side 3 and the thin L-shapes sit 0.016 to 0.039 below the fit. Widths 6 and above are partly in the fit set, so the point is the size of the
width-3 deficit next to them.

**R3. The offset matters more than the corner term (Numeric). R2's deficit is specific to offset `(0,0,0,0)`.**
The coarse lattice has period 3, so `E_f` depends on the loop's position modulo 3 in each of the four directions. Over all 81 positions:

- `(0,0,0,0)` is the **lowest** energy for all eight loops tried.
- The spread (maximum minus minimum) is 0.28 to 0.91 per loop. That is 15–25% of `E_f`, and larger than the whole corner term (`|4b| = 0.18`).
- Averaging over the 81 positions changes the fit to `α = 0.1906`, `b = −0.0618` (`4b = −0.247`): 12% larger in `α`, 39% larger in `b`.
- The averaged data are still roughly additive (leave-one-out error 0.023, against 0.006 at the single offset), but the width-3 deficit disappears: the squares of side 3 and the 3×9 rectangle now lie 0.019 and 0.022 *above* the averaged fit.

So the published coefficients `α = 0.1707`, `β ≈ −0.17` belong to the most favourable placement, and the "thin loops are below the fit" statement of R2 is a statement about that placement.
The loops here are placed on the torus at a fixed offset and nothing in this analogue says which offset the programme's construction corresponds to. The
programme's blocks are placed relative to the loop by its own conventions that I have not compared with, so read R3 as a property of this analogue.

**R4. The energy is carried by the links near a corner, and the corner constant is the same for convex and concave turns (Numeric).**
`contour_map.py` splits `E_f` into `c_l = J_l (ΓJ)_l` over the links of the loop (the sum reproduces `E_f` to 1e-9). On the aligned square of side 9, `c_l` is 0.170 on
the straight parts and drops to 0.154 on the link at a corner, recovering within three links, the block size. Assigning each link to its nearest corner, the four corners of the
aligned square have excess −0.0402 to −0.0404 over the loop's own edge value (−0.0445 to −0.0458 over the fitted `α`). In the L-shape the concave corner has excess
−0.0425 against a convex mean of −0.0447 (over `α`), inside the spread of the five convex corners (−0.0416 to −0.0479). So the one constant per corner does not depend on the turn direction in this analogue.

**R5. Of the placement effect in R3, most is the edge value, not the corner (Numeric).** Shifting the square of side 9 by `(1,1,0,0)` raises `E_f` from 5.970 to 6.375. Its edge value moves from 0.1703 to 0.1805 (6%),
which accounts for about 0.37 of the 0.41 difference over its 36 links, and its per-corner excess over that edge value changes from −0.040 to −0.031 (23% smaller in size), about 0.04 in total. The measure
of R4 against the *fitted* `α` is not meaningful for a shifted loop (it gives +0.05 to +0.07 per corner because the edge value moved); the corner excess has to be taken from the loop's own edge value, which needs a side
longer than six, so only the squares have it.

**R6. The gauge condition does not move the corner constant at the aligned placement (Numeric).** `xi1` differs from `landau` by 0.0001 to 0.0007 for every rectangle,
L-shape and three-direction loop (the published squares: below 6e-4), and the fitted `α` and `b` agree to four digits (`α = 0.1709`, `b = −0.0444` and `−0.0445`). For the square of side 9 shifted by `(1,1,0,0)` the
difference is 0.009, ten times larger and still 0.14% of its energy.

**R7. A single L = 5 run: α and β are larger than at L = 3 (Numeric, weak).** At L = 5 (K = 4, torus side 20), squares of side 5 and 10 give `E_f = 3.7613` and `7.8426`, so `α = 0.2041` and `β = −0.320` from that pair,
against `α = 0.1724`, `β = −0.213` from the same pair (n = 1, 2) at L = 3. The pair is itself a poor estimate: at L = 3 it is 1% off in `α` and about 20% off in `β` relative to the larger-size fits (0.1707; −0.17 to −0.18). So
the data say `α` grows by more than 15% from L = 3 to 5, which is well outside that scatter, and `β` is more negative, which is of the same order as it. They do not say how the constants behave towards L > 11,
which the programme needs, and the finite-size error of the K = 4 torus at L = 5 was not checked.

## What this does not test

- **No 60° or 120° corners.** The hypercubic action sees every turn between different axes as 90°. The corner types of a Spectre outline in the hexagonal lift are not distinguished here (see `../../GEOMETRY_BRIDGE.md`, open problem P1).
- **No non-abelian structure, no bound, no proof.** Nothing here checks any item in `STATUS_MAP.md`.
- **One block size almost everywhere.** All of R1 to R6 are at `L = 3` (K = 6 and 8); R7 is a single `L = 5` run with one size pair. The range found in R2 is stated in units of `L = 3` only because the width scan was not run at another `L`.
- **Prescription dependence beyond the two gauges.** R6 compares only `landau` and `xi1`; the programme's own cutoff test and gauge-fixing functional are not used.
- **Fit sets are small** (six or seven loops for two parameters), so "additive" means "consistent with additive to the quoted error", not a proof of locality.
