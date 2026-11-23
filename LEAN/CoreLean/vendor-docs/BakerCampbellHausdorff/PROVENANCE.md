# BakerCampbellHausdorff in CoreLean

Source: `C:\Users\Terinuva\Documents\Lean\Libraries\BakerCampbellHausdorff`, v0.4 (2026-10-08),
written for Mathlib `8d52ea9a` on Lean `v4.34.0-rc2`. Copied on 2026-11-21 into
`CoreLean/BakerCampbellHausdorff/` and `CoreLean/BakerCampbellHausdorff.lean`, built as the Lake
library `BakerCampbellHausdorff` of this project (Mathlib `v4.36.0`). Before the copy, the 17
`.lean` files were checked against the library's `SHA256SUMS.txt` (all match); `README.md`,
`STATUS.md` and `SHA256SUMS.txt` are kept in this folder.

Changes, all in `MulSeries.lean`, needed for Mathlib `v4.36.0`:

1. `MultilinearMap 𝕂 …` became `MultilinearMap (RingHom.id 𝕂) …` (multilinear maps are now
   semilinear over a ring homomorphism).
2. `RingHom.id_apply` was added to the two `simp only` calls of `map_update_smul'`.
3. `set_option maxHeartbeats 1000000 in` was put before `le_radius_mulSeries`.

The other 16 files are unchanged. After the changes the whole library builds, and the 78
declarations of the library's `checks/Axioms.lean` depend only on `propext`, `Classical.choice`
and `Quot.sound`.
