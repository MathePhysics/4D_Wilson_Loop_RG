# Packet 11 r16 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r16/review.md (changed lines), on LF dc8a61fc8643, labels 23ab3967bc50, and table 3a1f61afdbe0.

## Verdict

r16 has no fatal or serious finding. It has three minor findings, m-1 to m-3, and one trivial finding, t-1, so it is **not clean**. It resolves r15's m-1 in substance and r15's t-1 to t-4. r17 reviews the changed lines.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.7-1-4-1-0 (split from #4.7-1-4-1), new #4.7-1-4-1-1, #4.7-1-4-2 | The quotation now reads the printed domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}. #4.7-1-4-1-1 derives from it that both sides of ∂Ω″^∼_{h+1} are printed: ∂Ω lies on ∂Ω″^∼_{h+1} ∩ Z, each ∼ adds one layer of cubes (CRE p.245 l.40–43), LMR_{h+1} wide at the scale h, and LMR_{h+1} > 4dM′. #4.7-1-4-2 keeps only the reading of "regularity conditions typical for an h-order configuration", and records that any reading at a spacing ≥ a_{j(x)} with C₀ suffices. |
| m-2 | #4.528, new #4.7-1-5 to #4.7-1-5-2-1, #4.7-2, #4.7-1-1-1 | #4.528 is pinned to the proof's class (VAR p.300 l.28, l.36–37). The difference in indexing between the statement and the proof is recorded in #4.7-1-5. The covering is also derived for the proof's class: index-j cubes at M′ when δ⁺(x) ≥ 4M′, and index-(j + 1) cubes at 2M′ when δ⁺(x) < 4M′, both with C₀. So C₀^{ms} covers either indexing, and #4.7-2 says so. |
| m-3 | #4.7-1-4 | 𝐁's bottom domain comes from CRE (2.2), Γ_0 = Ω_1^c (p.255 l.12–16). The route through Λ is removed. |
| t-1 | #4.7-1-4-1 | "lie in no class cube" now reads "are covered by neither #4.7-1-2 nor #4.7-1-3, which has no layer beyond ∂Ω for them". |

## Pre-check

- **Sources read.**
  - LFR II p.370 l.35–37 (corrected part): the domain is "(Ω''_{h+1})^c ∩ Ω''^{∼2}_{h+1}", without the tilde on the first Ω.
  - CRE p.255 l.12–16: "For a sequence {Ω_j}, where Ω_j are considered as subsets of T_η, we denote Γ_0=Ω_1^c".
  - CRE p.245 l.40–43: "The operation ∼ … adding one layer of … cubes … in terms of which the sets are defined".
  - VAR p.300 l.28–37: "a cube □ intersecting Ω_j but not Ω_{j+1}, of a size 2ML^jη … M is a multiple of R₁M₁ … □̃ ⊂ B^{j−1}(Λ_{j−1})∪B^j(Λ_j) ⊂ Ω_{j−1}".
  - VAR p.278 l.50–p.279 l.4: the statement's class, □̃ ⊂ B^j ∪ B^{j+1} and □̃ ⊄ B^{j+1}.
- **Arithmetic for #4.7-1-5-1.**
  - □̃ lies within 4M′ of x.
  - The layer j − 1 is R′M′/L ≥ 12dM′ > 4M′ wide in the units a_j.
  - With ℓ¹ widths, R′/(dL) ≥ 12 > 4.
- **Arithmetic for #4.7-1-5-2 and #4.7-1-5-2-1.**
  - δ⁺ < 4M′a_j gives a distance < 4M′/L ≤ 2M′ in the units a_{j+1}.
  - The big blocks are ≤ 2M′a_{j+1}, so □ (side 4M′) reaches ≥ 2M′ towards y.
  - □̃ has side 4M′ + 4M′ = 8M′, and its reach is ≤ 6M′.
  - Ω_{j+2} is at ≥ R′M′ ≥ 24dM′.
  - Ω_j^c is at ≥ (R′ − 4)M′/L ≥ (12d − 2)M′ ≥ 10M′.
  - With ℓ¹ widths: R′/d ≥ 12L > 8, and (R′/d − 4)/L ≥ 10.
  - The bounds carry the factor 2L^{−p} ≤ 1 for p ≥ 1, the Hölder term L^{−(1+β)}.
  - M = 2M′ ≤ M(ε₁) since ε₁ ≤ a₁^{(M′)}/(2L).
- **Arithmetic for #4.7-1-4-1-1.**
  - A point at ℓ∞-distance < s from a set of side-s grid cubes lies in a touching cube, on both sides.
  - 4M′a_{j(x)} ≤ 4M′a_h < LMR_{h+1}a_h, since M > M₁ ≥ (12d + 1)M′ > 4dM′.
- **Every use.**
  - #4.7-1-4-2 is cited only in #4.7-1-5-1.
  - The table row #T4.35 still holds as written: it describes the statement's class, and #4.7-1-5 gives C₀ ≤ C₀^{ms}. It needs no edit.
  - The table's citation of #4.528 for LFR I's conditions is unchanged, since #4.528 was not split.
  - #4.7-1-1-1's range now runs to #4.7-1-5-2-1.
- **Lines.**
  - The new and changed lines are under 600 characters, except #4.528 at about 620, which is longer only by its pin.
  - #4.7-1-4-1 is split at the quotation into #4.7-1-4-1-0.
  - CR 0; no duplicate tags.

## Repaired files

LF 941aa3d49cc0, table 3a1f61afdbe0 (unchanged), labels a0d6f3509b45.
