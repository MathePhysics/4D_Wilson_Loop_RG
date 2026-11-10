# Packet 14bp (balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md), round 3, 9 Nov 2026

## Pre-check of bp-p14bp-20261109-r3 (narrow)

- **Lines under review:** #C10.3.21–#C10.3.21-5, #C10.3.21-8–#C10.3.21-8-1, and #C10.3.23–#C10.3.24-4, that is, r2's changed lines and their consumers. #C10.3.21-6–#C10.3.21-7-2 and #C10.3.22–#C10.3.22-1, unchanged since r2, are context. The whole file was re-read on 9 Nov 2026.
- **Re-derived (the r2 repairs):**
  - m1, #C10.3.21: γ runs along Γ to x, along [x, x′] in +μ, and back along −Γ′. If μ is Γ's last direction with n_μ < 0, Γ's last bond is the first bond of [x, x′] reversed. If μ is Γ′'s last direction with n_μ > 0, −Γ′ traverses the last bond of [x, x′] in −μ.
  - m2, #C10.3.21-8: with log h = iP, d log at h is the inverse of dexp_P.
  - m3, #C10.3.23-4: e^{iω(c₋)}W̄(c)e^{−iω(c₊)} = e^{i(ω(c₋) − Ad(W̄(c))ω(c₊))}W̄(c) to first order, which is e^{−iLηD_{W̄}ω}W̄. D*_{W̄} for (Lη)^dΣ_c and (Lη)^dΣ_y gives the leaving and entering terms with the signs of #C10.3.23-2–#C10.3.23-3.
  - m4, #C10.3.24-2: T = Ad(e^{iY}) − dexp_Y∘S with S = avg Σ dlog_h∘Ad(h), so T* = Ad(e^{−iY}) − S*∘dexp_Y* with S* = avg Σ Ad(h^{−1})dlog_h*. |T*| ≤ x + ((1 + x)³ − 1) ≤ x + 3.39x ≤ 5x.
  - #C10.3.21-8: (e^a − 1 − a)/a = 0.0652 ≤ 0.53a at a = 1/8, and 0.53·4/(1 − 0.066) ≤ 2.27 ≤ 2.4.
  - #C10.3.24-3: 5x(1 + 2dL^{d−1}) + 5xL^{d−1} ≤ 10(d + 1)xL^{d−1}.
  - #C10.3.24-4: x ≤ 4c_{av}C₀ε₁L^{2(i+1−n)} ≤ 4c_{av}C₀ε₁ ≤ 1/(20(d + 1)L^{d−1}).
- **Repair made in this pre-check:** #C10.3.24-1 bounded the change of an entering contour term by (1 + x)³ − 1 + x. That term multiplies four operators, each within x of the identity, so its change is at most (1 + x)⁴ − 1 = 4x + 6x² + 4x³ + x⁴ ≤ 4.82x at x ≤ 1/8. The old expression omitted the factor 1 + x on the first part, and the r2 pre-check had accepted it. The line now reads "(1 + x)⁴ − 1 ≤ 5x times its weight (x ≤ 1/8)"; the bound 5x is unchanged.
- **Definition check:** 0 conflicts (8 allowed, as in r2).
- **Size:** reviewed blocks 5.05k characters. CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600.
- **Spec:** specs\spec_p14bp_r3.json (BP 9f13883742ef, Cauchy 3802c8fb4ced, LF 56d172c27cf2).
- **Order:** after 14a r3.

Written 2026-11-09 06:49.

- **Update (07:29, SHA at 07:36):** the spec now carries Cauchy ab50fa4809fd, after 14b r2's repairs. Its Cauchy context extracts (#C10.3.1-5, #C9.8.1–#C9.8.1-2, #C10.1.4–#C10.1.4-0-3, #C10.3.17–#C10.3.20, and #C10.3.25–#C10.3.28) are unchanged against the 14b r2 snapshot. Definition check: 0 conflicts (8 allowed).
- **Built** at 08:06 (BP 9f13883742ef, Cauchy 03f0376a8c65, LF 6ac728004094, table 0d6adc9e81d4, LABELS 9faef7334bc0). The Cauchy context extracts are unchanged against the 14a r3 snapshot (ab50fa4809fd); 14a r3's repairs and the M8b pre-check touch none of them. Definition check: 0 conflicts (8 allowed). Launched at 08:06.

## Verdict of bp-p14bp-20261109-r3 (narrow)

- No fatal and no serious finding. There are two minor notational findings, m1 and m2, both valid, so the round is not clean. Every named step is CORRECT, including the five changes since r2. The referee re-derived the double occurrences, dlog_h, the site adjoint, (1 + x)⁴ − 1 ≤ 4.81x, and the adjoint T*.
- **Observation, context only:** RG I p.252 l.29 prints "|n_μ| ≤ L−1/2", which is (L − 1)/2 for the cube of side δ centred at y (inferred, not printed). #C10.1.4-0-1 derives |n_ν| ≤ L/2 from the cube, which holds under either reading, and the double occurrences need only |n_μ| < L. No change.

## Repairs (BP 9f13883742ef → 4bfff254a6d7)

| Finding | Line | Repair |
| --- | --- | --- |
| m1: the displayed group omits the orientation sign of b on Γ | #C10.3.23-4 | The group now reads L^{−1}Σ_{x̂}Σ_{Γ∋b}±… with ± the sign of b on Γ (#C10.3.21-2). #C10.3.23-5 uses absolute values and is unchanged. |
| m2: which end-point of b the transport reaches | #C10.3.21-2, #C10.3.21-3 | #C10.3.21-2 now states the term ±Ad(W(γ from c₋ to b₋))iηA(b), + along the orientation of b (b excluded from the transport) and − against it (b included). P_{b,Γ} runs from c₋ to b₋. #C10.3.21-3: P_{b,Γ′} runs from c₊ to b₋, since the part of γ after b₋ is the reverse of Γ′ from c₊ to b₋ in both orientations. |

- **Re-derived:** with W(b) ↦ e^{iηA(b)}W(b), a forward factor W(b) gives W(before)iηA(b)W(b)W(after)W(γ)^{−1} = Ad(W(before))iηA(b), and a backward factor W(b)^{−1} gives −Ad(W(before)W(b)^{−1})iηA(b). Both transports end at b₋. For the entering occurrence, Γ′ = Γ, so P_{b,Γ′} = P_{b,Γ} and the sign is opposite to the leaving one, as #C10.3.23-3 states.
- **Consumers:** #C10.3.23-3 and #C10.3.23-5 in this file, and Cauchy #C10.3.31-2 (the column weights), which are unchanged.
- **Hygiene:** CR 0, no trailing spaces, no duplicate tags, and no line over 600.

## Next

- r4, narrow (#C10.3.21-2–#C10.3.21-3 and #C10.3.23-3–#C10.3.23-5, the rest as context), as the first clean round. Then r5, full, after 14b2 r3.

Written 2026-11-09 08:15.
