# Packet 11 r15 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r15/review.md (changed lines), on LF 02bb1b22b20e, labels 02dad79f36c7, and table dc5e8a710045.

## Verdict

r15 has no fatal or serious finding and one minor finding, m-1, so it is **not clean**. It resolves r14's m-1 and T-1 to T-4. Its trivials t-1 to t-4 are repaired as well. r16 reviews the changed lines.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.7-1-3 (title), new #4.7-1-4, #4.7-1-4-1, #4.7-1-4-2, #4.7-2; table #T4.35 | #4.7-1-3 needs a layer j − 1 beyond Ω_j^c. 𝐁″_k has the whole lattice as its bottom domain (Γ″_0 = Ω″^c_1, LFR I (1.13)), and so has 𝐁. The joins' bottom domain is Ω of (2.14). Their points within 4M′ of ∂Ω take Bałaban's statement of LFR II p.370 l.35–38, quoted and accepted, with the reading labelled: the neighbourhood on both sides of ∂Ω″^∼_{h+1}, and the conditions (9)–(10) at the scale h. These give C₀ at a_h ≥ a_{j(x)}. |
| t-1 | new #4.7-1-1-1 | Half-open cubes; the widths of #4.22.3-0 in ℓ∞, an ℓ¹ width w giving w/d, with R′/d ≥ 12L in place of R′. |
| t-2 | #4.12-2-3 | CRE p.245 l.34 and l.38–40. |
| t-3 | #4.7-1, and the same pin at the R-operation regularity line | VAR p.278 l.50–p.279 l.4. |
| t-4 | #4.7-3-1; table #T4.35 | a₁^{(M′)}, VAR's a₁ at the product M′, as the Cauchy note's #C9.3 writes a₁^{(M_P)}. |

## Pre-check

- **Sources read.** LFR II p.370, rendered: (1.52)–(1.53), "These functions are supported in the domains Ω″^∼_{h+1}, (Ω″^∼_{h+1})^c correspondingly", and the passage quoted in #4.7-1-4-1, verbatim. LFR I p.179, rendered: (1.13), Γ″_0 = Ω″^c_1.
- **The reading.** The quantitative conditions are printed for (Ω″^∼_{h+1})^c ∩ Ω″^{∼2}_{h+1} only. The statement "in fact it is regular" covers the neighbourhood of the boundary. Reading it on both sides, with VAR's conditions at the scale h, is labelled as inferred, as #4.18-0 and #4.41-1-3-2 are.
- **Arithmetic.** With ℓ¹ widths: LR′/d ≥ 12L² > 4; R′/d ≥ 12L > 4L + 4; R′/(dL) ≥ 12 > 4; R′/d − 4 > 4 + 4/L.
- **Every use.** Only #4.7-2 claims "every point" from #4.7-1; it now cites #4.7-1-4. Table #T4.35 is updated. The two pins of "p.279 l.1–4" in the note are corrected.
- **Lines.** All under 600 characters; CR 0; no duplicate tags.

## Repaired files

LF dc8a61fc8643, table 3a1f61afdbe0, labels 23ab3967bc50 (multiply defined 101).
