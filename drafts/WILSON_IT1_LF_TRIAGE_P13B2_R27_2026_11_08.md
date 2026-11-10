# LF triage, part 13b2, round 27 (lf-p13b2-20261108-r27, narrow), 8 Nov 2026

## Verdict

Not clean. No fatal or serious finding. One minor (m1) and six trivial points (t1–t6). Every named step was CORRECT; m1 concerns the support of #4.567-2's second sentence.

## Repairs

| Finding | Repair | Lines |
|---|---|---|
| m1: #4.567-2 cites the class coverage of log d to #C8.6.2-16, which is Bałaban's statement for 𝐔 ∈ U^c_k(Z, α_{0,k}, α_{1,k}) (LFR II p.358 l.26–31), with no check that the class points lie there | Derived. A point of the class lies in 𝒫_k(X; r) for a domain X ⊃ Z. Its restriction to Z satisfies (i)–(iii) of run A's U^c_k (#C5.5-1), and the lift satisfies run B's (#C5.5-2, #C5.6-3); these are pointwise or per-cube conditions. (iv) follows by RG I (1.17) at ¼α (run A) and < 0.4α (run B). At every coupling between g^A_k and g^B_{k+1}, the CRE (2.28) thresholds are ≥ 0.8α (#C5.7-3, #4.562-1). Run B's data are the lift's averages (#C3.2, #4.5-2). So Bałaban's p.357–358 bounds apply within their printed scope. | new #4.567-3, #4.567-3-1, #4.567-3-2, #4.567-3-3; #4.567-2 rewritten; #4.155, #4.169-1 and Cauchy #C8.6.2-16 re-pointed |
| t1: the g_k²·g_k^{−2} cancellation is per run | reworded in place | #4.168-1 |
| t2: "the data built from U_0" omits V″ | replaced by "U^0_{k,Z}'s data" (#4.168-1 lists them) | #4.567-2 |
| t3: α₁ used in two senses in #4.561 | Proposition 6's smallness thresholds named without α₁ | #4.561 |
| t4: G-valued averages of G-valued fields uncited | CMP98 (15) and its composition (p.31 l.31) cited once; #4.561.1-1-0 points to it | #4.561.1, #4.561.1-1-0 |
| t5: LFR I Proposition 1's condition abs(B′) < ε not stated | stated at B′ = B^e(z), 𝔤^c-valued, with 2c_avε′_k < 20C_{V′}ε₁′ | #4.563-1.1 |
| t6: deeper-layer points of a q-block | a q-block's points lie in layers n ≥ q, where the factors L^{2(q−n)} and L^{q−n} ≤ 1 give (52) at α̂₀ and the field bound 26α̂₁ | #4.561.1-0.0-1 |

## Inputs pass on the repair (finished 13:17)

- #4.567-3 reads LFR II p.358 l.24–31 (transcript p358.tex), RG I p.262 (definition (i)–(iv)), CRE p.261 ((2.34)–(2.39)) and LFR II p.377 l.7–10.
- **Scope.** d and U_0 read the configuration only on Z: LFR II (1.1)–(1.3) and the table row #T11.30.
- **X ⊃ Z.** A polymer contains its components (p.389 l.27–28, as #C8.6.19 quotes it). A factor's domain Y contains the components of Z^∼ that it meets (p.377 l.7–8).
- **Radii.**
  - r = α/(8B₃).
  - (i)–(iii) hold at r (run A) and at e^{2β_I}r ≤ 0.2α (run B).
  - (iv) holds at 2B₃r = ¼α (run A) and at e^{2β_I}α/4 < 0.4α (run B), using e^{2β_I} < 1.6 from #C5.7-3.
  - All of these are below 0.8α, which is at most the threshold at every coupling in between.
- **Run B.**
  - The data are the lift's averages: Mι_X𝐔 = 𝐔 (#C3.2), and run B's constraints are run A's composed with M (#4.5-2).
  - The lift's orbit is one orbit (#C5.5-9).
  - Run B's index at Z's scale is k + 1 (#4.5-2, #C5.7-3).
- **Bałaban's items used.** These are exactly the bounds that #C8.6.4–#C8.6.7 read:
  - #C8.6.4: U_0's plaquettes (p.357 l.46–48);
  - #C8.6.6: the form (p.358 l.23–24), (1.6) and V (p.357 l.9–10);
  - #C8.6.6-3 and #C8.6.7-4: (1.10)–(1.11).
- **Name check.** The threshold notation α_i(g) was not introduced, because it would clash with the pair class's α₁ (#4.60). The text writes CRE's α_{i,j} instead.

**Open item for #4.169 (localised pieces, its own packet), not in 13b2.**
- Bałaban states V(Y) analytic on CRE's Ũ^c_k(Y, α̃₀, α̃₁) (p.377 l.9–10).
- That space includes (2.35) and (2.37), which the norm class 𝒫_k does not impose directly (#T11.14).
- #4.169-1 now cites #4.567-3 for d at points of the class, and Bałaban's own localisation at his representation configurations (p.369 l.7, p.373 l.10–17).
- Since round 28 the class of (LF-2) is the norm class at the radii r (#0.3, #4.472-0, #4.559-2). Whether V(Y)'s Ũ^c bounds hold at its points therefore rests on #4.523's claim that norm-class points satisfy CRE (2.34)–(2.39) at r. Of these, (2.35), (2.37) and (2.38) are open (WILSON_IT1_LF_TRIAGE_P13B2_R28_2026_11_08.md, open item for packet 47). This must be closed before #4.169's packet and packet 47. The comparison of 13b2 does not use #4.169-1 any more: #4.567-2 cites #4.567-3 directly.

## Pre-check for r28 (lf-p13b2-20261108-r28, narrow)

**Changed lines, each re-read:**
- In the packet: #4.561, #4.561.1, #4.561.1-0.0-1, #4.561.1-1-0, #4.563-1.1, #4.567-2, #4.567-3, #4.567-3-1, #4.567-3-2, #4.567-3-3.
- In the context: #4.168-1.
- Outside the packet: #4.155 and #4.169-1 (pointers), and Cauchy #C8.6.2-16.

**Consumers checked:**
- #4.563 cites #4.561.1-0.0-1, which is unchanged in content.
- #4.564 lists #4.567–#4.567-2; #4.567-3 is the support of #4.567-2.
- #4.568 is unchanged.

**Sizes and format:**
- Lines are ≤ 600 characters: #4.567-3 is 503, -3-1 529, -3-2 346 and -3-3 about 360.
- Packet argument: 23,901 characters (r27: 23,680). The context extract was narrowed to #4.559–#4.559-0, since 13b1 is done and cited by tag.
- CR count 0. The build has 28 files.

**Symbols:**
- No new symbols.
- r, r_{·,k} (#4.523), β_I (#C5.5-2, #T3.13), α_{i,j} (#T3.13, CRE (2.28)) and 𝒫_k (#T11.14) are cited, not restated.

**Citations, each quoted and checked:**
- RG I p.262 l.14 ("a union of orbits"), (1.11)–(1.14), and (1.17) at p.263 l.7–17 (as #C5.5-6 reads it).
- LFR II p.358 l.26–31.
- CRE (2.28) via #C5.7-3.
- CMP98 (15) at p.19 l.46, and p.31 l.31 ("a composition of k averaging operations").
- LFR I Proposition 1, l.46–48 ("abs(B′) < ε").

**Snapshot (the build at 13:17):** LF 16a7cb388027, Cauchy 4c3f931eee83, table 47f87bcff833, LABELS f6c81739a1a2. Rebuilt at 13:21 with LABELS 56bbd7dae965: 28 files, 23,901 characters. The gate lists the 11 changed tags above, matching this pre-check.

## Messages

- About 13:18, to the table fork: the LF and Cauchy SHAs, the new tags, a relabel request, and verification of 47f87bcff833 / f6c81739a1a2.
- 13:23, from the fork: table 7a23c2fa110e, LABELS 1aa9e2a3e9c5. The only change is BC's F₀ in #T12.27-6, which 13b2 doesn't cite. I verified both SHAs and rebuilt r28 at 13:23 so the snapshot carries them: 28 files, 23,901 characters.
- 13:20, from the fork: relabelled at LF 16a7cb388027. The table is 47f87bcff833 (unchanged) and LABELS is 56bbd7dae965, with 1434 rows. I verified both SHAs, and #4.567-3–#4.567-3-3 are present in LABELS.

## SHAs

LF aa91a5e94142 → 16a7cb388027; Cauchy f7bf7d6045cd → 4c3f931eee83.
