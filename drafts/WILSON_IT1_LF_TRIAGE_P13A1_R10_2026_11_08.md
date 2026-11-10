# Triage of lf-p13a1-20261108-r10

## Verdict

- r10 was a full round of 13a1 (#4.43–#4.50-2) at LF 9cc6351681fb, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1. #4.44-2 and #4.44-2-1 assert that 𝔛 := (1/i)log(V′^B₀(V′^A₀)^{−1}) is 𝔤-valued, and no line gives the condition that makes it so.
  - For general G, abs(U − 1) < 1 does not suffice. The referee's example is U = e^{2πi/7}·1 in SU(7), whose log is not traceless.
  - The condition is VAR (172)'s smallness at C₁′, already in (T-Λ).
- **Trivial:** t1–t5.
- The round is not clean, so 13a1's clean count stays 0. Round 9's m1 and t-a–t-c were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.50, #4.44-2-1 | 𝔛's 𝔤-valuedness not derived | #4.50 adds: "𝔛 is 𝔤-valued: abs(V′^B₀(V′^A₀)^{−1} − 1) < C_𝔛(M)ε_k ≤ ε₁ ≤ C₁′ε₁, and VAR (172) (p.305 l.33–36) writes such a G-valued datum as e^{iB′} with B′ in 𝔤, abs(B′) < 2C₁′ε₁, for ε₁ small, part of (T-Λ) (#4.50-1); Bałaban's logarithm returns B′ there, so 𝔛 = B′." #4.44-2-1 now says "𝔤-valued with V′^B₀ = e^{i𝔛}V′^A₀ by #4.50" |
| t1 | #4.48-3, new #4.48-3.0.0 | Z^{∼−2} used for MR_k-cubes, unqualified, after "for M₁-cubes" in #4.44-0.1 | The last sentence moves to #4.48-3.0.0: "Here Z^{∼−2} is read for MR_k-cubes, the cubes of LFR I p.179 l.8 (inferred, not printed). So … within the sup-distance 2MR_k of Z^c; for the M₁-cubes of #4.44-0.1 it lies nearer Z^c still, since M₁ < M." |
| t2 | #4.44 | Proposition 1's uniqueness domain unstated | "has exactly one critical orbit on the configurations of mild regularity on which (1.77) is defined (abs(∂V_k − 1) < a₁ on Z, p.194 l.32), a minimum" |
| t3 | #4.47 | c_K not rechecked for the weighted kernel | "…≤ 2B₀c_K abs(f)_{w_Λ,(−3)}, the weighted kernel L^{3(j−j′)_+}e^{−(15/16)δ₀d} being ≤ L^{3(j−j′)_+}e^{−½δ₀d}, the only part of the kernel that the count of c_K uses (#4.9-2-2)." This is simpler than the referee's route: #4.9-2-2's count runs at α = ½ and so sees only e^{−½δ₀d}. The kernel-form sentence, with ε₃'s definition, moves to the head of #4.47-0, where table row #T-ε₃ already points (#4.47-0) |
| t4 | #4.50-1.1.1-1 | "at every j" | "at matched scales, run A's j and run B's j + 1 (#CP.13-1; …)" |
| t5 (a) | #4.46-0 | (103)'s ε₃ is VAR's | "(103) (p.293 l.36–37; its ε₃ is VAR's of (114), not #4.47-0's)" |
| t5 (b) | #4.47-0 | C_N beside the dimension N | "C_N #4.33's constant, not a function of the dimension N" |
| t5 (c) | #4.47-0 | "the J-terms of the kernel form" | "it also covers the current J, which supplies ε₁ in VAR (85) (balaban_proofs/BP_VAR_PROP4_KERNEL.md #4.36-0)" |

## Checks

- **m1, re-derived.**
  - abs(V′^B₀(V′^A₀)^{−1} − 1) = abs(V′^B₀ − V′^A₀) < 2O(1)B₅M⁶ε_k = (2/π)C_𝔛(M)ε_k.
  - C_𝔛(M)ε_k ≤ ε₁ by C(M) ≥ C_𝔛(M) (#4.43-1.2), and ε₁ ≤ C₁′ε₁ since C₁′ = 4c_tot(1/128)C₁ ≥ 1.
  - VAR p.305 l.33–36 prints "abs(V′ − 1) < C₁ε₁, hence V′ = e^{iB′}, abs(B′) < 2C₁ε₁ on 𝔅_k, for ε₁ sufficiently small".
  - For B′ ∈ 𝔤 small, the spectrum of iB′ lies near 0, so the principal logarithm of e^{iB′} is iB′.
- **t3, re-derived.** #4.9-2-2 bounds the row sums with α = ½ in #4.9-1-1's count, that is, through Σe^{−½δ₀d}. Since 15/16 ≥ ½, the weighted kernel is pointwise below the kernel the count uses.
- **Line lengths:** #4.44 489, #4.44-2-1 260, #4.46-0 465, #4.47 542, #4.47-0 517, #4.48-3 366, #4.48-3.0.0 349, #4.50 591, and #4.50-1.1.1-1 603 characters.
- No CRLF. The only new tag is #4.48-3.0.0. ε₃'s definition {#D.ε₃.c} moves from #4.47 to #4.47-0, the line the table's row already cites.

## Rounds

- **Next: 13b1 r15 (full),** then 13b2 r15 (full).
- **Then 13a1 r11.** It will be narrow, on the lines changed since r10, so it can be the first clean round. A full r12 would follow.

## Pre-check of lf-p13b1-20261108-r15 (full)

- **Spec.** specs\spec_p13b1_r15.json at LF a100b37e1628, prior lf-p13b-20261108-r14. --check gives 0 conflicts (2 allowed).
- **Size.** 9.9k of reviewed lines, with #4.561 as context.
- **Reading.** I read the whole part, as recorded in WILSON_IT1_LF_TRIAGE_P13B_R14_2026_11_08.md (*Reading of 13b before its full round, and the split*). No gap was found.
- **Changed since r14:** #4.52-1-1.1-1 (o1), #4.556, and #4.560-2 (pointers). r10's repairs are outside 13b1. #4.560-1.1.2 cites #4.50's a priori location, and #4.50's added sentence leaves that bound unchanged.
- **New tags.** 13b1 is a new part name, so the gate finds no prior round of it. Its changed tags are computed by hand: #4.52-1-1.1-1, #4.556, and #4.560-2.
- No known weak point and no OPEN is in these lines.

## SHAs

LF 9cc6351681fb (r10's snapshot) → 613cc9ffae31 (13b pointers) → a100b37e1628 (r10's repairs). Table 6d09b1b5054d (unchanged).
