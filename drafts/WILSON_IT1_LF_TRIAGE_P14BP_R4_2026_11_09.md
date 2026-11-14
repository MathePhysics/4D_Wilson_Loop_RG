# Packet 14bp (balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md), round 4, 9 Nov 2026

## Pre-check of bp-p14bp-20261109-r4 (narrow)

- **Lines under review:** #C10.3.21-2–#C10.3.21-3 and #C10.3.23-3–#C10.3.23-5. These are r3's repaired lines, #C10.3.21-2, #C10.3.21-3, and #C10.3.23-4, with their consumers #C10.3.23-3 and #C10.3.23-5. The rest of the file, reviewed CORRECT in r3, is context.
- **Every changed line re-read** on 9 Nov 2026 (WILSON_IT1_LF_TRIAGE_P14BP_R3_2026_11_09.md).
- **Re-derived:**
  - The sign and the transport: a forward factor W(b) of W(γ) gives +Ad(W(γ from c₋ to b₋))iηA(b), with b excluded. A backward factor W(b)^{−1} gives −Ad(W(γ from c₋ to b₋))iηA(b), with b included, since γ arrives at b₋ after traversing b.
  - For b on −Γ′, in both orientations the part of γ after b₋ is the reverse of Γ′ from c₊ to b₋. So W(γ from c₋ to b₋) = W(γ)W(Γ′ from c₊ to b₋) = hW(c)W(Γ′ from c₊ to b₋).
  - The entering occurrence has Γ′ = Γ, so its transport is P_{b,Γ}, and its sign is opposite to the leaving one. The sign of b on Γ multiplies the whole group of #C10.3.23-4, since D*_{W̄} acts on ν at the block y and not on b.
  - #C10.3.23-5 takes absolute values, so the sign does not enter it.
- **Grep:** P_{b,Γ} and P_{b,Γ′} occur only in this file. Cauchy #C10.3.31-2 uses only the column weights, which are unchanged.
- **No known weak point** remains in the lines under review.
- **Definition check:** 0 conflicts (8 allowed, as in r3). The c_{av} entry now also cites table #T12.12(a) for the LF's c_av.
- **Size:** the reviewed lines are 1.31k characters (25k cap). CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600.
- **Spec:** specs\spec_p14bp_r4.json (BP 4bfff254a6d7, Cauchy d901e7a1b941, LF 6ac728004094).
- **Order:** after 14a r4 and 12b-bp r3. Rebuild at launch.

Written 2026-11-09 08:17.

- **Built** at 08:48 (BP 4bfff254a6d7, Cauchy 045261827913 after 14a r4's repairs and the packet-15 consolidation, which touch none of this packet's Cauchy context, LF 6ac728004094, table b9cb1fe93596, LABELS 39857d2caa24). Definition check: 0 conflicts (8 allowed). The argument field, context included, is 12.3k characters. Launched at 08:48, after 12b-bp r3's triage.

## Verdict of bp-p14bp-20261109-r4

No fatal or serious finding. Two minor expository findings (M1, M2) and one notational remark, all correct, all repaired by rewording the existing sentences. Not clean: next r5, narrow (the changed lines), then r6, full.

## Repairs

| Item | Finding | Repair |
|---|---|---|
| M1 | #C10.3.23-3 does not state that the entering terms carry the opposite orientation sign, which #C10.3.23-4 uses | #C10.3.23-3 now says "the entering ones after Ad(W(c))^{−1} and with the opposite sign, since −Γ′ traverses b against Γ′" |
| M2 | #C10.3.21-3's "the part of γ after b₋" is ambiguous, γ revisiting points (#C10.3.21) | now "the part of γ after this occurrence's visit to b₋" |
| remark | P_{b,Γ} denotes Ad of a transport, but #C10.3.21-2 calls it the transport | #C10.3.21-2 defines P_{b,Γ} := Ad(W(Γ from c₋ to b₋)), the adjoint action of the transport, and #C10.3.21-3 P_{b,Γ′} := Ad(W(Γ′ from c₊ to b₋)) |

- **Re-derived:** for b with sign s on Γ′, −Γ′ traverses b with sign −s. So the entering group is −s·Ad(W(c))^{−1}ν(c) carried by P_{b,Γ}*, and with the leaving +s·ν(c) the bracket is Σ_{c₋=y}ν(c) − Σ_{c₊=y}Ad(W̄(c))^{−1}ν(c) = −LηD*_{W̄}ν(y), as in #C10.3.23-4.
- **Consumers:** Cauchy #C10.3.31-2 counts "Ad(W(c))P_{b,Γ′}" as one transport of norm 1, which the Ad definition confirms. No other note uses P_{b,Γ}.
- **Hygiene:** CR 0, no trailing spaces, duplicate tags, or long lines.
- **Repaired SHA:** BP 0c5dc5ff8bfd.

Written 2026-11-09 08:54.
