# Extension-mechanism comparison: coupling vs witness replay vs closures

Run 2026-07-14 on AMD Ryzen 7 5800H, compiled executables (`lake exe verif
compare` and its verbatim ports).  One run per branch, each branch's own
extension mechanism enabled (`checkDProbing g order true`); the naive
no-extension baseline is mechanism-independent (see `2026-07-12.txt`).

| Branch | Mechanism | Commit | Notes |
|---|---|---|---|
| `coupling-extension` | coupling: replay the certifying tape bijection `T`; PIT fast-reject + exact structural/ANF acceptance | `8168703` + working tree | has multiplicative factoring |
| `replay-witness` | witness replay in the spirit of maskVerif: syntactic re-check of the rewrite witness on each candidate | `5841643` | **no factoring** (by design, mirrors maskVerif) |
| `closure-exploration` | closures: topological closure of the certified probe set | `085f748` | has factoring |

The benchmark list is `runCompare` in `Main.lean` (the full evaluation suite
plus the d+1 quadratic S-box family; `.ai/EVAL_EXAMPLES.md` has provenance).
Raw outputs: `compare-coupling_2026-07-14.txt`,
`compare-replay_2026-07-14.txt`, `compare-closure_2026-07-14.txt`.

Column key: C = coupling, R = replay, Cl = closure; verdicts S = secure,
I = INSECURE; **←** marks a verdict disagreement.  "free wires" is the
extension yield (wires certified for free beyond the chosen probes);
discharges = rewrite-engine calls.

| Example | d | verdict C/R/Cl | time ms C/R/Cl | discharges C/R/Cl | free wires C/R/Cl |
|---|---|---|---|---|---|
| ISW AND (2 shares) | 1 | S/S/S | 0/0/1 | 7/7/15 | 2/2/0 |
| ISW AND (3 shares) | 2 | S/S/S | 3/1/34 | 34/34/309 | 31/31/8 |
| ISW AND (4 shares) | 3 | S/S/S | 46/37/3190 | 338/338/10770 | 437/437/439 |
| ISW AND (5 shares) | 4 | S/S/S | 1125/845/409472 | 4735/4735/632834 | 8078/8078/37513 |
| DOM AND (2 shares) | 1 | S/S/S | 1/0/0 | 11/11/15 | 2/2/0 |
| DOM AND (2 shares) o2 | 2 | I/I/I | 0/0/1 | 2/2/6 | 0/0/2 |
| DOM AND (3 shares) | 2 | S/S/S | 5/4/35 | 88/88/325 | 44/44/7 |
| DOM AND (4 shares) | 3 | S/S/S | 104/90/3419 | 859/859/13291 | 784/784/532 |
| Trichina AND | 1 | S/S/S | 0/1/1 | 11/11/15 | 2/2/0 |
| Trichina AND (bad assoc) | 1 | I/I/I | 1/0/1 | 10/10/12 | 1/1/0 |
| TI AND (3 shares) | 1 | S/S/S | 0/0/1 | 9/9/27 | 9/9/0 |
| TI AND (3 shares) o2 | 2 | I/I/I | 1/1/1 | 10/10/10 | 5/5/2 |
| Additive refresh (3 shares) | 2 | S/S/S | 0/0/0 | 6/6/8 | 1/1/0 |
| Additive refresh (4 shares) | 3 | S/S/S | 1/0/1 | 11/11/17 | 6/6/0 |
| ISW refresh (3 shares) | 2 | S/S/S | 0/0/0 | 6/6/10 | 4/4/0 |
| ISW refresh (4 shares) | 3 | S/S/S | 0/1/2 | 12/12/51 | 24/24/0 |
| DOM Keccak χ (2 shares) | 1 | S/S/S | 14/11/29 | 49/49/107 | 29/29/5 |
| DOM Keccak χ (3 shares) | 2 | S/S/S | 2807/1797/11563 | 2865/2865/14047 | 2671/2671/645 |
| TI Keccak χ (3 shares) | 1 | S/S/S | 21/14/103 | 43/43/183 | 68/68/5 |
| TI Keccak χ (3 shares) o2 | 2 | I/I/I | 21/14/72 | 57/57/352 | 92/92/27 |
| Q⁴₁₂ (2-share direct) | 1 | S/I/S **←** | 2/2/5 | 27/26/47 | 16/16/10 |
| Q⁴₁₂ TI (3 shares) | 1 | S/S/S | 5/4/25 | 25/25/83 | 30/30/6 |
| TI Fides AB1 (4 shares) | 1 | S/S/S | 1941/972/36461 | 55/55/1127 | 537/537/14 |
| x+yz TI direct (3 shares) | 1 | S/S/S | 1/0/3 | 7/7/29 | 10/10/0 |
| x+yz TI with CT (3 shares) | 1 | S/S/S | 1/1/3 | 11/11/29 | 9/9/0 |
| x+yz TI (4 shares) | 2 | S/S/S | 11/8/170 | 78/78/767 | 115/115/20 |
| x+yz TI (4 shares) o3 | 3 | I/I/I | 11/7/8 | 102/102/72 | 99/99/15 |
| x+yz+xyz TI (4 shares) | 1 | S/S/S | 45/18/175 | 31/31/167 | 63/63/1 |
| xy TI virtual variable | 1 | S/S/S | 3/1/17 | 9/9/55 | 23/23/0 |
| xy TI virtual share | 1 | S/S/S | 1/0/7 | 9/9/37 | 15/15/0 |
| xy TI 4to3 shares | 1 | S/S/S | 1/1/3 | 11/11/25 | 8/8/0 |
| Q31 d+1 | 1 | S/S/S | 0/1/0 | 13/13/23 | 11/11/10 |
| Q32 d+1 | 1 | S/I/S **←** | 2/1/4 | 25/24/43 | 13/13/6 |
| Q33 d+1 | 1 | I/I/I | 4/2/7 | 18/18/32 | 22/22/2 |
| Q44 d+1 | 1 | S/S/S | 1/0/1 | 15/15/27 | 14/14/14 |
| Q412 d+1 | 1 | S/I/S **←** | 2/2/5 | 25/24/47 | 15/15/8 |
| Q4293 d+1 | 1 | S/I/S **←** | 4/2/6 | 31/24/59 | 20/20/8 |
| Q4294 d+1 | 1 | S/S/S | 1/1/3 | 23/23/39 | 16/16/12 |
| Q4299 d+1 | 1 | S/I/S **←** | 5/2/13 | 35/18/75 | 26/22/8 |
| Q4300 d+1 | 1 | I/I/I | 4/3/8 | 18/18/32 | 24/24/2 |

## Observations

1. **Verdicts.** Coupling and closure agree on all 40 entries (both engines
   retain multiplicative factoring).  Replay false-INSECUREs exactly the five
   factoring-family instances (Q⁴₁₂ 2-share direct, and the d+1
   quadratic-feedback classes Q³₂, Q⁴₁₂, Q⁴₂₉₃, Q⁴₂₉₉) — it is factoring-free
   by design, mirroring maskVerif.  All genuine flaws (I/I/I rows) are found
   by all three.

2. **Coupling vs replay: identical yield, small speed tax, strictly more
   verdicts.**  On every commonly-verified entry the discharge counts and
   free-wire yields are *identical to the digit* (e.g. ISW-5 @4:
   4735 discharges, 8078 free wires on both) — the coupling extension fully
   matches witness replay where replay works.  Replay is consistently
   1.3–2× faster in wall clock (no factoring attempts, cheaper syntactic
   acceptance: Fides 972 ms vs 1941 ms), but pays with the five false alarms.

3. **Coupling vs closure: same verdicts, dramatically different economics.**
   The closure extension yields far fewer free wires on the larger instances
   (Fides: 14 vs 537; DOM Keccak-3 @2: 645 vs 2671; ISW-3 @2: 8 vs 31), so
   the space-split degrades toward enumeration: ISW-5 @4 needs 632,834
   discharges and 409 s under closures vs 4,735 discharges and 1.1 s under
   coupling (~134× discharges, ~360× time); Fides 1,127 vs 55 discharges.

4. **Caveat for the write-up.**  The closure branch's engine predates several
   optimizations that landed on `coupling-extension` (module split, batched
   extension replay, shared eval caches), so raw wall-clock ratios overstate
   the mechanism gap; the mechanism-fair metrics are the discharge counts and
   free-wire yields, which are engine-version-insensitive.  Directionally the
   conclusion is unchanged: coupling attains replay's extension yield while
   keeping factoring's verdict quality, and closures trail on both.
