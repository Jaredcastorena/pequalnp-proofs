# Partial monotone circuit lower bounds for L-meta-984

This research packet proves **25 of the 31 total lower bounds** in L-meta-984.
It does **not** prove the full 31-case statement.

Proved case indices: 0–18 and 21–26.
Remaining case indices: **19, 20, 27, 28, 29, 30**.

The final exports are in namespace `PEqualNP.Outside.L_meta_984_combine`:

- `twentyfive_totals`: the conjunction of the 25 proved total lower bounds.
- `conditional_missing_six`: the exact 31-case conclusion, conditional on the six explicitly named missing total bounds.
- `total24`: the newly integrated case 24 total lower bound.

All final theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`, `native_decide`, or new axiom declarations in this packet.
Source comments retain the attributions accompanying the reused helper proofs.

## Modules

| Module | Dependencies | Role |
|---|---|---|
| `PacketBase` | `Mathlib`, `PEqualNP.Defs` | All 31 AND bounds, 16 OR bounds, direct cases 16/22, and exact count assembly |
| `SharedSixCases` | `Mathlib`, `PEqualNP.Defs` | Six earlier general circuit bounds with shared generic helpers |
| `TwentyFourModular` | `PacketBase`, `SharedSixCases` | Compact cycle case 8 and the first 24 total bounds |
| `TwentyFiveModular` | `TwentyFourModular` | Case 24 OR bound, 25 totals, and the six-premise conditional theorem |

Use Lean 4.36.0 and the existing proof repository's pinned Mathlib dependency.
If these files are stored in `lean/Partial984`, run the following from `lean/`:

```sh
LEAN_PATH=Partial984 lake env lean -R Partial984 -o Partial984/PacketBase.olean Partial984/PacketBase.lean
LEAN_PATH=Partial984 lake env lean -R Partial984 -o Partial984/SharedSixCases.olean Partial984/SharedSixCases.lean
LEAN_PATH=Partial984 lake env lean -R Partial984 -o Partial984/TwentyFourModular.olean Partial984/TwentyFourModular.lean
LEAN_PATH=Partial984 lake env lean -R Partial984 -o Partial984/TwentyFiveModular.olean Partial984/TwentyFiveModular.lean
```

The first module contains expensive finite kernel certificates. The verified
module checks took approximately 445, 202, 5, and 33 seconds respectively on
the checking machine. The first check used approximately 29 GiB of memory.

This is a modular partial research contribution. It is not an eligible full
L-meta-984 submission: six cases remain open, and the current standalone
25-case candidate is 974,709 bytes, above the 512 KiB single-file limit.
