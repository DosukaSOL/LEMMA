# Patch 0002: never silently drop a constructor payload

| | |
|---|---|
| **File** | `LeanSVM/Compiler/Lower.lean` (`valToReg`) |
| **Diff** | [`0002-no-silent-payload-loss.patch`](0002-no-silent-payload-loss.patch) (applies after patch 0001) |
| **Severity** | Soundness: the compiled program computed a different value from the Lean program, with no warning |
| **Effect on upstream examples** | None: all 8 example `.so` files are byte-identical |

## The bug

`valToReg` turns a lowered value into a single 64-bit register. For a constructor with a tag other
than 0 and one field, such as `Option.some q`, it returned **only the tag** and threw away the
field. The same happened for dynamically tagged constructors (`dynCtor tag payloads`).

This happens whenever such a value must fit in one register, for example when an `Option` flows
through an `if` join point or out of a function with several return branches:

```lean
let r := if mode == 0 then mulDivFloor a b d else mulDivCeil a b d   -- Option UInt64
match r with
| none => SolanaM.fail 7
| some q => SolanaM.require (q == c) Err.invalidArgument
```

Upstream compiles this without complaint, but the join block only receives the tag. When
`some q` is matched, `q` reads as the constant `0`. In LEMMA's `mulDiv` differential suite this
pattern gave **6,978 wrong results**, while the Lean definitions were proven correct.

## The fix

If the constructor has a runtime payload, `valToReg` now throws a compile error naming the
problem. If the payload is erased (proof-only or unit), it still returns the tag as before. So the
compiler either compiles the program correctly or rejects it; it no longer miscompiles it.

LEMMA's own on-chain code does not pass `Option`s through join points. The math library exposes
`SolanaM` versions (`mulDivFloorM`, `mulDivCeilM`), which upstream lowers correctly, and proves
them equal to the pure `Option` specifications (`mulDivFloorM_eq`, `mulDivCeilM_eq`).

## Verification

- Regression test `LemmaTest.Patch0002.p_optionJoin` (in `tests/LemmaTest/NatProbes.lean`):
  - with the patch, it is rejected at compile time;
  - without it, it compiles (confirmed), and that compiled code gave the wrong results above.
- All 8 upstream example binaries are byte-identical, and all upstream compiler proofs still check.

## What is NOT done

- Proper support for multi-register `Option`/sum values at join points. That would be the real
  feature; this patch only makes the gap safe.
- A full audit of other places where the lowering could lose data. This bug was found by
  differential testing, not by review, and there may be others. Differential tests stay mandatory
  for every LEMMA program.
