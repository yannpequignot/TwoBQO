# TwoBQO

[![CI](https://github.com/yannpequignot/TwoBQO/actions/workflows/ci.yml/badge.svg)](https://github.com/yannpequignot/TwoBQO/actions/workflows/ci.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-purple.svg)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)

A self-contained Lean 4 / Mathlib formalization of **2-better-quasi-orders (2-BQO)**, staged as a
candidate Mathlib contribution.

A 2-BQO is a strengthening of well-quasi-order (WQO) phrased via *pair-sequences*
`f : ∀ m n, m < n → α` rather than plain sequences: a relation `r` is 2-BQO if every pair-sequence
has a *good triple* `m < n < l` with `r (f m n) (f n l)`. Unlike WQO, 2-BQO is closed under several
constructions WQO alone is not known to be closed under — most importantly infinite (lexicographic)
sums indexed by a 2-BQO and passage to sequences under a suitable embedding relation.

The theory follows Pequignot,
[*Towards better: A motivated introduction to better-quasi-orders*](https://ems.press/journals/emss/articles/15096),
EMS Surveys 2017.

## Files

Each file is `sorry`-free and builds against Mathlib `v4.28.0`.

| File | Contents | Suggested Mathlib path |
|------|----------|------------------------|
| [`RamseyInfinite.lean`](RamseyInfinite.lean) | Infinite Ramsey theorem at **arbitrary arity** `r` (`infinite_ramsey`), by induction on `r` via the iterated-pigeonhole "fan" argument, with colourings `Finset ℕ → κ` on `r`-subsets (matching B. Mehta's unported Lean 3 `inf_ramsey.lean`); enumeration form (`infinite_ramsey_seq`); and the classical relational pairs/triples (`infinite_ramsey_pairs`, `infinite_ramsey_triples`) derived from it. | `Mathlib/Combinatorics/Ramsey/Infinite.lean` |
| [`WQO.lean`](WQO.lean) | The **perfect/bad dichotomy** for sequences (`Sequences.perfect_or_bad`, straight from Ramsey for pairs) and, from it, the monotone-subsequence property of a WQO **without transitivity**: `WellQuasiOrdered.exists_monotone_subseq_lt` (strict, no typeclass) and `…_of_refl` (Mathlib's exact shape but only `[Std.Refl r]` instead of `[IsPreorder α r]`). | `Mathlib/Order/WellQuasiOrder.lean` |
| [`WellQuasiOrderRegular.lean`](WellQuasiOrderRegular.lean) | Regular sequences in a WQO (`WellQuasiOrdered.eventuallyRegular`), stabilization of antitone sequences, and Higman's order as a WQO on all of `List Q` (`WellQuasiOrdered.sublistForall₂`). | `Mathlib/Order/WellQuasiOrder/Regular.lean` |
| [`TwoBQO.lean`](TwoBQO.lean) | The 2-BQO theory: `PairSeq`, `TwoBQO`, and the closure/consequence theorems. | `Mathlib/Order/TwoBQO.lean` |

## Main results

- `TwoBQO.wellQuasiOrdered` — 2-BQO implies WQO.
- `TwoBQO.of_finite_coloring` — a preorder with a finite partial-order quotient is 2-BQO.
- `TwoBQO.of_wellFoundedLT`, `Ordinal.isTwoBQO` — well-founded linear orders (and ordinals) are 2-BQO.
- `TwoBQO.comap`, `TwoBQO.mono`, `TwoBQO.union`, `TwoBQO.prod`, `TwoBQO.pi` — closure under monotone
  preimage, relation weakening, covering by two parts, and finite products.
- `TwoBQO.lexSigmaQO` — closure under lexicographic sum along a 2-BQO index.
- `TwoBQO.dom_twoBQO` — the domination order on subsets of a 2-BQO is WQO.
- `TwoBQO.embedForAll_wqo` — the pointwise embedding preorder on `ℕ → Q` is WQO when `r` is 2-BQO.
- `WellQuasiOrdered.exists_monotone_subseq_of_refl` — every sequence in a WQO has a monotone
  subsequence assuming only `[Std.Refl r]`, **dropping the transitivity** carried by Mathlib's
  current `WellQuasiOrdered.exists_monotone_subseq` (answering a Zulip question of Leo Shine).

## Building

A standard Lake project pinned to Mathlib `v4.28.0`:

```sh
lake exe cache get   # download the prebuilt Mathlib oleans (do this first)
lake build           # kernel-checks all three files
```

`lake build` builds `TwoBQO` and, transitively, `RamseyInfinite` and `WellQuasiOrderRegular`.
CI runs the same build on every push (see the badge above).

## Status

Staged for a Mathlib contribution; not yet submitted. Naming, target file locations, and namespaces
are provisional and subject to discussion on the Mathlib Zulip.

## License

Released under the Apache 2.0 license, matching Mathlib. Copyright (c) 2026 Yann Pequignot.
