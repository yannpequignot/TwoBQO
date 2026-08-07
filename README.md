# NashWilliams

[![CI](https://github.com/yannpequignot/NashWilliams/actions/workflows/ci.yml/badge.svg)](https://github.com/yannpequignot/NashWilliams/actions/workflows/ci.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-purple.svg)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)

A Lean 4 / Mathlib formalization of **Nash-Williams fronts**, the **infinite Ramsey theorem**, and
**2-better-quasi-orders (2-BQO)**, staged for contribution to Mathlib.

The theory follows Pequignot,
[*Towards better: A motivated introduction to better-quasi-orders*](https://ems.press/journals/emss/articles/15096),
EMS Surveys 2017.

Every file is `sorry`-free, builds against Mathlib `v4.28.0`, and is warning-free under Mathlib's
own linter set (`linter.mathlibStandardSet`, enabled in [`lakefile.lean`](lakefile.lean)).

## Layout mirrors Mathlib

The tree under `NashWilliams/` mirrors the Mathlib paths these files are staged for, so
upstreaming is a `NashWilliams` → `Mathlib` prefix swap in both paths and imports. (A literal
top-level `Mathlib/` directory is not usable here — it would shadow the Mathlib dependency.)

| File | Upstream target | Contents |
|------|-----------------|----------|
| [`Data/Nat/Nth.lean`](NashWilliams/Data/Nat/Nth.lean) | `Mathlib/Data/Nat/Nth.lean` | `Set.Infinite.exists_strictMono_range` and its membership form: an infinite `X ⊆ ℕ` as a strictly monotone enumeration. |
| [`Data/Fintype/Pigeonhole.lean`](NashWilliams/Data/Fintype/Pigeonhole.lean) | `Mathlib/Data/Fintype/Pigeonhole.lean` | `exists_infinite_fiber_nat`: a finitely-valued sequence on `ℕ` is constant on an infinite set. |
| [`Combinatorics/Ramsey/Infinite.lean`](NashWilliams/Combinatorics/Ramsey/Infinite.lean) | `Mathlib/Combinatorics/Ramsey/Infinite.lean` | Infinite Ramsey at **arbitrary arity** (`infinite_ramsey`), by induction on the arity via the iterated-pigeonhole "fan" argument; the enumeration form `infinite_ramsey_seq`; and the classical relational `infinite_ramsey_pairs` / `infinite_ramsey_triples`. |
| [`Combinatorics/Front/Defs.lean`](NashWilliams/Combinatorics/Front/Defs.lean) | `Mathlib/Combinatorics/Front/Defs.lean` | `IsFront`, the initial-segment relation `IsInit`, the uniform fronts `powK` (`[M]^k`) and the Schreier front. |
| [`Combinatorics/Front/Rank.lean`](NashWilliams/Combinatorics/Front/Rank.lean) | `Mathlib/Combinatorics/Front/Rank.lean` | The tree of a front, well-foundedness of proper end-extension, and the ordinal `IsFront.rank`. |
| [`Combinatorics/Front/Ray.lean`](NashWilliams/Combinatorics/Front/Ray.lean) | `Mathlib/Combinatorics/Front/Ray.lean` | The ray `F after a` and `IsFront.ray_rank_lt`. |
| [`Combinatorics/Front/Shrink.lean`](NashWilliams/Combinatorics/Front/Shrink.lean) | `Mathlib/Combinatorics/Front/Shrink.lean` | Restriction `F ↾ N` of a front to an infinite subset, and `IsFront.shrink_rank_le`. |
| [`Combinatorics/Front/NashWilliams.lean`](NashWilliams/Combinatorics/Front/NashWilliams.lean) | `Mathlib/Combinatorics/Front/NashWilliams.lean` | The Nash-Williams theorem, its finite-colour version, and infinite Ramsey re-derived from it. |
| [`Order/WellQuasiOrder.lean`](NashWilliams/Order/WellQuasiOrder.lean) | `Mathlib/Order/WellQuasiOrder.lean` ⚠️ **existing file** | The perfect/bad dichotomy, and the monotone-subsequence property of a WQO **without transitivity**. Contents are to be *appended* to Mathlib's file, not added as a new one. |
| [`Order/WellQuasiOrder/Regular.lean`](NashWilliams/Order/WellQuasiOrder/Regular.lean) | `Mathlib/Order/WellQuasiOrder/Regular.lean` | Regular sequences in a WQO, stabilization of antitone sequences, and Higman's order as a WQO on `List Q`. |
| [`Order/TwoBQO.lean`](NashWilliams/Order/TwoBQO.lean) | `Mathlib/Order/TwoBQO.lean` | The 2-BQO theory: `PairSeq`, `TwoBQO`, and the closure/consequence theorems. |

Paths, names and namespaces are **provisional** and subject to discussion on the Mathlib Zulip —
in particular the choice of `Combinatorics/Front/` for the front development, since Mathlib
currently has neither a `Combinatorics/Ramsey/` nor a `Combinatorics/Front/` directory.

## Main results

**Fronts and Nash-Williams**

- `Front.IsFront.rank` — every front has an ordinal rank (proper end-extension on its tree is
  well-founded); `Front.powK_rank` and `Front.schreier_rank` compute it for `[M]^k` and the
  Schreier front.
- `Front.IsFront.nash_williams` — a 2-colouring of a front admits a monochromatic sub-front, by
  recursion on the rank.
- `Front.IsFront.nash_williams_fin` — the finite-colour version.

**Infinite Ramsey**

- `infinite_ramsey` / `infinite_ramsey_seq` — arbitrary finite arity, proved directly.
- `Front.ramsey_seq_of_nashWilliams` — the same statement, proved a second way by instantiating
  Nash-Williams at the uniform front `[M]^k`.

**Well- and better-quasi-orders**

- `WellQuasiOrdered.exists_monotone_subseq_lt` — every sequence in a WQO has a monotone
  subsequence, **dropping the transitivity** carried by Mathlib's current
  `WellQuasiOrdered.exists_monotone_subseq` (answering a Zulip question of Leo Shine).
- `TwoBQO.wellQuasiOrdered` — 2-BQO implies WQO.
- `TwoBQO.of_finite_coloring` — a preorder with a finite partial-order quotient is 2-BQO.
- `TwoBQO.of_wellFoundedLT`, `Ordinal.isTwoBQO` — well-founded linear orders (and ordinals) are
  2-BQO.
- `TwoBQO.comap`, `.mono`, `.union`, `.prod`, `.pi` — closure under monotone preimage, relation
  weakening, covering by two parts, and finite products.
- `TwoBQO.lexSigmaQO` — closure under lexicographic sum along a 2-BQO index.
- `TwoBQO.dom_twoBQO` — the domination order on subsets of a 2-BQO is WQO.
- `TwoBQO.embedForAll_wqo` — the pointwise embedding preorder on `ℕ → Q` is WQO when `r` is 2-BQO.

## Two proofs of infinite Ramsey

The infinite Ramsey theorem is proved twice, deliberately: once directly by iterated pigeonhole,
and once as a corollary of Nash-Williams applied to the uniform front `[M]^k`. Both are kept.

The two are **independent**: neither file imports the other, and they share only the generic
helpers in `NashWilliams/Data/`. So the front development can be upstreamed, deferred, or dropped
without affecting the direct proof, and vice versa.

## Upstreaming roadmap

Ordered by how self-contained each block is. Each is independently PR-able.

1. **Small gap-fillers.** `WellQuasiOrdered.exists_monotone_subseq_lt`; `List.IsPrefix.head?_eq`;
   the `List.SublistForall₂` `IsPreorder` instance; `RelHom.rank_le` (the cross-relation companion
   to `IsWellFounded.rank_lt_of_rel`); and the two `Data/` helpers. One lemma each.
2. **`Combinatorics/Ramsey/Infinite.lean`.** Mathlib has no infinite Ramsey theorem at all.
3. **`Order/WellQuasiOrder/Regular.lean` and `Order/TwoBQO.lean`.**
4. **`Combinatorics/Front/*`** and the Nash-Williams-derived Ramsey proof.

To upstream: fork `leanprover-community/mathlib4` (`origin` = your fork, `upstream` = mathlib4)
per the [git guide](https://leanprover-community.github.io/contribute/git.html), branch off
`master`, and copy the relevant files with `NashWilliams` → `Mathlib` swapped in paths and
imports. Open one focused PR per block.

## Known follow-ups

- `Front.tree` re-implements the prefix-closure already provided by
  `Mathlib.SetTheory.Descriptive.Tree`, and `Front.mem_tree_ray` is essentially `Tree.subAt`.
  Reusing that API is the main cleanup wanted before tier 4 goes upstream.
- `Sequences.{IsBad, IsPerfect, perfect_or_bad}` in `Order/WellQuasiOrder.lean` duplicates
  `PairSeq.{IsBad, IsPerfect, perfect_or_bad}` in `Order/TwoBQO.lean`.
- `Order/TwoBQO.lean` declares most names by dotted prefix at root rather than in `namespace`
  blocks, and hosts `Preorder.IsRegularSeq.exists_strictMono_dominating`, which belongs in
  `Order/WellQuasiOrder/Regular.lean`.
- `List.IsPrefix.head?_eq` is not `protected`, unlike neighbouring Mathlib `IsPrefix` lemmas.

## Building

```sh
lake exe cache get   # download the prebuilt Mathlib oleans (do this first)
lake build           # kernel-checks the whole development
```

`lake build` builds `NashWilliams.lean`, which imports every module. A green build asserts more
than compilation: Mathlib's linters run over every file, and each headline theorem is followed by
a `#guard_msgs`-wrapped `#print axioms`, so a green build also certifies that the development
rests only on the standard axioms — in particular that it is `sorry`-free.

To check that `NashWilliams.lean` still imports everything after adding a file:

```sh
lake exe mk_all --lib NashWilliams --check
```

## License

Released under the Apache 2.0 license, matching Mathlib. Copyright (c) 2026 Yann Pequignot.
