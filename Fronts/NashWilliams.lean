/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Fronts.Ray
import Fronts.Shrink

/-!
# The Nash-Williams theorem

The Nash-Williams theorem: a 2-coloring (equivalently, a subset `S`) of a front `F` on `M` admits a
monochromatic sub-front, i.e. an infinite `X ⊆ M` with `F | X ⊆ S` or `F | X ∩ S = ∅`. Here `F | X`
is `shrink F (M ∘ e)` for the increasing enumeration `M ∘ e` of `X`.

This file stages the development:

* `IsFront.nash_williams` — the base 2-color/subset theorem (rank recursion; proof in progress).
* `IsFront.nash_williams_fin` — the finite-color version, by induction on colors and
  color-blurring.
* `Front.ramsey_seq_of_nashWilliams` — the finite-arity infinite Ramsey theorem, obtained by
  instantiating the finite-color version at the uniform front `[M]^k` (`powK`). This re-derives
  `infinite_ramsey_seq` from the Nash-Williams theorem, independently of the direct iterated-
  pigeonhole proof in `RamseyInfinite`.

Supporting lemmas:

* `Front.shrink_shrink` — restricting twice collapses to a single restriction.
* `Front.shrink_powK` — the restriction of a uniform front is the uniform front on the subset.
-/

open Set List

set_option autoImplicit false

noncomputable section

namespace Front

variable {F : Set (List ℕ)} {M : ℕ → ℕ}

/-! ### Stage 1: the base 2-color / subset theorem -/

/-- **The Nash-Williams theorem (subset form).** For a front `F` on `M` and any subset `S`, there
is an infinite subset `M ∘ e ⊆ M` on which the restricted front `shrink F (M ∘ e)` is entirely
inside `S` or entirely outside `S`.

Proved by transfinite recursion on `hF.rank` (the *ray recursion*); proof in progress. -/
theorem IsFront.nash_williams (hF : IsFront F M) (S : Set (List ℕ)) :
    ∃ e : ℕ → ℕ, StrictMono e ∧
      (shrink F (M ∘ e) ⊆ S ∨ Disjoint (shrink F (M ∘ e)) S) := by
  sorry

/-! ### Restriction helpers -/

/-- Restricting twice to nested subsets collapses to the inner restriction. -/
theorem shrink_shrink {N N' : ℕ → ℕ} (h : Set.range N' ⊆ Set.range N) :
    shrink (shrink F N) N' = shrink F N' := by
  sorry

/-- The restriction of the uniform front `[M]^k` to an infinite subset `M ∘ e` is the uniform front
`[M ∘ e]^k` on that subset. -/
theorem shrink_powK (hM : StrictMono M) {e : ℕ → ℕ} (he : StrictMono e) (k : ℕ) :
    shrink (powK M k) (M ∘ e) = powK (M ∘ e) k := by
  sorry

/-! ### Stage 2: the finite-color version -/

/-- **Finite-color Nash-Williams.** For a front `F` on `M` and a coloring `c` of finite lists by a
finite palette `κ`, there is an infinite subset `M ∘ e ⊆ M` on which `c` is constant over the
restricted front.

Obtained from `IsFront.nash_williams` by induction on `‖κ‖` with color-blurring: split off one
color as a subset `S`, apply the base theorem, and recurse into the smaller palette on the
disjoint side (a front via `shrink_isFront`), composing restrictions with `shrink_shrink`. -/
theorem IsFront.nash_williams_fin (hF : IsFront F M) {κ : Type*} [Finite κ] (c : List ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ, ∀ s ∈ shrink F (M ∘ e), c s = col := by
  sorry

/-! ### Stage 3: the finite-arity infinite Ramsey theorem -/

/-- **Infinite Ramsey at arbitrary finite arity, via Nash-Williams.** A finite coloring `c` of the
size-`k` subsets of `ℕ` admits a strictly monotone `e` and a color `col` such that every size-`k`
subset of `range e` has color `col`.

Obtained by applying `IsFront.nash_williams_fin` to the uniform front `[ℕ]^k` (`powK id k`) with
the list-coloring `s ↦ c s.toFinset`, rewriting the restricted front via `shrink_powK`, and
bridging the size-`k` `Finset`s with their sorted lists. This matches `infinite_ramsey_seq` and
re-derives it from the Nash-Williams theorem. -/
theorem ramsey_seq_of_nashWilliams {κ : Type*} [Finite κ] (k : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = k → c t = col := by
  sorry

end Front
