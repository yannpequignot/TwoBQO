/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Nth

/-!
# The infinite Ramsey theorem

This file proves the infinite Ramsey theorem for finite colourings of the `r`-element subsets of
`ℕ`, for arbitrary arity `r`, and derives the classical pairs (`RT²`) and triples (`RT³`) cases in
their relational form.

## Main results

* `infinite_ramsey`: for every finite colouring `c : Finset ℕ → κ` of the `r`-subsets and every
  infinite `M ⊆ ℕ`, there is an infinite `N ⊆ M` all of whose `r`-subsets get one colour. Proved
  by induction on `r` (the "fan" argument).
* `infinite_ramsey_seq`: the enumeration form — the monochromatic set is the range of a strictly
  monotone `e : ℕ → ℕ`.
* `infinite_ramsey_pairs`, `infinite_ramsey_triples`: the classical RT²/RT³ statements for
  colourings of ordered pairs `m < n` and triples `m < n < l`, derived from `infinite_ramsey`
  (`infinite_ramsey_pairs` from arity `2`; `infinite_ramsey_triples` by replaying the fan argument
  one level up on `infinite_ramsey_pairs`).

The `Finset ℕ` colouring interface follows B. Mehta's Lean 3 `inf_ramsey.lean`. See also the
standalone project https://github.com/yannpequignot/lean-infinite-ramsey.
-/
open Set
set_option autoImplicit false
noncomputable section

theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s :=
  ⟨Nat.nth (· ∈ s), Nat.nth_strictMono hs, Nat.nth_mem_of_infinite hs⟩

theorem exists_infinite_fiber_nat {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  exact ⟨k, Set.infinite_coe_iff.mp hk⟩

/-- Pigeonhole for a finite colouring of `ℕ`: some colour class is infinite, and can be
enumerated by a strictly monotone function. -/
theorem Function.exists_strictMono_eq_of_finite_coloring {κ : Type*} [Fintype κ]
    (f : ℕ → κ) : ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ k : κ, ∀ i, f (e i) = k := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  obtain ⟨e, he, hmem⟩ := (Set.infinite_coe_iff.mp hk).exists_strictMono
  exact ⟨e, he, k, hmem⟩

variable {κ : Type*}

private structure RamseyState (c : Finset ℕ → κ) (r : ℕ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hprop : ∀ t : Finset ℕ, ↑t ⊆ succ → t.card = r → c (insert vert t) = col

theorem infinite_ramsey [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by
  induction r generalizing c M with
  | zero =>
    refine ⟨M, subset_rfl, hM, c ∅, fun t _ ht => ?_⟩
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    have stepCore : ∀ S : Set ℕ, S.Infinite →
        ∃ a' ∈ S, ∃ (col' : κ) (N : Set ℕ),
          N.Infinite ∧ N ⊆ S ∧ (∀ x ∈ N, a' < x) ∧
          ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c (insert a' t) = col' := by
      intro S hS
      refine ⟨sInf S, Nat.sInf_mem hS.nonempty, ?_⟩
      have hle : ∀ x ∈ S, sInf S ≤ x := fun x hx => Nat.sInf_le hx
      have hdiff : (S \ {sInf S}).Infinite := hS.diff (Set.finite_singleton _)
      obtain ⟨N, hNsub, hNinf, col', hmono⟩ := ih (fun e => c (insert (sInf S) e)) hdiff
      refine ⟨col', N, hNinf, hNsub.trans Set.diff_subset, ?_, hmono⟩
      intro x hxN
      have hxd := hNsub hxN
      exact lt_of_le_of_ne (hle x hxd.1) fun h => hxd.2 (h ▸ rfl)
    have advance : ∀ s : RamseyState c r, ∃ s' : RamseyState c r,
        s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
      intro s
      obtain ⟨a', ha'mem, col', N, hNinf, hNsub, hNgt, hNprop⟩ := stepCore s.succ s.hInf
      exact ⟨⟨a', col', N, hNinf, hNgt, hNprop⟩, ha'mem, hNsub⟩
    obtain ⟨a₀, ha₀M, col₀, N₀, hN₀inf, hN₀sub, hN₀gt, hN₀prop⟩ := stepCore M hM
    let s₀ : RamseyState c r := ⟨a₀, col₀, N₀, hN₀inf, hN₀gt, hN₀prop⟩
    let states : ℕ → RamseyState c r := fun n => n.rec s₀ fun _ s => (advance s).choose
    have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
      fun n => (advance (states n)).choose_spec.1
    have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
      fun n => (advance (states n)).choose_spec.2
    have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
      fun n => (states n).hgt _ (I1 n)
    have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
      intro m n hmn
      induction n with
      | zero => simp [Nat.le_zero.mp hmn]
      | succ n ih2 =>
        rcases Nat.lt_or_eq_of_le hmn with h | rfl
        · exact (I2 n).trans (ih2 (Nat.lt_succ_iff.mp h))
        · exact subset_rfl
    have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
      intro m n hmn
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero m)
      | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
    have vmono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
    have hsuccM : ∀ n, (states n).succ ⊆ M := fun n => (I4 0 n (Nat.zero_le n)).trans hN₀sub
    have hvertM : ∀ n, (states n).vert ∈ M := by
      intro n
      cases n with
      | zero => exact ha₀M
      | succ n => exact hsuccM n (I1 n)
    obtain ⟨col, hJinf⟩ := exists_infinite_fiber_nat (fun n => (states n).col)
    set V : ℕ → ℕ := fun n => (states n).vert with hV
    set J : Set ℕ := {n | (states n).col = col} with hJ
    refine ⟨V '' J, ?_, hJinf.image (vmono.injective.injOn), col, ?_⟩
    · rintro x ⟨n, _, rfl⟩; exact hvertM n
    · intro t htN htcard
      have ht_ne : t.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact Nat.succ_pos r)
      set a := t.min' ht_ne with ha
      have ha_mem : a ∈ t := Finset.min'_mem _ _
      obtain ⟨m, hmJ, hVm⟩ : ∃ m, (states m).col = col ∧ (states m).vert = a := by
        obtain ⟨m, hmJ, hVm⟩ := htN (Finset.mem_coe.mpr ha_mem)
        exact ⟨m, hmJ, hVm⟩
      have hsub : ↑(t.erase a) ⊆ (states m).succ := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx
        obtain ⟨hxne, hxt⟩ := hx
        obtain ⟨p, hpJ, hVp⟩ := htN (Finset.mem_coe.mpr hxt)
        have hax : a < x := lt_of_le_of_ne (Finset.min'_le t x hxt) (Ne.symm hxne)
        have hmp : m < p := by
          have h1 : (states m).vert < (states p).vert := by
            rw [hVm, show (states p).vert = x from hVp]; exact hax
          exact vmono.lt_iff_lt.mp h1
        have := I5 m p hmp
        rwa [show (states p).vert = x from hVp] at this
      have hcard : (t.erase a).card = r := by
        rw [Finset.card_erase_of_mem ha_mem, htcard]; omega
      have key := (states m).hprop (t.erase a) hsub hcard
      rw [hVm, Finset.insert_erase ha_mem, hmJ] at key
      exact key

theorem infinite_ramsey_seq [Finite κ] (r : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = r → c t = col := by
  obtain ⟨N, _, hNinf, col, hcol⟩ := infinite_ramsey r c (M := Set.univ) Set.infinite_univ
  obtain ⟨e, he, hmem⟩ := hNinf.exists_strictMono
  exact ⟨e, he, col, fun t htsub htcard =>
    hcol t (htsub.trans (Set.range_subset_iff.mpr hmem)) htcard⟩

/-- **The infinite Ramsey theorem for pairs (RT²)**, in relational form: for a finite colouring
`c` of the ordered pairs `m < n`, there is a strictly monotone `e` and a colour `k` with
`c (e i) (e j) = k` for all `i < j`. Derived from `infinite_ramsey_seq` at arity `2`. -/
theorem infinite_ramsey_pairs {κ : Type*} [Fintype κ] (c : ∀ (m n : ℕ), m < n → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ i j : ℕ, (h : i < j) → c (e i) (e j) (he h) = k := by
  classical
  -- Colour a finite set by `c` of its min and max (junk value elsewhere).
  set d : κ := c 0 1 Nat.zero_lt_one with hd
  set C : Finset ℕ → κ := fun t =>
    if h : t.Nonempty then
      if hlt : t.min' h < t.max' h then c (t.min' h) (t.max' h) hlt else d
    else d with hC
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_seq 2 C
  refine ⟨e, he, k, fun i j hij => ?_⟩
  have hlt : e i < e j := he hij
  set t : Finset ℕ := {e i, e j} with ht
  have hij_ne : e i ∉ ({e j} : Finset ℕ) := by simp [ne_of_lt hlt]
  have htcard : t.card = 2 := by
    rw [ht, Finset.card_insert_of_notMem hij_ne, Finset.card_singleton]
  have htne : t.Nonempty := ⟨e i, by rw [ht]; exact Finset.mem_insert_self _ _⟩
  have htsub : ↑t ⊆ Set.range e := by
    rw [ht]; intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [⟨i, rfl⟩, ⟨j, rfl⟩]
  have hei_mem : e i ∈ t := by rw [ht]; exact Finset.mem_insert_self _ _
  have hej_mem : e j ∈ t := by rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem_iff : ∀ y ∈ t, y = e i ∨ y = e j := by
    intro y hy; rw [ht] at hy
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
  have hmin : t.min' htne = e i := by
    apply le_antisymm (Finset.min'_le _ _ hei_mem)
    apply Finset.le_min'
    intro y hy; rcases hmem_iff y hy with rfl | rfl
    exacts [le_refl _, le_of_lt hlt]
  have hmax : t.max' htne = e j := by
    apply le_antisymm _ (Finset.le_max' _ _ hej_mem)
    apply Finset.max'_le
    intro y hy; rcases hmem_iff y hy with rfl | rfl
    exacts [le_of_lt hlt, le_refl _]
  have hCt : C t = c (e i) (e j) hlt := by
    have h1 : C t = if hlt' : t.min' htne < t.max' htne
        then c (t.min' htne) (t.max' htne) hlt' else d := by
      rw [hC]; simp only [htne, dif_pos]
    rw [h1, hmin, hmax, dif_pos hlt]
  have hkt : C t = k := hk t htsub htcard
  rw [hCt] at hkt
  exact hkt

/-- An intermediate state in the construction of `infinite_ramsey_triples`: a vertex `vert` such
that the colour of every triple `(vert, n, l)` with `n < l` both in the infinite successor set
`succ` above `vert` is constantly `col`. -/
private structure TripleState (κ : Type*) [Fintype κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hcol : ∀ n ∈ succ, ∀ l ∈ succ, ∀ (hn : vert < n) (hl : n < l),
    c vert n l ⟨hn, hl⟩ = col

/-- **The infinite Ramsey theorem for triples (RT³).** Every finite colouring of the triples
`m < n < l` of `ℕ` has an infinite monochromatic set: a strictly monotone `e : ℕ → ℕ` and a
colour `k` such that `c (e h) (e i) (e j) = k` for every `h < i < j`.

Proved by replicating the pairs argument one level up: each step colours the fan from the current
vertex `a'` by applying `infinite_ramsey_pairs` to the induced pair-colouring
`(i, j) ↦ c (a', enumᵢ, enumⱼ)` on an enumeration of the successor set. -/
theorem infinite_ramsey_triples {κ : Type*} [Fintype κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ h i j : ℕ, (hs : h < i ∧ i < j) →
        c (e h) (e i) (e j) ⟨he hs.1, he hs.2⟩ = k := by
  have step :
      ∀ (a : ℕ) (S : Set ℕ), S.Infinite → (∀ x ∈ S, a < x) →
      ∃ a' ∈ S, ∃ col : κ, ∃ S' : Set ℕ,
        S'.Infinite ∧ S' ⊆ S ∧
        (∀ x ∈ S', a' < x) ∧
        (∀ n ∈ S', ∀ l ∈ S', ∀ (hn : a' < n) (hl : n < l),
          c a' n l ⟨hn, hl⟩ = col) := by
    intro a S hS hlt
    set a' := sInf S with ha'_def
    have ha'S : a' ∈ S := Nat.sInf_mem hS.nonempty
    have ha'mn : ∀ x ∈ S, a' ≤ x := fun x hx => Nat.sInf_le hx
    have hTinf : (S \ {a'}).Infinite := hS.diff (Set.finite_singleton a')
    have hTgt : ∀ x ∈ S \ {a'}, a' < x := fun x ⟨hxS, hxne⟩ =>
      Nat.lt_of_le_of_ne (ha'mn x hxS)
        (fun h => hxne (h ▸ Set.mem_singleton_iff.mpr rfl))
    obtain ⟨enum, henum_mono, henum_mem⟩ := hTinf.exists_strictMono
    -- Induce a pair-colouring on indices and apply RT².
    let c_pair : ∀ i j : ℕ, i < j → κ := fun i j hij =>
      c a' (enum i) (enum j) ⟨hTgt _ (henum_mem i), henum_mono hij⟩
    obtain ⟨idx, hidx, col, hcol⟩ := infinite_ramsey_pairs c_pair
    refine ⟨a', ha'S, col, Set.range (enum ∘ idx),
        Set.infinite_range_of_injective (henum_mono.injective.comp hidx.injective),
        ?_, ?_, ?_⟩
    · rintro x ⟨n, rfl⟩; exact (henum_mem (idx n)).1
    · rintro x ⟨n, rfl⟩; exact hTgt _ (henum_mem (idx n))
    · rintro n ⟨i, rfl⟩ l ⟨j, rfl⟩ hn hl
      have hij_idx : idx i < idx j := henum_mono.lt_iff_lt.mp (by exact_mod_cast hl)
      have hij : i < j := hidx.lt_iff_lt.mp hij_idx
      have key : c_pair (idx i) (idx j) hij_idx = col := hcol i j hij
      convert key using 2
  obtain ⟨a₀, _, col₀, S₀, hS₀inf, _, hS₀gt, hS₀col⟩ :=
    step 0 (Set.Ioi 0)
      (Set.infinite_of_injective_forall_mem Nat.succ_injective fun n => Nat.succ_pos n)
      fun x hx => hx
  let s₀ : TripleState κ c := ⟨a₀, col₀, S₀, hS₀inf, hS₀gt, hS₀col⟩
  have advance : ∀ s : TripleState κ c, ∃ s' : TripleState κ c,
      s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
    intro ⟨a, _col, S, hSinf, hSgt, _⟩
    obtain ⟨a', ha'S, col', S', hS'inf, hS'sub, hS'gt, hS'col⟩ := step a S hSinf hSgt
    exact ⟨⟨a', col', S', hS'inf, hS'gt, hS'col⟩, ha'S, hS'sub⟩
  let states : ℕ → TripleState κ c := fun n => n.rec s₀ fun _ s => (advance s).choose
  have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
    fun n => (advance (states n)).choose_spec.1
  have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
    fun n => (advance (states n)).choose_spec.2
  have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
    fun n => (states n).hgt _ (I1 n)
  have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
    intro m n hmn
    induction n with
    | zero => simp [Nat.le_zero.mp hmn]
    | succ n ih =>
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · exact (I2 n).trans (ih (Nat.lt_succ_iff.mp h))
      · exact le_refl _
  have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
    intro m n hmn
    cases n with
    | zero => exact absurd hmn (Nat.not_lt_zero m)
    | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
  have verts_strictMono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
  have I6 : ∀ m n l (hmn : m < n) (hnl : n < l),
      c (states m).vert (states n).vert (states l).vert
        ⟨verts_strictMono hmn, verts_strictMono hnl⟩ = (states m).col := by
    intro m n l hmn hnl
    exact (states m).hcol
      _ (I5 m n hmn) _ (I5 m l (hmn.trans hnl))
      (verts_strictMono hmn) (verts_strictMono hnl)
  obtain ⟨idx, hidx, k, hk⟩ := (fun n => (states n).col).exists_strictMono_eq_of_finite_coloring
  refine ⟨fun n => (states (idx n)).vert, verts_strictMono.comp hidx, k, ?_⟩
  intro h i j ⟨hhi, hij⟩
  have h1 := I6 (idx h) (idx i) (idx j) (hidx hhi) (hidx hij)
  have h2 := hk h
  convert h1.trans h2 using 2

end

/-!
## Verification

These `#guard_msgs` blocks make the build fail if the headline results ever depend on anything
beyond the three standard axioms of classical mathematics (in particular, on `sorryAx`).
-/

/-- info: 'infinite_ramsey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_ramsey

/-- info: 'infinite_ramsey_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_ramsey_pairs

/-- info: 'infinite_ramsey_triples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_ramsey_triples
