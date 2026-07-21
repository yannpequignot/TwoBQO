/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Fronts.Rank

/-!
# The derivative of a front

Given a front `F` on `M` and a node `[a]` of its tree (i.e. `a` is the least element of some
element of `F`), the *derivative* `F after a` is the front obtained by stripping the leading `a`
from the elements of `F` that start with `a`. It is a front on `M after a`, the infinite set
`{n ∈ M : n > a}`, itself represented enumeration-first as the subsequence `M ∘ (· + j)` where
`j` is the least index at which `M` passes `a`.

## Main definitions

* `Front.Mafter M a` : the enumeration `M ∘ (· + afterShift M a)` of `{n ∈ M : n > a}`.
* `Front.Fafter F a` : the derivative `{t | a :: t ∈ F}`.

## Main results

* `Front.Fafter_isFront` : `F after a` is a front on `M after a`.
* `Front.IsFront.singleton_mem_tree` : in a nontrivial front (`[] ∉ F`) every `n ∈ M` heads an
  element, i.e. `[n] ∈ tree F`.
* `Front.IsFront.Fafter_isFront_mem` : for a nontrivial front and `n ∈ M`, `F after n` is a front
  on `M after n`.

## Nontriviality

The trivial front is `{[]}` (rank `0`). For a front, `[] ∉ F`, `F ≠ {[]}`, `⋃ F = M`, and
"`[n] ∈ tree F` for every `n ∈ M`" are all equivalent; `[] ∉ F` is the canonical working flag
(see `IsFront.nil_not_mem_iff`).
-/

open Set List
set_option autoImplicit false
noncomputable section
namespace Front

variable {F : Set (List ℕ)} {M : ℕ → ℕ}

/-- The least index at which `M` passes `a`. -/
def afterShift (M : ℕ → ℕ) (a : ℕ) : ℕ := sInf {j | a < M j}

/-- `M after a`: the increasing enumeration of `{n ∈ M : n > a}`, as the subsequence
`M ∘ (· + afterShift M a)`. -/
def Mafter (M : ℕ → ℕ) (a : ℕ) : ℕ → ℕ := fun i => M (i + afterShift M a)

/-- `F after a`: strip the leading `a` from the elements of `F` that start with `a`. -/
def Fafter (F : Set (List ℕ)) (a : ℕ) : Set (List ℕ) := {t | a :: t ∈ F}

theorem afterShift_spec (hM : StrictMono M) (a : ℕ) : a < M (afterShift M a) := by
  have hne : {j | a < M j}.Nonempty :=
    ⟨a + 1, lt_of_lt_of_le (Nat.lt_succ_self a) (hM.le_apply : a + 1 ≤ M (a + 1))⟩
  exact Nat.sInf_mem hne

theorem lt_of_lt_afterShift {a k : ℕ} (hk : k < afterShift M a) : M k ≤ a := by
  by_contra h
  have hle : afterShift M a ≤ k := Nat.sInf_le (Nat.lt_of_not_le h)
  omega

theorem Mafter_strictMono (hM : StrictMono M) (a : ℕ) : StrictMono (Mafter M a) :=
  fun _ _ hxy => hM (by omega)

theorem Mafter_gt (hM : StrictMono M) (a i : ℕ) : a < Mafter M a i :=
  lt_of_lt_of_le (afterShift_spec hM a) (hM.monotone (by omega))

theorem Mafter_mem_range (a i : ℕ) : Mafter M a i ∈ Set.range M := ⟨i + afterShift M a, rfl⟩

theorem mem_range_Mafter_iff (hM : StrictMono M) (a n : ℕ) :
    n ∈ Set.range (Mafter M a) ↔ n ∈ Set.range M ∧ a < n := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Mafter_mem_range a i, Mafter_gt hM a i⟩
  · rintro ⟨⟨k, rfl⟩, hlt⟩
    have hk : afterShift M a ≤ k := Nat.sInf_le hlt
    exact ⟨k - afterShift M a, by rw [Mafter]; congr 1; omega⟩

/-- Density transported: any strictly monotone subsequence of `M` has an initial segment in `F`. -/
theorem exists_frontElem_isInit (hF : IsFront F M) {N : ℕ → ℕ} (hN : StrictMono N)
    (hsub : Set.range N ⊆ Set.range M) : ∃ u ∈ F, IsInit u N := by
  obtain ⟨h, hh, hcomp⟩ := exists_strictMono_comp hF.mono hN fun i => hsub ⟨i, rfl⟩
  obtain ⟨u, hu, hInit⟩ := hF.dense h hh
  rw [hcomp] at hInit
  exact ⟨u, hu, hInit⟩

theorem nil_not_mem (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F) : [] ∉ F := by
  intro hnil
  obtain ⟨w, hw, hpre⟩ := ha
  have := hF.incomp [] hnil w hw List.nil_prefix
  rw [← this] at hpre
  simpa using hpre.length_le

/-- A front is *nontrivial* (`[] ∉ F`) iff it is not the trivial front `{[]}`. -/
theorem IsFront.nil_not_mem_iff (hF : IsFront F M) : [] ∉ F ↔ F ≠ {[]} := by
  constructor
  · intro h heq; exact h (by simp [heq])
  · intro hne hnil
    apply hne
    ext t
    simp only [Set.mem_singleton_iff]
    exact ⟨fun ht => (hF.incomp [] hnil t ht List.nil_prefix).symm, fun h => h ▸ hnil⟩

/-- **In a nontrivial front, every element of `M` heads some element of `F`.** For `[] ∉ F` and
`n ∈ M`, the singleton `[n]` is a node of the tree of `F`. -/
theorem IsFront.singleton_mem_tree (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : [n] ∈ tree F := by
  obtain ⟨k, rfl⟩ := hn
  set N : ℕ → ℕ := fun i => M (i + k) with hN
  have hNmono : StrictMono N := fun x y h => hF.mono (by omega)
  have hNsub : Set.range N ⊆ Set.range M := by rintro _ ⟨i, rfl⟩; exact ⟨i + k, rfl⟩
  obtain ⟨u, hu, hInit⟩ := exists_frontElem_isInit hF hNmono hNsub
  have hune : u ≠ [] := fun h => h0 (h ▸ hu)
  have hlen : 0 < u.length := List.length_pos_iff.mpr hune
  have hhead : u.headI = M k := by rw [hInit.headI hlen]; simp [hN]
  have hpre : [u.headI] <+: u := by
    cases u with
    | nil => exact absurd rfl hune
    | cons c t => exact ⟨t, rfl⟩
  rw [hhead] at hpre
  exact ⟨u, hu, hpre⟩

/-- The head-stripping construction: if `[a]` is in the tree and `Q` is a strictly monotone
subsequence of `M` with `a < Q 0`, then some `a :: t ∈ F` with `t` an initial segment of `Q`. -/
theorem exists_cons_mem (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F)
    {Q : ℕ → ℕ} (hQ : StrictMono Q) (haQ : a < Q 0) (hQM : ∀ i, Q i ∈ Set.range M) :
    ∃ t, a :: t ∈ F ∧ IsInit t Q := by
  have haM : a ∈ Set.range M := by
    obtain ⟨w, hw, hpre⟩ := ha
    exact hF.subM w hw a (hpre.subset (List.mem_singleton_self a))
  set N : ℕ → ℕ := fun i => if i = 0 then a else Q (i - 1) with hN
  have hN0 : N 0 = a := by simp [hN]
  have hNsucc : ∀ k, N (k + 1) = Q k := by intro k; simp [hN]
  have hNmono : StrictMono N := by
    apply strictMono_nat_of_lt_succ
    intro i
    cases i with
    | zero => rw [hN0, hNsucc]; exact haQ
    | succ k => rw [hNsucc, hNsucc]; exact hQ (Nat.lt_succ_self k)
  have hNsub : Set.range N ⊆ Set.range M := by
    rintro _ ⟨i, rfl⟩
    cases i with
    | zero => rw [hN0]; exact haM
    | succ k => rw [hNsucc]; exact hQM k
  obtain ⟨u, hu, hInit⟩ := exists_frontElem_isInit hF hNmono hNsub
  have hune : u ≠ [] := fun h => nil_not_mem hF ha (h ▸ hu)
  obtain ⟨m, hm⟩ : ∃ m, u.length = m + 1 := ⟨u.length - 1, by
    have : 0 < u.length := List.length_pos_iff.mpr hune; omega⟩
  have hu_eq : u = a :: (List.range m).map Q := by
    rw [hInit, hm, List.range_succ_eq_map, List.map_cons, hN0]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    exact hNsucc k
  refine ⟨(List.range m).map Q, ?_, isInit_take Q m⟩
  rw [← hu_eq]; exact hu

/-- **`F after a` is a front on `M after a`**, whenever `[a]` is a node of the tree of `F`
(i.e. `a` is the least element of some element of `F`). -/
theorem Fafter_isFront (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F) :
    IsFront (Fafter F a) (Mafter M a) where
  mono := Mafter_strictMono hF.mono a
  sorted t ht := (hF.sorted (a :: t) ht).of_cons
  subM t ht x hx := by
    have hxM : x ∈ Set.range M := hF.subM (a :: t) ht x (List.mem_cons_of_mem a hx)
    have hax : a < x := (List.pairwise_cons.mp (hF.sorted (a :: t) ht)).1 x hx
    exact (mem_range_Mafter_iff hF.mono a x).mpr ⟨hxM, hax⟩
  incomp s hs t ht hst := by
    have heq : a :: s = a :: t :=
      hF.incomp (a :: s) hs (a :: t) ht ((List.prefix_cons_inj a).mpr hst)
    injection heq with _ h
  dense g hg := by
    have hQmono : StrictMono (Mafter M a ∘ g) := (Mafter_strictMono hF.mono a).comp hg
    obtain ⟨t, htF, htInit⟩ := exists_cons_mem hF ha hQmono
      (by exact Mafter_gt hF.mono a (g 0)) (fun i => Mafter_mem_range a (g i))
    exact ⟨t, htF, htInit⟩
  base := by
    by_cases haF : [a] ∈ F
    · left
      ext t
      simp only [Fafter, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro ht
        have heq := hF.incomp [a] haF (a :: t) ht ((List.prefix_cons_inj a).mpr List.nil_prefix)
        injection heq with _ h; exact h.symm
      · rintro rfl; exact haF
    · right
      ext n
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨t, ht, hnt⟩
        have hxM : n ∈ Set.range M := hF.subM (a :: t) ht n (List.mem_cons_of_mem a hnt)
        have hax : a < n := (List.pairwise_cons.mp (hF.sorted (a :: t) ht)).1 n hnt
        exact (mem_range_Mafter_iff hF.mono a n).mpr ⟨hxM, hax⟩
      · intro hn
        obtain ⟨hnM, hax⟩ := (mem_range_Mafter_iff hF.mono a n).mp hn
        obtain ⟨k, rfl⟩ := hnM
        have hQmono : StrictMono (fun i => M (i + k)) := fun x y hxy => hF.mono (by omega)
        obtain ⟨t, htF, htInit⟩ := exists_cons_mem hF ha hQmono (by simpa using hax)
          (fun i => ⟨i + k, rfl⟩)
        have htne : t ≠ [] := by rintro rfl; exact haF htF
        have hlen : 0 < t.length := List.length_pos_iff.mpr htne
        have hhead : t.headI = M k := by
          rw [htInit.headI hlen]; simp
        refine ⟨t, htF, ?_⟩
        rw [← hhead, headI_eq_getElem hlen]
        exact List.getElem_mem hlen

/-- For a nontrivial front and `n ∈ M`, `F after n` is a front on `M after n`. -/
theorem IsFront.Fafter_isFront_mem (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : IsFront (Fafter F n) (Mafter M n) :=
  Fafter_isFront hF (hF.singleton_mem_tree h0 hn)

end Front
