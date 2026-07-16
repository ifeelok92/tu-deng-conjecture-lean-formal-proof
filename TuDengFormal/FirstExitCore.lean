import Mathlib

set_option linter.style.header false

/-!
# First-exit language: kernel-checked combinatorial core

This module formalizes the deletion argument used in
`Tu_Deng_Conjecture_Proof_Revised_ZH.tex`:

* the lexicographic boundary language;
* closure under deleting a marked `1`;
* the marked-deletion injection and its coefficient inequality.

-/

namespace TuDeng.FirstExit

open scoped BigOperators

abbrev Word := List Bool

/-- Number of zeroes in a binary word. -/
def zeros (w : Word) : ℕ := w.count false

/-- Number of ones in a binary word. -/
def ones (w : Word) : ℕ := w.count true

theorem zeros_add_ones (w : Word) : zeros w + ones w = w.length := by
  exact List.count_false_add_count_true w

/-! ## The finite-word lexicographic order used by the paper -/

/-- Lexicographic order with `false < true`, and a strict prefix smaller. -/
def LexLT : Word → Word → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs =>
      if a = b then LexLT as bs else a = false ∧ b = true

@[simp] theorem lex_nil_nil : ¬ LexLT [] [] := by simp [LexLT]
@[simp] theorem lex_nil_cons (b : Bool) (v : Word) : LexLT [] (b :: v) := by simp [LexLT]
@[simp] theorem not_lex_cons_nil (b : Bool) (v : Word) : ¬ LexLT (b :: v) [] := by simp [LexLT]

@[simp] theorem lex_cons_same (b : Bool) (u v : Word) :
    LexLT (b :: u) (b :: v) ↔ LexLT u v := by simp [LexLT]

@[simp] theorem lex_false_true (u v : Word) : LexLT (false :: u) (true :: v) := by
  simp [LexLT]

@[simp] theorem not_lex_true_false (u v : Word) : ¬ LexLT (true :: u) (false :: v) := by
  simp [LexLT]

theorem lex_trans : ∀ {u v w : Word}, LexLT u v → LexLT v w → LexLT u w := by
  intro u v w huv hvw
  induction u generalizing v w with
  | nil => cases v <;> cases w <;> simp_all [LexLT]
  | cons a u ih =>
      cases v with
      | nil => simp_all [LexLT]
      | cons b v =>
          cases w with
          | nil => simp_all [LexLT]
          | cons c w =>
              by_cases hab : a = b
              · subst b
                by_cases hbc : a = c
                · subst c
                  simp only [lex_cons_same] at huv hvw ⊢
                  exact ih huv hvw
                · have hac : a ≠ c := hbc
                  simp only [LexLT, if_pos rfl] at huv
                  simp only [LexLT, if_neg hac] at hvw ⊢
                  exact hvw
              · have hab' : a ≠ b := hab
                simp only [LexLT, if_neg hab'] at huv
                rcases huv with ⟨rfl, rfl⟩
                cases c <;> simp_all [LexLT]

theorem lex_prefix (a u v : Word) (h : LexLT u v) :
    LexLT (a ++ u) (a ++ v) := by
  induction a with
  | nil => simpa
  | cons b a ih => simpa using ih

theorem lex_lt_true_cons : ∀ s : Word, LexLT s (true :: s)
  | [] => by simp
  | false :: s => by simp
  | true :: s => by simpa using lex_lt_true_cons s

/-- Removing one occurrence of `1` strictly lowers a word lexicographically. -/
theorem lex_delete_true (w : Word) (i : ℕ) (hi : i < w.length)
    (hbit : w[i] = true) : LexLT (w.eraseIdx i) w := by
  have htail : LexLT (w.drop (i + 1)) (true :: w.drop (i + 1)) :=
    lex_lt_true_cons _
  have hdrop : w.drop i = true :: w.drop (i + 1) := by
    simpa [hbit] using (List.drop_eq_getElem_cons hi)
  have hw : w.take i ++ (true :: w.drop (i + 1)) = w := by
    rw [← hdrop, List.take_append_drop]
  rw [List.eraseIdx_eq_take_drop_succ]
  simpa only [hw] using lex_prefix (w.take i) _ _ htail

/-! ## Principal subsequence ideal and lexicographic boundary language -/

/-- The directed `1`-boundary of the principal subsequence ideal of `v`. -/
def BoundaryOne (v y : Word) : Prop :=
  ∃ u, u.Sublist v ∧ ¬ y.Sublist v ∧ y = u ++ [true]

/-- `Sub(v)` together with the part of its `1`-boundary below `v` in lexicographic order. -/
def Lang (v y : Word) : Prop :=
  y.Sublist v ∨ (BoundaryOne v y ∧ LexLT y v)

theorem lang_of_sublist {v y : Word} (h : y.Sublist v) : Lang v y := Or.inl h

theorem boundaryOne_append {v u : Word} (hu : u.Sublist v)
    (hnot : ¬ (u ++ [true]).Sublist v) : BoundaryOne v (u ++ [true]) := by
  exact ⟨u, hu, hnot, rfl⟩

/-- The paper's one-sided closure: deleting any marked `1` stays in `Lang v`. -/
theorem lang_eraseIdx_true {v y : Word} (hy : Lang v y) (i : ℕ)
    (hi : i < y.length) (hbit : y[i] = true) : Lang v (y.eraseIdx i) := by
  rcases hy with hsub | ⟨⟨u, hu, hnot, rfl⟩, hlex⟩
  · exact Or.inl ((List.eraseIdx_sublist y i).trans hsub)
  · have hi' : i < u.length + 1 := by simpa using hi
    have hile : i ≤ u.length := Nat.lt_succ_iff.mp hi'
    rcases hile.lt_or_eq with hil | rfl
    · have herase : (u ++ [true]).eraseIdx i = u.eraseIdx i ++ [true] :=
        List.eraseIdx_append_of_lt_length hil [true]
      rw [herase]
      by_cases hz : (u.eraseIdx i ++ [true]).Sublist v
      · exact Or.inl hz
      · exact Or.inr ⟨boundaryOne_append ((List.eraseIdx_sublist u i).trans hu) hz,
          lex_trans (by
            rw [← herase]
            exact lex_delete_true (u ++ [true]) i hi hbit) hlex⟩
    · have herase : (u ++ [true]).eraseIdx u.length = u := by
        simp [List.eraseIdx_append_of_length_le]
      rw [herase]
      exact Or.inl hu

/-- The finite set of all subsequences of `v`. -/
def subwordFinset (v : Word) : Finset Word := v.sublists.toFinset

/-- Executable directed `1`-boundary. -/
def boundaryOneFinset (v : Word) : Finset Word :=
  ((subwordFinset v).image fun u => u ++ [true]).filter fun y => ¬ y.Sublist v

/-- Finite realization of `Lang v`. -/
noncomputable def langFinset (v : Word) : Finset Word := by
  classical
  exact subwordFinset v ∪ (boundaryOneFinset v).filter fun y => LexLT y v

theorem mem_subwordFinset {v y : Word} : y ∈ subwordFinset v ↔ y.Sublist v := by
  simp [subwordFinset, List.mem_sublists]

theorem mem_boundaryOneFinset {v y : Word} :
    y ∈ boundaryOneFinset v ↔ BoundaryOne v y := by
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hy, hnot⟩
    rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
    exact ⟨u, mem_subwordFinset.mp hu, hnot, rfl⟩
  · rintro ⟨u, hu, hnot, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨u, mem_subwordFinset.mpr hu, rfl⟩, hnot⟩

theorem mem_langFinset {v y : Word} : y ∈ langFinset v ↔ Lang v y := by
  classical
  simp only [langFinset, Finset.mem_union, Finset.mem_filter, mem_subwordFinset,
    mem_boundaryOneFinset, Lang]

theorem langFinset_delete_closed (v : Word) :
    ∀ y ∈ langFinset v, ∀ i, (hi : i < y.length) → y[i] = true →
      y.eraseIdx i ∈ langFinset v := by
  intro y hy i hi hbit
  exact mem_langFinset.mpr (lang_eraseIdx_true (mem_langFinset.mp hy) i hi hbit)

/-- The lexicographic boundary cannot contain more `1`s than its generating word. -/
theorem boundaryOne_ones_le {v y : Word} (hy : BoundaryOne v y)
    (hlex : LexLT y v) : ones y ≤ ones v := by
  rcases hy with ⟨u, hu, hnot, rfl⟩
  induction v generalizing u with
  | nil =>
      have : u = [] := List.sublist_nil.mp hu
      subst u
      simp at hlex
  | cons b v ih =>
      cases u with
      | nil =>
          cases b
          · simp [LexLT] at hlex
          · simp [ones]
      | cons a u =>
          cases a <;> cases b
          · have hu' : u.Sublist v := List.cons_sublist_cons.mp hu
            have hnot' : ¬ (u ++ [true]).Sublist v := by
              simpa using hnot
            have hlex' : LexLT (u ++ [true]) v := by simpa using hlex
            simpa [ones] using ih u hu' hlex' hnot'
          · have husub : (false :: u).Sublist v := by
              rcases List.sublist_cons_iff.mp hu with huv | ⟨r, hbad, _⟩
              · exact huv
              · simp at hbad
            have hcount := husub.count_le true
            simp [ones] at hcount ⊢
            omega
          · simp [LexLT] at hlex
          · have hu' : u.Sublist v := List.cons_sublist_cons.mp hu
            have hnot' : ¬ (u ++ [true]).Sublist v := by
              simpa using hnot
            have hlex' : LexLT (u ++ [true]) v := by simpa using hlex
            have hrec := ih u hu' hlex' hnot'
            simpa [ones] using Nat.add_le_add_right hrec 1

theorem lang_ones_le {v y : Word} (hy : Lang v y) : ones y ≤ ones v := by
  rcases hy with hsub | ⟨hboundary, hlex⟩
  · exact hsub.count_le true
  · exact boundaryOne_ones_le hboundary hlex

theorem langFinset_ones_le {v y : Word} (hy : y ∈ langFinset v) :
    ones y ≤ ones v := lang_ones_le (mem_langFinset.mp hy)

/-- Any feasible pair of zero/one counts is realized by a subsequence. -/
theorem exists_sublist_with_counts (v : Word) (a b : ℕ)
    (ha : a ≤ zeros v) (hb : b ≤ ones v) :
    ∃ u, u.Sublist v ∧ zeros u = a ∧ ones u = b := by
  induction v generalizing a b with
  | nil =>
      have ha0 : a = 0 := by simpa [zeros] using ha
      have hb0 : b = 0 := by simpa [ones] using hb
      subst a
      subst b
      exact ⟨[], List.nil_sublist [], by simp [zeros, ones]⟩
  | cons x v ih =>
      cases x
      · cases a with
        | zero =>
            obtain ⟨u, hu, hzu, hou⟩ := ih 0 b (by simp [zeros]) (by simpa [ones] using hb)
            exact ⟨u, hu.cons false, hzu, hou⟩
        | succ a =>
            have ha' : a ≤ zeros v := by simpa [zeros] using ha
            obtain ⟨u, hu, hzu, hou⟩ := ih a b ha' (by simpa [ones] using hb)
            exact ⟨false :: u, hu.cons₂ false, by simpa [zeros, ones] using hzu,
              by simpa [zeros, ones] using hou⟩
      · cases b with
        | zero =>
            obtain ⟨u, hu, hzu, hou⟩ := ih a 0 (by simpa [zeros] using ha) (by simp [ones])
            exact ⟨u, hu.cons true, hzu, hou⟩
        | succ b =>
            have hb' : b ≤ ones v := by simpa [ones] using hb
            obtain ⟨u, hu, hzu, hou⟩ := ih a b (by simpa [zeros] using ha) hb'
            exact ⟨true :: u, hu.cons₂ true, by simpa [zeros, ones] using hzu,
              by simpa [zeros, ones] using hou⟩

/-! ## Finite coefficient layers and marked deletion -/

/-- Words in `L` having exactly `a` zeroes and `b` ones. -/
def layer (L : Finset Word) (a b : ℕ) : Finset Word :=
  L.filter fun w => zeros w = a ∧ ones w = b

/-- Raw positions occupied by `1`. -/
def truePositions (w : Word) : Finset ℕ :=
  (Finset.range w.length).filter fun i => w[i]? = some true

theorem card_truePositions (w : Word) : (truePositions w).card = ones w := by
  simp only [truePositions, Finset.card_filter]
  induction w with
  | nil => simp [ones]
  | cons b w ih =>
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simp [ones, List.count_cons]
      exact ih

/-- A word in one coefficient layer together with a marked occurrence of `1`. -/
def markedOnes (L : Finset Word) (a b : ℕ) : Finset (Σ _ : Word, ℕ) :=
  (layer L a b).sigma fun w => truePositions w

/-- A word in the lower layer together with an arbitrary insertion slot. -/
def insertionSlots (L : Finset Word) (a b : ℕ) : Finset (Σ _ : Word, ℕ) :=
  (layer L a b).sigma fun w => Finset.range (w.length + 1)

theorem count_eraseIdx_true {w : Word} {i : ℕ} (hi : i < w.length)
    (hbit : w[i] = true) :
    zeros (w.eraseIdx i) = zeros w ∧ ones (w.eraseIdx i) = ones w - 1 := by
  have hp := List.getElem_cons_eraseIdx_perm hi
  have hzero := hp.count_eq false
  have hone := hp.count_eq true
  simp [hbit] at hzero hone
  constructor
  · simpa [zeros] using hzero
  · dsimp [ones]
    omega

theorem card_markedOnes (L : Finset Word) (a b : ℕ) :
    (markedOnes L a b).card = b * (layer L a b).card := by
  rw [markedOnes, Finset.card_sigma]
  simp_rw [card_truePositions]
  have h : ∀ w ∈ layer L a b, ones w = b := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2.2
  calc
    ∑ w ∈ layer L a b, ones w = ∑ _w ∈ layer L a b, b := by
      apply Finset.sum_congr rfl
      intro w hw
      exact h w hw
    _ = b * (layer L a b).card := by simp [Nat.mul_comm]

theorem card_insertionSlots (L : Finset Word) (a b : ℕ) :
    (insertionSlots L a b).card = (a + b + 1) * (layer L a b).card := by
  rw [insertionSlots, Finset.card_sigma]
  have hlen : ∀ w ∈ layer L a b, w.length + 1 = a + b + 1 := by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    rw [← zeros_add_ones w, hw'.1, hw'.2]
  simp_rw [Finset.card_range]
  calc
    ∑ w ∈ layer L a b, (w.length + 1) =
        ∑ _w ∈ layer L a b, (a + b + 1) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hlen w hw
    _ = (a + b + 1) * (layer L a b).card := by simp [Nat.mul_comm]

/-- Erase the marked `1`, remembering its old position as an insertion slot. -/
def markedDelete (p : Σ _ : Word, ℕ) : Σ _ : Word, ℕ :=
  ⟨p.1.eraseIdx p.2, p.2⟩

theorem markedDelete_injective_on (L : Finset Word) (a b : ℕ) :
    Set.InjOn markedDelete (markedOnes L a b : Set (Σ _ : Word, ℕ)) := by
  intro p hp q hq heq
  have hp' := Finset.mem_sigma.mp hp
  have hq' := Finset.mem_sigma.mp hq
  have hipos := Finset.mem_range.mp (Finset.mem_filter.mp hp'.2).1
  have hqpos := Finset.mem_range.mp (Finset.mem_filter.mp hq'.2).1
  have hpbit? := (Finset.mem_filter.mp hp'.2).2
  have hqbit? := (Finset.mem_filter.mp hq'.2).2
  have hpbit : p.1[p.2] = true := by
    exact (List.getElem?_eq_some_iff.mp hpbit?).choose_spec
  have hqbit : q.1[q.2] = true := by
    exact (List.getElem?_eq_some_iff.mp hqbit?).choose_spec
  have hi : p.2 = q.2 := congrArg Sigma.snd heq
  have hl : p.1.eraseIdx p.2 = q.1.eraseIdx q.2 := congrArg Sigma.fst heq
  have hlist : p.1 = q.1 := calc
    p.1 = (p.1.eraseIdx p.2).insertIdx p.2 true := by
      symm
      simpa [hpbit] using List.insertIdx_eraseIdx_getElem hipos
    _ = (q.1.eraseIdx q.2).insertIdx q.2 true := by rw [hl, hi]
    _ = q.1 := by simpa [hqbit] using List.insertIdx_eraseIdx_getElem hqpos
  exact Sigma.ext hlist (heq_of_eq hi)

/--
The marked-deletion coefficient inequality.  This is Corollary 6.4 of the paper:
`b * j(a,b) ≤ (a+b) * j(a,b-1)`.
-/
theorem marked_deletion_inequality
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (a b : ℕ) (hb : 1 ≤ b) :
    b * (layer L a b).card ≤ (a + b) * (layer L a (b - 1)).card := by
  have hmap : Set.MapsTo markedDelete
      (markedOnes L a b : Set (Σ _ : Word, ℕ))
      (insertionSlots L a (b - 1) : Set (Σ _ : Word, ℕ)) := by
    intro p hp
    have hp' := Finset.mem_sigma.mp hp
    have hwlayer := hp'.1
    have hpos := Finset.mem_filter.mp hp'.2
    have hi : p.2 < p.1.length := Finset.mem_range.mp hpos.1
    have hbit : p.1[p.2] = true := by
      exact (List.getElem?_eq_some_iff.mp hpos.2).choose_spec
    have hw := (Finset.mem_filter.mp hwlayer).1
    have hcounts := (Finset.mem_filter.mp hwlayer).2
    have herase := count_eraseIdx_true hi hbit
    have hmem : (⟨p.1.eraseIdx p.2, p.2⟩ : Σ _ : Word, ℕ) ∈
        insertionSlots L a (b - 1) := by
      rw [insertionSlots, Finset.mem_sigma]
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨hclosed p.1 hw p.2 hi hbit,
          by simpa [hcounts.1, hcounts.2] using herase⟩
      · apply Finset.mem_range.mpr
        change p.2 < (p.1.eraseIdx p.2).length + 1
        rw [List.length_eraseIdx_of_lt hi]
        omega
    exact hmem
  have hcard := Finset.card_le_card_of_injOn markedDelete hmap
    (markedDelete_injective_on L a b)
  rw [card_markedOnes, card_insertionSlots] at hcard
  have harith : a + (b - 1) + 1 = a + b := by omega
  simpa [harith] using hcard

theorem diagonal_subdiagonal
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (m : ℕ) (hm : 1 ≤ m) :
    (layer L m m).card ≤ 2 * (layer L m (m - 1)).card := by
  have h := marked_deletion_inequality L hclosed m m hm
  have hmpos : 0 < m := hm
  apply Nat.le_of_mul_le_mul_left (c := m)
  · calc
      m * (layer L m m).card ≤ (m + m) * (layer L m (m - 1)).card := h
      _ = m * (2 * (layer L m (m - 1)).card) := by ring
  · exact hmpos

/-! ## The half-plane defect after the marked-deletion comparison -/

/-- Coefficient `j_(a,b)` of the enumerator of `L`. -/
def jCoeff (L : Finset Word) (a b : ℕ) : ℕ := (layer L a b).card

theorem lex_language_subdiagonal_nonempty (v : Word) (h : ones v < zeros v) :
    1 ≤ jCoeff (langFinset v) (ones v + 1) (ones v) := by
  obtain ⟨u, hu, hzu, hou⟩ := exists_sublist_with_counts v (ones v + 1) (ones v)
    (by omega) (le_refl _)
  rw [jCoeff, Finset.one_le_card]
  exact ⟨u, Finset.mem_filter.mpr ⟨mem_langFinset.mpr (Or.inl hu), hzu, hou⟩⟩

theorem lex_language_high_diagonal_zero (v : Word) :
    jCoeff (langFinset v) (ones v + 1) (ones v + 1) = 0 := by
  rw [jCoeff, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨y, hy⟩
  have hy' := Finset.mem_filter.mp hy
  have hle := langFinset_ones_le hy'.1
  omega

/-- The surviving diagonal/subdiagonal contribution at level `m ≥ 1`. -/
def defectTerm (L : Finset Word) (m : ℕ) : ℚ :=
  (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) -
    (jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m)

/-- Truncation of `Phi_-((X+Y-1)J)` at diagonal level `M`. -/
def halfplaneDefect (L : Finset Word) (M : ℕ) : ℚ :=
  1 / 2 + ∑ m ∈ Finset.Icc 1 M, defectTerm L m

theorem defectTerm_nonpos
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (m : ℕ) (hm : 1 ≤ m) : defectTerm L m ≤ 0 := by
  have hnat := diagonal_subdiagonal L hclosed m hm
  have hq : (jCoeff L m m : ℚ) ≤ 2 * (jCoeff L m (m - 1) : ℚ) := by
    exact_mod_cast hnat
  have hpow : (0 : ℚ) < (2 : ℚ) ^ (2 * m + 1) := by positivity
  have hdiv : (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) ≤
      (2 * (jCoeff L m (m - 1) : ℚ)) / (2 : ℚ) ^ (2 * m + 1) :=
    div_le_div_of_nonneg_right hq hpow.le
  have hid : (2 * (jCoeff L m (m - 1) : ℚ)) / (2 : ℚ) ^ (2 * m + 1) =
      (jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m) := by
    rw [show 2 * m + 1 = (2 * m) + 1 by omega, pow_succ]
    field_simp
    <;> ring
  dsimp [defectTerm]
  linarith

theorem halfplaneDefect_le_half
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (M : ℕ) : halfplaneDefect L M ≤ 1 / 2 := by
  have hsum : (∑ m ∈ Finset.Icc 1 M, defectTerm L m) ≤ 0 := by
    apply Finset.sum_nonpos
    intro m hm
    exact defectTerm_nonpos L hclosed m (Finset.mem_Icc.mp hm).1
  dsimp [halfplaneDefect]
  linarith

theorem defectTerm_le_negative_unit
    (L : Finset Word) (m : ℕ)
    (hdiag : jCoeff L m m = 0)
    (hsub : 1 ≤ jCoeff L m (m - 1)) :
    defectTerm L m ≤ -(1 / (2 : ℚ) ^ (2 * m)) := by
  have hq : (1 : ℚ) ≤ (jCoeff L m (m - 1) : ℚ) := by exact_mod_cast hsub
  have hp : (0 : ℚ) < (2 : ℚ) ^ (2 * m) := by positivity
  have hdiv : (1 : ℚ) / (2 : ℚ) ^ (2 * m) ≤
      (jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m) :=
    div_le_div_of_nonneg_right hq hp.le
  simp only [defectTerm, hdiag, Nat.cast_zero, zero_div, zero_sub]
  linarith

theorem halfplaneDefect_strict_room
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (M m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hM : m₀ ≤ M)
    (hdiag : jCoeff L m₀ m₀ = 0)
    (hsub : 1 ≤ jCoeff L m₀ (m₀ - 1)) :
    halfplaneDefect L M ≤ 1 / 2 - 1 / (2 : ℚ) ^ (2 * m₀) := by
  let S := Finset.Icc 1 M
  let gap : ℚ := 1 / (2 : ℚ) ^ (2 * m₀)
  have hm₀S : m₀ ∈ S := by simp [S, hm₀, hM]
  have hpoint : ∀ m ∈ S, defectTerm L m ≤ if m = m₀ then -gap else 0 := by
    intro m hm
    by_cases heq : m = m₀
    · subst m
      simpa [gap] using defectTerm_le_negative_unit L m₀ hdiag hsub
    · simp only [heq, if_false]
      exact defectTerm_nonpos L hclosed m (Finset.mem_Icc.mp hm).1
  have hsum : (∑ m ∈ S, defectTerm L m) ≤ ∑ m ∈ S, if m = m₀ then -gap else 0 := by
    exact Finset.sum_le_sum fun m hm => hpoint m hm
  have hrhs : (∑ m ∈ S, if m = m₀ then -gap else 0) = -gap := by
    rw [Finset.sum_eq_single m₀]
    · simp
    · intro b hb hbne
      simp [hbne]
    · exact fun hnot => (hnot hm₀S).elim
  rw [hrhs] at hsum
  dsimp [halfplaneDefect]
  change 1 / 2 + (∑ m ∈ S, defectTerm L m) ≤ _
  dsimp [gap] at hsum ⊢
  linarith

/-- The exceptional monomial contributes only when `zeros v > ones v`. -/
def exceptionMass (v : Word) : ℚ :=
  if ones v < zeros v then 1 / (2 : ℚ) ^ (zeros v + ones v + 2) else 0

theorem lex_language_halfplane_with_exception (v : Word) (M : ℕ)
    (hM : ones v + 1 ≤ M) :
    halfplaneDefect (langFinset v) M + exceptionMass v ≤ 1 / 2 := by
  by_cases hzo : ones v < zeros v
  · have hroom := halfplaneDefect_strict_room (langFinset v)
      (langFinset_delete_closed v) M (ones v + 1) (by omega) hM
      (lex_language_high_diagonal_zero v)
      (by simpa using lex_language_subdiagonal_nonempty v hzo)
    have hexp : 2 * ones v + 3 ≤ zeros v + ones v + 2 := by omega
    have hpow : (2 : ℚ) ^ (2 * ones v + 3) ≤
        (2 : ℚ) ^ (zeros v + ones v + 2) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hrecip : 1 / (2 : ℚ) ^ (zeros v + ones v + 2) ≤
        1 / (2 : ℚ) ^ (2 * ones v + 3) :=
      one_div_le_one_div_of_le (by positivity) hpow
    have hhalf : 1 / (2 : ℚ) ^ (2 * ones v + 3) =
        (1 / 2) * (1 / (2 : ℚ) ^ (2 * (ones v + 1))) := by
      rw [show 2 * ones v + 3 = 2 * (ones v + 1) + 1 by omega, pow_succ]
      field_simp
      <;> ring
    rw [exceptionMass, if_pos hzo]
    rw [hhalf] at hrecip
    have hgap : (0 : ℚ) < 1 / (2 : ℚ) ^ (2 * (ones v + 1)) := by positivity
    linarith
  · rw [exceptionMass, if_neg hzo, add_zero]
    exact halfplaneDefect_le_half (langFinset v) (langFinset_delete_closed v) M

theorem lex_language_halfplane_bound (v : Word) (M : ℕ) :
    halfplaneDefect (langFinset v) M ≤ 1 / 2 := by
  exact halfplaneDefect_le_half (langFinset v) (langFinset_delete_closed v) M

end TuDeng.FirstExit
