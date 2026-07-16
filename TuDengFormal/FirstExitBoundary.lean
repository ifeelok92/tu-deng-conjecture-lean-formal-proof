import TuDengFormal.FirstExitCore

set_option linter.style.header false

/-!
# Directed boundaries of principal subsequence ideals

This module proves the four set-level recurrences used by the first-exit
argument.  They are independent of the polynomial and arithmetic layers.
-/

namespace TuDeng.FirstExit

/-- Directed boundary in the direction `b`. -/
def Boundary (v : Word) (b : Bool) (y : Word) : Prop :=
  ∃ u, u.Sublist v ∧ ¬ y.Sublist v ∧ y = u ++ [b]

theorem boundary_true_iff {v y : Word} : Boundary v true y ↔ BoundaryOne v y := by
  rfl

/-- Subsequence decomposition after adjoining one final symbol. -/
theorem sublist_concat_iff (y v : Word) (b : Bool) :
    y.Sublist (v ++ [b]) ↔ y.Sublist v ∨ ∃ u, u.Sublist v ∧ y = u ++ [b] := by
  rw [List.sublist_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, h₁, h₂⟩
    have h₂' : l₂ = [] ∨ l₂ = [b] := by simpa using h₂
    rcases h₂' with rfl | rfl
    · exact Or.inl (by simpa using h₁)
    · exact Or.inr ⟨l₁, h₁, rfl⟩
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact ⟨y, [], by simp, h, List.nil_sublist [b]⟩
    · exact ⟨u, [b], rfl, hu, by simp⟩

theorem append_singleton_injective (b : Bool) :
    Function.Injective (fun y : Word => y ++ [b]) := by
  intro x y h
  exact List.append_cancel_right h

theorem singleton_suffix_eq {u v : Word} {a b : Bool}
    (h : u ++ [a] = v ++ [b]) : a = b := by
  have hlen : u.length = v.length := by
    have := congrArg List.length h
    simp at this
    omega
  have hs := (List.append_inj h hlen).2
  simpa using hs

/-- Same-direction boundary recurrence, e.g. `∂₀D(v0) = (∂₀D(v))0`. -/
theorem boundary_concat_same {v y : Word} {b : Bool} :
    Boundary (v ++ [b]) b y ↔
      ∃ x, Boundary v b x ∧ y = x ++ [b] := by
  constructor
  · rintro ⟨u, hu, hnot, rfl⟩
    rcases (sublist_concat_iff u v b).mp hu with huold | ⟨p, hp, rfl⟩
    · exact (hnot ((sublist_concat_iff (u ++ [b]) v b).mpr
        (Or.inr ⟨u, huold, rfl⟩))).elim
    · have hpb : ¬ (p ++ [b]).Sublist v := by
        intro hpb
        exact hnot ((sublist_concat_iff (p ++ [b] ++ [b]) v b).mpr
          (Or.inr ⟨p ++ [b], hpb, rfl⟩))
      exact ⟨p ++ [b], ⟨p, hp, hpb, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨p, hp, hxnot, rfl⟩, rfl⟩
    refine ⟨p ++ [b], (sublist_concat_iff (p ++ [b]) v b).mpr
      (Or.inr ⟨p, hp, rfl⟩), ?_, rfl⟩
    intro hbad
    rcases (sublist_concat_iff (p ++ [b] ++ [b]) v b).mp hbad with hold | ⟨q, hq, heq⟩
    · exact hxnot ((List.sublist_append_left (p ++ [b]) [b]).trans hold)
    · have : p ++ [b] = q := List.append_cancel_right heq
      exact hxnot (this ▸ hq)

/-- Mixed-direction boundary recurrence. -/
theorem boundary_concat_other {v y : Word} {b c : Bool} (hbc : c ≠ b) :
    Boundary (v ++ [b]) c y ↔
      Boundary v c y ∨ ∃ x, Boundary v b x ∧ y = x ++ [c] := by
  constructor
  · rintro ⟨u, hu, hnot, rfl⟩
    by_cases huold : u.Sublist v
    · exact Or.inl ⟨u, huold, fun hy => hnot ((List.sublist_append_of_sublist_left hy)), rfl⟩
    · rcases (sublist_concat_iff u v b).mp hu with _ | ⟨p, hp, rfl⟩
      · contradiction
      · exact Or.inr ⟨p ++ [b], ⟨p, hp, huold, rfl⟩, rfl⟩
  · rintro (⟨u, hu, hnot, rfl⟩ | ⟨x, ⟨p, hp, hxnot, rfl⟩, rfl⟩)
    · refine ⟨u, List.sublist_append_of_sublist_left hu, ?_, rfl⟩
      intro hbad
      rcases (sublist_concat_iff (u ++ [c]) v b).mp hbad with hold | ⟨q, hq, heq⟩
      · exact hnot hold
      · exact hbc (singleton_suffix_eq heq)
    · refine ⟨p ++ [b], (sublist_concat_iff (p ++ [b]) v b).mpr
        (Or.inr ⟨p, hp, rfl⟩), ?_, rfl⟩
      intro hbad
      rcases (sublist_concat_iff (p ++ [b] ++ [c]) v b).mp hbad with hold | ⟨q, hq, heq⟩
      · exact hxnot ((List.sublist_append_left (p ++ [b]) [c]).trans hold)
      · exact hbc (singleton_suffix_eq heq)

/-! ## Lexicographic truncation of the boundary recurrences -/

/-- A boundary word remains on the same side of its generator when an arbitrary
symbol is appended to the word and the boundary direction is appended to the
generator.  The boundary hypothesis excludes the prefix anomaly. -/
theorem lex_boundary_append_target {v x : Word} {b : Bool}
    (hx : Boundary v b x) (c : Bool) :
    LexLT (x ++ [c]) (v ++ [b]) ↔ LexLT x v := by
  rcases hx with ⟨p, hp, hnot, rfl⟩
  induction v generalizing p with
  | nil =>
      have : p = [] := List.sublist_nil.mp hp
      subst p
      simp [LexLT]
  | cons a v ih =>
      cases p with
      | nil =>
          cases a <;> cases b <;> cases c <;> simp_all [LexLT]
      | cons d p =>
          cases d <;> cases a
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [b]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
          · simp [LexLT]
          · simp [LexLT]
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [b]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'

/-- Extending a generator by `0` does not change the lex status of an old
`1`-boundary word. -/
theorem lex_old_one_against_zero {v x : Word} (hx : Boundary v true x) :
    LexLT x (v ++ [false]) ↔ LexLT x v := by
  rcases hx with ⟨p, hp, hnot, rfl⟩
  induction v generalizing p with
  | nil =>
      have : p = [] := List.sublist_nil.mp hp
      subst p
      simp [LexLT]
  | cons a v ih =>
      cases p with
      | nil => cases a <;> simp_all [LexLT]
      | cons d p =>
          cases d <;> cases a
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [true]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
          · simp [LexLT]
          · simp [LexLT]
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [true]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'

/-- Extending a generator by `1` adds exactly the exceptional old boundary
word `v0` below the new generator. -/
theorem lex_old_zero_against_one {v x : Word} (hx : Boundary v false x) :
    LexLT x (v ++ [true]) ↔ LexLT x v ∨ x = v ++ [false] := by
  rcases hx with ⟨p, hp, hnot, rfl⟩
  induction v generalizing p with
  | nil =>
      have : p = [] := List.sublist_nil.mp hp
      subst p
      simp [LexLT]
  | cons a v ih =>
      cases p with
      | nil => cases a <;> simp_all [LexLT]
      | cons d p =>
          cases d <;> cases a
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [false]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
          · simp [LexLT]
          · simp [LexLT]
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [false]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'

/-- Lexicographically truncated directed boundary. -/
def LexBoundary (v : Word) (b : Bool) (y : Word) : Prop :=
  Boundary v b y ∧ LexLT y v

theorem lexBoundary_concat_same {v y : Word} {b : Bool} :
    LexBoundary (v ++ [b]) b y ↔
      ∃ x, LexBoundary v b x ∧ y = x ++ [b] := by
  rw [LexBoundary, boundary_concat_same]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hlex⟩
    exact ⟨x, ⟨hx, (lex_boundary_append_target hx b).mp hlex⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hlex⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (lex_boundary_append_target hx b).mpr hlex⟩

theorem lexBoundary_one_concat_zero {v y : Word} :
    LexBoundary (v ++ [false]) true y ↔
      LexBoundary v true y ∨
        ∃ x, LexBoundary v false x ∧ y = x ++ [true] := by
  rw [LexBoundary, boundary_concat_other (by decide : true ≠ false)]
  constructor
  · rintro ⟨hold | ⟨x, hx, rfl⟩, hlex⟩
    · exact Or.inl ⟨hold, (lex_old_one_against_zero hold).mp hlex⟩
    · exact Or.inr ⟨x, ⟨hx, (lex_boundary_append_target hx true).mp hlex⟩, rfl⟩
  · rintro (⟨hold, hlex⟩ | ⟨x, ⟨hx, hlex⟩, rfl⟩)
    · exact ⟨Or.inl hold, (lex_old_one_against_zero hold).mpr hlex⟩
    · exact ⟨Or.inr ⟨x, hx, rfl⟩, (lex_boundary_append_target hx true).mpr hlex⟩

theorem lexBoundary_zero_concat_one {v y : Word} :
    LexBoundary (v ++ [true]) false y ↔
      LexBoundary v false y ∨
        (∃ x, LexBoundary v true x ∧ y = x ++ [false]) ∨ y = v ++ [false] := by
  rw [LexBoundary, boundary_concat_other (by decide : false ≠ true)]
  constructor
  · rintro ⟨hold | ⟨x, hx, rfl⟩, hlex⟩
    · rcases (lex_old_zero_against_one hold).mp hlex with hlex | rfl
      · exact Or.inl ⟨hold, hlex⟩
      · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl ⟨x, ⟨hx, (lex_boundary_append_target hx false).mp hlex⟩, rfl⟩)
  · rintro (⟨hold, hlex⟩ | (⟨x, ⟨hx, hlex⟩, rfl⟩ | rfl))
    · exact ⟨Or.inl hold, (lex_old_zero_against_one hold).mpr (Or.inl hlex)⟩
    · exact ⟨Or.inr ⟨x, hx, rfl⟩, (lex_boundary_append_target hx false).mpr hlex⟩
    · have hvb : Boundary v false (v ++ [false]) :=
        ⟨v, List.Sublist.refl v, (by
          intro h
          have hlen := h.length_le
          simp at hlen), rfl⟩
      exact ⟨Or.inl hvb, (lex_old_zero_against_one hvb).mpr (Or.inr rfl)⟩

end TuDeng.FirstExit
