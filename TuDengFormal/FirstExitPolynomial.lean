import TuDengFormal.FirstExitBoundary

set_option linter.style.header false

/-!
# Cross-boundary enumerator identity

This module lifts the set-level boundary recurrences to the bivariate
enumerators used by the half-plane functional.
-/

namespace TuDeng.FirstExit

open scoped BigOperators

/-- Finite directed boundary. -/
def boundaryFinset (v : Word) (b : Bool) : Finset Word :=
  ((subwordFinset v).image fun u => u ++ [b]).filter fun y => ¬ y.Sublist v

/-- Finite lexicographically truncated directed boundary. -/
noncomputable def lexBoundaryFinset (v : Word) (b : Bool) : Finset Word := by
  classical
  exact (boundaryFinset v b).filter fun y => LexLT y v

theorem mem_boundaryFinset {v y : Word} {b : Bool} :
    y ∈ boundaryFinset v b ↔ Boundary v b y := by
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hy, hnot⟩
    rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
    exact ⟨u, mem_subwordFinset.mp hu, hnot, rfl⟩
  · rintro ⟨u, hu, hnot, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨u, mem_subwordFinset.mpr hu, rfl⟩, hnot⟩

theorem mem_lexBoundaryFinset {v y : Word} {b : Bool} :
    y ∈ lexBoundaryFinset v b ↔ LexBoundary v b y := by
  classical
  simp [lexBoundaryFinset, mem_boundaryFinset, LexBoundary]

theorem lexBoundaryFinset_concat_same (v : Word) (b : Bool) :
    lexBoundaryFinset (v ++ [b]) b =
      (lexBoundaryFinset v b).image (fun y => y ++ [b]) := by
  classical
  ext y
  rw [mem_lexBoundaryFinset, lexBoundary_concat_same]
  simp only [Finset.mem_image, mem_lexBoundaryFinset]
  aesop

theorem lexBoundaryFinset_one_concat_zero (v : Word) :
    lexBoundaryFinset (v ++ [false]) true =
      lexBoundaryFinset v true ∪
        (lexBoundaryFinset v false).image (fun y => y ++ [true]) := by
  classical
  ext y
  rw [mem_lexBoundaryFinset, lexBoundary_one_concat_zero]
  simp only [Finset.mem_union, Finset.mem_image, mem_lexBoundaryFinset]
  aesop

theorem lexBoundaryFinset_zero_concat_one (v : Word) :
    lexBoundaryFinset (v ++ [true]) false =
      (lexBoundaryFinset v false ∪
        (lexBoundaryFinset v true).image (fun y => y ++ [false])) ∪
          {v ++ [false]} := by
  classical
  ext y
  rw [mem_lexBoundaryFinset, lexBoundary_zero_concat_one]
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
    mem_lexBoundaryFinset]
  aesop

/-! ## Bivariate enumerators -/

abbrev BiPoly := MvPolynomial Bool ℤ

noncomputable def X : BiPoly := MvPolynomial.X false
noncomputable def Y : BiPoly := MvPolynomial.X true

noncomputable def wordMonomial (w : Word) : BiPoly := X ^ zeros w * Y ^ ones w

noncomputable def enumerator (S : Finset Word) : BiPoly := ∑ w ∈ S, wordMonomial w

theorem wordMonomial_append_false (w : Word) :
    wordMonomial (w ++ [false]) = X * wordMonomial w := by
  simp [wordMonomial, X, Y, zeros, ones, List.count_append]
  ring

theorem wordMonomial_append_true (w : Word) :
    wordMonomial (w ++ [true]) = Y * wordMonomial w := by
  simp [wordMonomial, X, Y, zeros, ones, List.count_append]
  ring

theorem enumerator_image_append (S : Finset Word) (b : Bool) :
    enumerator (S.image fun w => w ++ [b]) =
      (if b then Y else X) * enumerator S := by
  classical
  have hinj : Set.InjOn (fun w : Word => w ++ [b]) (S : Set Word) :=
    fun _ _ _ _ h => append_singleton_injective b h
  rw [enumerator, Finset.sum_image hinj]
  cases b
  · simp_rw [wordMonomial_append_false]
    simp [enumerator, Finset.mul_sum]
  · simp_rw [wordMonomial_append_true]
    simp [enumerator, Finset.mul_sum]

theorem enumerator_union {S T : Finset Word} (h : Disjoint S T) :
    enumerator (S ∪ T) = enumerator S + enumerator T := by
  simp [enumerator, Finset.sum_union h]

theorem enumerator_singleton (w : Word) : enumerator {w} = wordMonomial w := by
  simp [enumerator]

theorem not_lex_append_self (v : Word) (b : Bool) : ¬ LexLT (v ++ [b]) v := by
  induction v with
  | nil => simp
  | cons a v ih => simpa using ih

theorem disjoint_H_image_U (v : Word) : Disjoint (lexBoundaryFinset v true)
    ((lexBoundaryFinset v false).image fun x => x ++ [true]) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hyimage
  have hy' := (mem_lexBoundaryFinset.mp hy).1
  rcases hy' with ⟨u, hu, _, huy⟩
  rcases Finset.mem_image.mp hyimage with ⟨x, hx, hxy⟩
  have hx' := (mem_lexBoundaryFinset.mp hx).1
  rcases hx' with ⟨p, hp, hxnot, hpx⟩
  have hux : u = x := by
    apply List.append_cancel_right
    calc
      u ++ [true] = y := huy.symm
      _ = x ++ [true] := hxy.symm
  exact hxnot (hux ▸ hu)

theorem disjoint_U_image_H (v : Word) : Disjoint (lexBoundaryFinset v false)
    ((lexBoundaryFinset v true).image fun x => x ++ [false]) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hyimage
  have hy' := (mem_lexBoundaryFinset.mp hy).1
  rcases hy' with ⟨u, hu, _, huy⟩
  rcases Finset.mem_image.mp hyimage with ⟨x, hx, hxy⟩
  have hx' := (mem_lexBoundaryFinset.mp hx).1
  rcases hx' with ⟨p, hp, hxnot, hpx⟩
  have hux : u = x := by
    apply List.append_cancel_right
    calc
      u ++ [false] = y := huy.symm
      _ = x ++ [false] := hxy.symm
  exact hxnot (hux ▸ hu)

theorem exceptional_not_mem_U (v : Word) :
    v ++ [false] ∉ lexBoundaryFinset v false := by
  intro h
  exact not_lex_append_self v false (mem_lexBoundaryFinset.mp h).2

theorem exceptional_not_mem_image_H (v : Word) :
    v ++ [false] ∉ (lexBoundaryFinset v true).image (fun x => x ++ [false]) := by
  classical
  intro h
  rcases Finset.mem_image.mp h with ⟨x, hx, heq⟩
  have hxv : x = v := append_singleton_injective false heq
  have hboundary := (mem_lexBoundaryFinset.mp hx).1
  rcases hboundary with ⟨u, hu, hnot, hxu⟩
  exact hnot (hxv ▸ List.Sublist.refl v)

noncomputable def Uenum (v : Word) : BiPoly := enumerator (lexBoundaryFinset v false)
noncomputable def Henum (v : Word) : BiPoly := enumerator (lexBoundaryFinset v true)

theorem Uenum_concat_zero (v : Word) : Uenum (v ++ [false]) = X * Uenum v := by
  rw [Uenum, lexBoundaryFinset_concat_same, enumerator_image_append]
  simp [Uenum]

theorem Henum_concat_one (v : Word) : Henum (v ++ [true]) = Y * Henum v := by
  rw [Henum, lexBoundaryFinset_concat_same, enumerator_image_append]
  simp [Henum]

theorem Henum_concat_zero (v : Word) :
    Henum (v ++ [false]) = Henum v + Y * Uenum v := by
  rw [Henum, lexBoundaryFinset_one_concat_zero,
    enumerator_union (disjoint_H_image_U v), enumerator_image_append]
  simp [Henum, Uenum]

theorem Uenum_concat_one (v : Word) :
    Uenum (v ++ [true]) = Uenum v + X * Henum v + wordMonomial (v ++ [false]) := by
  have hdis₁ := disjoint_U_image_H v
  have hdis₂ : Disjoint
      (lexBoundaryFinset v false ∪
        (lexBoundaryFinset v true).image (fun x => x ++ [false])) {v ++ [false]} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_union]
    exact not_or_intro (exceptional_not_mem_U v) (exceptional_not_mem_image_H v)
  rw [Uenum, lexBoundaryFinset_zero_concat_one, enumerator_union hdis₂,
    enumerator_union hdis₁, enumerator_image_append, enumerator_singleton]
  simp [Uenum, Henum]

/-! ## The complete boundary and the tree identity -/

theorem boundaryFinset_concat_same (v : Word) (b : Bool) :
    boundaryFinset (v ++ [b]) b =
      (boundaryFinset v b).image (fun y => y ++ [b]) := by
  classical
  ext y
  rw [mem_boundaryFinset, boundary_concat_same]
  simp only [Finset.mem_image, mem_boundaryFinset]
  aesop

theorem boundaryFinset_concat_other (v : Word) (b c : Bool) (hbc : c ≠ b) :
    boundaryFinset (v ++ [b]) c =
      boundaryFinset v c ∪
        (boundaryFinset v b).image (fun y => y ++ [c]) := by
  classical
  ext y
  rw [mem_boundaryFinset, boundary_concat_other hbc]
  simp only [Finset.mem_union, Finset.mem_image, mem_boundaryFinset]
  aesop

theorem disjoint_boundary_image (v : Word) (b c : Bool) :
    Disjoint (boundaryFinset v c)
      ((boundaryFinset v b).image fun x => x ++ [c]) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hyimage
  rcases (mem_boundaryFinset.mp hy) with ⟨u, hu, _, huy⟩
  rcases Finset.mem_image.mp hyimage with ⟨x, hx, hxy⟩
  rcases (mem_boundaryFinset.mp hx) with ⟨p, hp, hxnot, hpx⟩
  have hux : u = x := by
    apply List.append_cancel_right
    calc
      u ++ [c] = y := huy.symm
      _ = x ++ [c] := hxy.symm
  exact hxnot (hux ▸ hu)

noncomputable def Benum (v : Word) (b : Bool) : BiPoly :=
  enumerator (boundaryFinset v b)

noncomputable def Ienum (v : Word) : BiPoly := enumerator (subwordFinset v)

theorem Benum_concat_same (v : Word) (b : Bool) :
    Benum (v ++ [b]) b = (if b then Y else X) * Benum v b := by
  rw [Benum, boundaryFinset_concat_same, enumerator_image_append]
  simp [Benum]

theorem Benum_concat_other (v : Word) (b c : Bool) (hbc : c ≠ b) :
    Benum (v ++ [b]) c = Benum v c + (if c then Y else X) * Benum v b := by
  rw [Benum, boundaryFinset_concat_other v b c hbc,
    enumerator_union (disjoint_boundary_image v b c), enumerator_image_append]
  simp [Benum]

theorem Benum_concat_zero_zero (v : Word) :
    Benum (v ++ [false]) false = X * Benum v false := by
  simpa using Benum_concat_same v false

theorem Benum_concat_zero_one (v : Word) :
    Benum (v ++ [false]) true = Benum v true + Y * Benum v false := by
  simpa using Benum_concat_other v false true (by decide)

theorem Benum_concat_one_zero (v : Word) :
    Benum (v ++ [true]) false = Benum v false + X * Benum v true := by
  simpa using Benum_concat_other v true false (by decide)

theorem Benum_concat_one_one (v : Word) :
    Benum (v ++ [true]) true = Y * Benum v true := by
  simpa using Benum_concat_same v true

theorem subwordFinset_concat (v : Word) (b : Bool) :
    subwordFinset (v ++ [b]) = subwordFinset v ∪ boundaryFinset v b := by
  classical
  ext y
  rw [mem_subwordFinset, sublist_concat_iff]
  simp only [Finset.mem_union, mem_subwordFinset, mem_boundaryFinset]
  constructor
  · rintro (hold | ⟨u, hu, rfl⟩)
    · exact Or.inl hold
    · by_cases hnew : (u ++ [b]).Sublist v
      · exact Or.inl hnew
      · exact Or.inr ⟨u, hu, hnew, rfl⟩
  · rintro (hold | ⟨u, hu, _, rfl⟩)
    · exact Or.inl hold
    · exact Or.inr ⟨u, hu, rfl⟩

theorem disjoint_subword_boundary (v : Word) (b : Bool) :
    Disjoint (subwordFinset v) (boundaryFinset v b) := by
  rw [Finset.disjoint_left]
  intro y hy hb
  rcases mem_boundaryFinset.mp hb with ⟨u, _, hnot, rfl⟩
  exact hnot (mem_subwordFinset.mp hy)

theorem Ienum_concat (v : Word) (b : Bool) :
    Ienum (v ++ [b]) = Ienum v + Benum v b := by
  rw [Ienum, subwordFinset_concat,
    enumerator_union (disjoint_subword_boundary v b)]
  rfl

noncomputable def Lambda : BiPoly := X + Y - 1

theorem boundaryFinset_nil (b : Bool) : boundaryFinset [] b = {[b]} := by
  ext y
  simp only [mem_boundaryFinset, Boundary, List.sublist_nil, Finset.mem_singleton]
  constructor
  · rintro ⟨u, rfl, hnot, rfl⟩
    exact rfl
  · rintro rfl
    exact ⟨[], rfl, by simp, rfl⟩

theorem Benum_nil (b : Bool) : Benum [] b = if b then Y else X := by
  cases b <;>
    simp [Benum, boundaryFinset_nil, enumerator_singleton, wordMonomial,
      X, Y, zeros, ones]

theorem lexBoundaryFinset_nil (b : Bool) : lexBoundaryFinset [] b = ∅ := by
  ext y
  rw [mem_lexBoundaryFinset]
  constructor
  · rintro ⟨_, hlex⟩
    cases y <;> simp at hlex
  · intro h
    simp at h

theorem Uenum_nil : Uenum [] = 0 := by simp [Uenum, lexBoundaryFinset_nil, enumerator]
theorem Henum_nil : Henum [] = 0 := by simp [Henum, lexBoundaryFinset_nil, enumerator]

/-- The two directed boundary enumerators are the leaves of the finite
subsequence tree. -/
theorem boundary_tree_identity (v : Word) :
    Benum v false + Benum v true = 1 + Lambda * Ienum v := by
  induction v using List.reverseRecOn with
  | nil =>
      rw [Benum_nil, Benum_nil]
      rw [show Ienum [] = 1 by
        simp [Ienum, subwordFinset, enumerator, wordMonomial, X, Y, zeros, ones]]
      dsimp [Lambda]
      ring
  | append_singleton v b ih =>
      cases b
      · rw [Benum_concat_zero_zero, Benum_concat_zero_one,
          Ienum_concat]
        calc
          X * Benum v false + (Benum v true + Y * Benum v false) =
              (Benum v false + Benum v true) + Lambda * Benum v false := by
                dsimp [Lambda]
                ring
          _ = (1 + Lambda * Ienum v) + Lambda * Benum v false := by rw [ih]
          _ = 1 + Lambda * (Ienum v + Benum v false) := by ring
      · rw [Benum_concat_one_zero, Benum_concat_one_one,
          Ienum_concat]
        calc
          Benum v false + X * Benum v true + Y * Benum v true =
              (Benum v false + Benum v true) + Lambda * Benum v true := by
                dsimp [Lambda]
                ring
          _ = (1 + Lambda * Ienum v) + Lambda * Benum v true := by rw [ih]
          _ = 1 + Lambda * (Ienum v + Benum v true) := by ring

/-! ## The positive-prefix lift -/

noncomputable def dMonomial (v : Word) : BiPoly := wordMonomial (v ++ [false])
noncomputable def sMonomial (v : Word) : BiPoly := Y * dMonomial v

theorem dMonomial_concat_zero (v : Word) :
    dMonomial (v ++ [false]) = X * dMonomial v := by
  change wordMonomial ((v ++ [false]) ++ [false]) = X * wordMonomial (v ++ [false])
  exact wordMonomial_append_false (v ++ [false])

theorem dMonomial_concat_one (v : Word) :
    dMonomial (v ++ [true]) = Y * dMonomial v := by
  change wordMonomial ((v ++ [true]) ++ [false]) = Y * wordMonomial (v ++ [false])
  rw [wordMonomial_append_false, wordMonomial_append_true,
    wordMonomial_append_false]
  ring

theorem sMonomial_eq_Yd (v : Word) : sMonomial v = Y * dMonomial v := rfl

/-- Prefixing the generator by `0` changes its two complete boundary
enumerators by the lexicographically truncated boundary vector. -/
theorem positive_prefix_lift (v : Word) :
    (Benum (false :: v) false - Benum v false =
        -sMonomial v + Lambda * (Uenum v + dMonomial v)) ∧
    (Benum (false :: v) true - Benum v true =
        sMonomial v + Lambda * Henum v) := by
  induction v using List.reverseRecOn with
  | nil =>
      constructor
      · rw [show false :: [] = [] ++ [false] by rfl,
          Benum_concat_zero_zero, Benum_nil, Uenum_nil]
        simp [sMonomial, dMonomial, wordMonomial, X, Y, zeros, ones, Lambda]
        ring
      · rw [show false :: [] = [] ++ [false] by rfl,
          Benum_concat_zero_one, Benum_nil, Henum_nil]
        simp [Benum_nil, sMonomial, dMonomial, wordMonomial, X, Y, zeros, ones,
          Lambda]
  | append_singleton v b ih =>
      rcases ih with ⟨ih₀, ih₁⟩
      cases b
      · rw [show false :: (v ++ [false]) = (false :: v) ++ [false] by simp]
        constructor
        · rw [Benum_concat_zero_zero, Benum_concat_zero_zero,
            Uenum_concat_zero, dMonomial_concat_zero]
          calc
            X * Benum (false :: v) false - X * Benum v false =
                X * (Benum (false :: v) false - Benum v false) := by ring
            _ = X * (-sMonomial v + Lambda * (Uenum v + dMonomial v)) := by rw [ih₀]
            _ = -sMonomial (v ++ [false]) +
                Lambda * (X * Uenum v + X * dMonomial v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_zero]
                  ring
        · rw [Benum_concat_zero_one, Benum_concat_zero_one,
            Henum_concat_zero]
          calc
            (Benum (false :: v) true + Y * Benum (false :: v) false) -
                (Benum v true + Y * Benum v false) =
                (Benum (false :: v) true - Benum v true) +
                  Y * (Benum (false :: v) false - Benum v false) := by ring
            _ = (sMonomial v + Lambda * Henum v) +
                Y * (-sMonomial v + Lambda * (Uenum v + dMonomial v)) := by
                  rw [ih₀, ih₁]
            _ = sMonomial (v ++ [false]) +
                Lambda * (Henum v + Y * Uenum v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_zero]
                  dsimp [Lambda]
                  ring
      · rw [show false :: (v ++ [true]) = (false :: v) ++ [true] by simp]
        constructor
        · rw [Benum_concat_one_zero, Benum_concat_one_zero,
            Uenum_concat_one, dMonomial_concat_one]
          calc
            (Benum (false :: v) false + X * Benum (false :: v) true) -
                (Benum v false + X * Benum v true) =
                (Benum (false :: v) false - Benum v false) +
                  X * (Benum (false :: v) true - Benum v true) := by ring
            _ = (-sMonomial v + Lambda * (Uenum v + dMonomial v)) +
                X * (sMonomial v + Lambda * Henum v) := by rw [ih₀, ih₁]
            _ = -sMonomial (v ++ [true]) +
                Lambda * (Uenum v + X * Henum v + dMonomial v +
                  Y * dMonomial v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_one]
                  dsimp [Lambda]
                  ring
        · rw [Benum_concat_one_one, Benum_concat_one_one,
            Henum_concat_one]
          calc
            Y * Benum (false :: v) true - Y * Benum v true =
                Y * (Benum (false :: v) true - Benum v true) := by ring
            _ = Y * (sMonomial v + Lambda * Henum v) := by rw [ih₁]
            _ = sMonomial (v ++ [true]) + Lambda * (Y * Henum v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_one]
                  ring

/-! ## The cross-boundary identity -/

noncomputable def Jenum (v : Word) : BiPoly := Ienum v + Henum v

noncomputable def Cenum (v : Word) : BiPoly :=
  Benum (false :: v) true + Benum v false

/-- Exact formal counterpart of the paper's cross-boundary identity
`C_v = 1 + (X + Y - 1) J_v + s_v`. -/
theorem cross_boundary_identity (v : Word) :
    Cenum v = 1 + Lambda * Jenum v + sMonomial v := by
  have hlift := (positive_prefix_lift v).2
  calc
    Cenum v = (Benum v false + Benum v true) +
        (Benum (false :: v) true - Benum v true) := by
          dsimp [Cenum]
          ring
    _ = (1 + Lambda * Ienum v) +
        (sMonomial v + Lambda * Henum v) := by
          rw [boundary_tree_identity, hlift]
    _ = 1 + Lambda * Jenum v + sMonomial v := by
          dsimp [Jenum]
          ring

theorem langFinset_eq (v : Word) :
    langFinset v = subwordFinset v ∪ lexBoundaryFinset v true := by
  classical
  ext y
  rw [mem_langFinset]
  simp only [Finset.mem_union, mem_subwordFinset, mem_lexBoundaryFinset,
    Lang, LexBoundary, boundary_true_iff]

theorem disjoint_subword_lexBoundary (v : Word) :
    Disjoint (subwordFinset v) (lexBoundaryFinset v true) := by
  rw [Finset.disjoint_left]
  intro y hy hb
  rcases (mem_lexBoundaryFinset.mp hb).1 with ⟨u, _, hnot, rfl⟩
  exact hnot (mem_subwordFinset.mp hy)

theorem enumerator_langFinset (v : Word) :
    enumerator (langFinset v) = Jenum v := by
  rw [langFinset_eq, enumerator_union (disjoint_subword_lexBoundary v)]
  rfl

end TuDeng.FirstExit
