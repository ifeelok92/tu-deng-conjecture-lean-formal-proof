import TuDengFormal.FirstExitPolynomial

set_option linter.style.header false

/-!
# The strict half-plane functional

This module applies the strict half-plane functional to the exact
cross-boundary identity and connects it to the marked-deletion inequality.
-/

namespace TuDeng.FirstExit

open scoped BigOperators

/-- Strict negative-half-plane mass, after substituting `X = Y = 1/2`. -/
noncomputable def phiNeg (p : BiPoly) : ℚ :=
  p.sum fun e c =>
    if e false > e true then (c : ℚ) / (2 : ℚ) ^ (e false + e true) else 0

theorem phiNeg_add (p q : BiPoly) : phiNeg (p + q) = phiNeg p + phiNeg q := by
  apply Finsupp.sum_add_index
  · intro e he
    simp
  · intro e he a b
    by_cases h : e false > e true
    · simp [phiNeg, h]
      push_cast
      ring
    · simp [phiNeg, h]

theorem phiNeg_zero : phiNeg (0 : BiPoly) = 0 := by
  exact Finsupp.sum_zero_index

theorem phiNeg_neg (p : BiPoly) : phiNeg (-p) = -phiNeg p := by
  have h := phiNeg_add p (-p)
  rw [add_neg_cancel, phiNeg_zero] at h
  linarith

theorem phiNeg_sub (p q : BiPoly) : phiNeg (p - q) = phiNeg p - phiNeg q := by
  rw [sub_eq_add_neg, phiNeg_add, phiNeg_neg]
  ring

theorem phiNeg_monomial (e : Bool →₀ ℕ) (c : ℤ) :
    phiNeg ((MvPolynomial.monomial e) c) =
      if e false > e true then (c : ℚ) / (2 : ℚ) ^ (e false + e true) else 0 := by
  simp [phiNeg, MvPolynomial.monomial]

theorem wordMonomial_eq_monomial (w : Word) :
    wordMonomial w =
      (MvPolynomial.monomial
        (Finsupp.single false (zeros w) + Finsupp.single true (ones w))) 1 := by
  rw [wordMonomial, X, Y, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
  simp

theorem phiNeg_wordMonomial (w : Word) :
    phiNeg (wordMonomial w) =
      if ones w < zeros w then 1 / (2 : ℚ) ^ (zeros w + ones w) else 0 := by
  rw [wordMonomial_eq_monomial, phiNeg_monomial]
  simp [Finsupp.single_apply]

theorem phiNeg_finset_sum {A : Type*} (S : Finset A) (f : A → BiPoly) :
    phiNeg (∑ x ∈ S, f x) = ∑ x ∈ S, phiNeg (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [phiNeg_zero]
  | @insert x S hx ih => simp [hx, phiNeg_add, ih]

theorem phiNeg_enumerator (S : Finset Word) :
    phiNeg (enumerator S) =
      ∑ w ∈ S, if ones w < zeros w then
        1 / (2 : ℚ) ^ (zeros w + ones w) else 0 := by
  rw [enumerator, phiNeg_finset_sum]
  simp_rw [phiNeg_wordMonomial]

@[simp] theorem zeros_append_false (w : Word) : zeros (w ++ [false]) = zeros w + 1 := by
  simp [zeros, List.count_append]

@[simp] theorem ones_append_false (w : Word) : ones (w ++ [false]) = ones w := by
  simp [ones, List.count_append]

@[simp] theorem zeros_append_true (w : Word) : zeros (w ++ [true]) = zeros w := by
  simp [zeros, List.count_append]

@[simp] theorem ones_append_true (w : Word) : ones (w ++ [true]) = ones w + 1 := by
  simp [ones, List.count_append]

/-- The half-plane functional of `Lambda` times one word monomial.  All
monomials cancel except those on the diagonal and the adjacent subdiagonal. -/
theorem phiNeg_Lambda_wordMonomial (w : Word) :
    phiNeg (Lambda * wordMonomial w) =
      if zeros w = ones w then 1 / (2 : ℚ) ^ (2 * zeros w + 1)
      else if zeros w = ones w + 1 then -(1 / (2 : ℚ) ^ (2 * zeros w))
      else 0 := by
  have hpoly : Lambda * wordMonomial w =
      wordMonomial (w ++ [false]) + wordMonomial (w ++ [true]) - wordMonomial w := by
    rw [wordMonomial_append_false, wordMonomial_append_true]
    dsimp [Lambda]
    ring
  rw [hpoly, phiNeg_sub, phiNeg_add, phiNeg_wordMonomial,
    phiNeg_wordMonomial, phiNeg_wordMonomial]
  rw [zeros_append_false, ones_append_false, zeros_append_true, ones_append_true]
  by_cases hd : zeros w = ones w
  · rw [if_pos hd]
    simp only [if_pos (by omega : ones w < zeros w + 1),
      if_neg (by omega : ¬ ones w + 1 < zeros w),
      if_neg (by omega : ¬ ones w < zeros w)]
    rw [show zeros w + 1 + ones w = 2 * zeros w + 1 by omega]
    ring
  · rw [if_neg hd]
    by_cases hs : zeros w = ones w + 1
    · rw [if_pos hs]
      simp only [if_pos (by omega : ones w < zeros w + 1),
        if_neg (by omega : ¬ ones w + 1 < zeros w),
        if_pos (by omega : ones w < zeros w)]
      rw [show zeros w + 1 + ones w = 2 * zeros w by omega,
        show 2 * zeros w = (zeros w + ones w) + 1 by omega, pow_succ]
      field_simp
      ring
    · rw [if_neg hs]
      by_cases hfar : ones w + 2 ≤ zeros w
      · simp only [if_pos (by omega : ones w < zeros w + 1),
          if_pos (by omega : ones w + 1 < zeros w),
          if_pos (by omega : ones w < zeros w)]
        rw [show zeros w + 1 + ones w = (zeros w + ones w) + 1 by omega,
          show zeros w + (ones w + 1) = (zeros w + ones w) + 1 by omega,
          pow_succ]
        field_simp
        ring
      · have hle : zeros w ≤ ones w := by omega
        simp only [if_neg (by omega : ¬ ones w < zeros w + 1),
          if_neg (by omega : ¬ ones w + 1 < zeros w),
          if_neg (by omega : ¬ ones w < zeros w)]
        ring

theorem phiNeg_Lambda_enumerator (L : Finset Word) :
    phiNeg (Lambda * enumerator L) =
      ∑ w ∈ L,
        if zeros w = ones w then 1 / (2 : ℚ) ^ (2 * zeros w + 1)
        else if zeros w = ones w + 1 then -(1 / (2 : ℚ) ^ (2 * zeros w))
        else 0 := by
  rw [enumerator, Finset.mul_sum, phiNeg_finset_sum]
  simp_rw [phiNeg_Lambda_wordMonomial]

private theorem diagonal_filter_eq_layer (L : Finset Word) (m : ℕ) :
    ((L.filter fun w => zeros w = ones w).filter fun w => zeros w = m) =
      layer L m m := by
  ext w
  simp [layer]
  aesop

private theorem subdiagonal_filter_eq_layer (L : Finset Word) (m : ℕ) (hm : 1 ≤ m) :
    ((L.filter fun w => zeros w = ones w + 1).filter fun w => zeros w = m) =
      layer L m (m - 1) := by
  ext w
  simp only [Finset.mem_filter, layer]
  constructor
  · rintro ⟨⟨hw, hsub⟩, hz⟩
    exact ⟨hw, hz, by omega⟩
  · rintro ⟨hw, hz, ho⟩
    exact ⟨⟨hw, by omega⟩, hz⟩

theorem diagonal_sum_eq (L : Finset Word) (M : ℕ)
    (hbound : ∀ w ∈ L, zeros w = ones w → zeros w ≤ M) :
    (∑ w ∈ L, if zeros w = ones w then
        1 / (2 : ℚ) ^ (2 * zeros w + 1) else 0) =
      ∑ m ∈ Finset.Icc 0 M,
        (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) := by
  classical
  rw [← Finset.sum_filter]
  have hmap : ∀ w ∈ L.filter (fun w => zeros w = ones w),
      zeros w ∈ Finset.Icc 0 M := by
    intro w hw
    simp only [Finset.mem_filter] at hw
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hbound w hw.1 hw.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun w => 1 / (2 : ℚ) ^ (2 * zeros w + 1))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [diagonal_filter_eq_layer]
  calc
    (∑ w ∈ layer L m m, 1 / (2 : ℚ) ^ (2 * zeros w + 1)) =
        ∑ _w ∈ layer L m m, 1 / (2 : ℚ) ^ (2 * m + 1) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2.1]
    _ = (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) := by
          simp [jCoeff, div_eq_mul_inv]

theorem subdiagonal_sum_eq (L : Finset Word) (M : ℕ)
    (hbound : ∀ w ∈ L, zeros w = ones w + 1 → zeros w ≤ M) :
    (∑ w ∈ L, if zeros w = ones w + 1 then
        -(1 / (2 : ℚ) ^ (2 * zeros w)) else 0) =
      ∑ m ∈ Finset.Icc 1 M,
        -((jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m)) := by
  classical
  rw [← Finset.sum_filter]
  have hmap : ∀ w ∈ L.filter (fun w => zeros w = ones w + 1),
      zeros w ∈ Finset.Icc 1 M := by
    intro w hw
    simp only [Finset.mem_filter] at hw
    exact Finset.mem_Icc.mpr ⟨(by omega), hbound w hw.1 hw.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun w => -(1 / (2 : ℚ) ^ (2 * zeros w)))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [subdiagonal_filter_eq_layer L m (Finset.mem_Icc.mp hm).1]
  calc
    (∑ w ∈ layer L m (m - 1), -(1 / (2 : ℚ) ^ (2 * zeros w))) =
        ∑ _w ∈ layer L m (m - 1), -(1 / (2 : ℚ) ^ (2 * m)) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2.1]
    _ = -((jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m)) := by
          simp [jCoeff, div_eq_mul_inv]

private theorem lambda_contribution_split (L : Finset Word) :
    (∑ w ∈ L,
      if zeros w = ones w then 1 / (2 : ℚ) ^ (2 * zeros w + 1)
      else if zeros w = ones w + 1 then -(1 / (2 : ℚ) ^ (2 * zeros w))
      else 0) =
    (∑ w ∈ L, if zeros w = ones w then
      1 / (2 : ℚ) ^ (2 * zeros w + 1) else 0) +
    (∑ w ∈ L, if zeros w = ones w + 1 then
      -(1 / (2 : ℚ) ^ (2 * zeros w)) else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hd : zeros w = ones w
  · have hs : ¬ zeros w = ones w + 1 := by omega
    simp [hd, hs]
  · by_cases hs : zeros w = ones w + 1
    · simp [hd, hs]
    · simp [hd, hs]

theorem jCoeff_lang_zero_zero (v : Word) : jCoeff (langFinset v) 0 0 = 1 := by
  rw [jCoeff]
  have hlayer : layer (langFinset v) 0 0 = {[]} := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨_, hz, ho⟩
      have hlen : w.length = 0 := by
        have := zeros_add_ones w
        omega
      have hw_nil : w = [] := List.length_eq_zero_iff.mp hlen
      simpa [hw_nil]
    · intro hw
      have hw_nil : w = [] := by simpa using hw
      subst w
      exact Finset.mem_filter.mpr ⟨mem_langFinset.mpr (Or.inl (List.nil_sublist v)),
        by simp [zeros, ones]⟩
  rw [hlayer]
  simp

private theorem Icc_zero_split (M : ℕ) :
    Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
  ext m
  simp
  omega

/-- The polynomial half-plane functional is exactly the finite defect sum
used by the marked-deletion argument. -/
theorem phiNeg_Lambda_Jenum (v : Word) :
    phiNeg (Lambda * Jenum v) =
      halfplaneDefect (langFinset v) (ones v + 1) := by
  rw [← enumerator_langFinset, phiNeg_Lambda_enumerator,
    lambda_contribution_split]
  have hdiag := diagonal_sum_eq (langFinset v) (ones v + 1) (by
    intro w hw heq
    have hle := langFinset_ones_le hw
    omega)
  have hsub := subdiagonal_sum_eq (langFinset v) (ones v + 1) (by
    intro w hw heq
    have hle := langFinset_ones_le hw
    omega)
  rw [hdiag, hsub, Icc_zero_split]
  have hzero : 0 ∉ Finset.Icc 1 (ones v + 1) := by simp
  rw [Finset.sum_insert hzero, jCoeff_lang_zero_zero]
  norm_num only [Nat.cast_one, Nat.reduceMul, zero_add, pow_one, one_div]
  have hcombine :
      (∑ m ∈ Finset.Icc 1 (ones v + 1),
          (jCoeff (langFinset v) m m : ℚ) / (2 : ℚ) ^ (2 * m + 1)) +
      (∑ m ∈ Finset.Icc 1 (ones v + 1),
          -((jCoeff (langFinset v) m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m))) =
      ∑ m ∈ Finset.Icc 1 (ones v + 1), defectTerm (langFinset v) m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [defectTerm]
    ring
  rw [add_assoc, hcombine]
  rfl

theorem phiNeg_one : phiNeg (1 : BiPoly) = 0 := by
  rw [show (1 : BiPoly) = (MvPolynomial.monomial 0) 1 by simp,
    phiNeg_monomial]
  simp

theorem sMonomial_eq_wordMonomial (v : Word) :
    sMonomial v = wordMonomial ((v ++ [false]) ++ [true]) := by
  rw [wordMonomial_append_true]
  rfl

theorem phiNeg_sMonomial (v : Word) : phiNeg (sMonomial v) = exceptionMass v := by
  rw [sMonomial_eq_wordMonomial, phiNeg_wordMonomial]
  simp only [zeros_append_true, ones_append_true, zeros_append_false, ones_append_false]
  dsimp [exceptionMass]
  by_cases h : ones v < zeros v
  · rw [if_pos h, if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg h, if_neg (by omega)]

theorem phiNeg_Cenum_formula (v : Word) :
    phiNeg (Cenum v) =
      halfplaneDefect (langFinset v) (ones v + 1) + exceptionMass v := by
  rw [cross_boundary_identity, phiNeg_add, phiNeg_add, phiNeg_one,
    phiNeg_Lambda_Jenum, phiNeg_sMonomial, zero_add]

/-- Kernel-checked half-plane bound for the complete cross-boundary
enumerator.  This is the full combinatorial/polynomial half of the claimed
Tu--Deng proof. -/
theorem cross_boundary_halfplane_bound (v : Word) :
    phiNeg (Cenum v) ≤ 1 / 2 := by
  rw [phiNeg_Cenum_formula]
  exact lex_language_halfplane_with_exception v (ones v + 1) (le_refl _)

end TuDeng.FirstExit
