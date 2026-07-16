import TuDengFormal.FirstExitFunctional

set_option linter.style.header false

/-!
# Cyclic carries and first-exit codes

This module formalizes the exact carry-code reduction.  Bits are read from
low to high.  At an active position (`carry ≠ target bit`) the recorded
symbol is the complement of the input bit.
-/

namespace TuDeng.FirstExit

open scoped BigOperators

/-- A possible active-position code while scanning target word `q`, starting
with carry `c` and ending with carry `cf`.  Inactive input bits are omitted. -/
def ValidCode : Word → Bool → Bool → Word → Prop
  | [], c, cf, y => y = [] ∧ c = cf
  | t :: q, c, cf, y =>
      if c = t then ValidCode q c cf y
      else match y with
        | [] => False
        | x :: xs => ValidCode q (!x) cf xs

noncomputable instance validCodeDecidable (q : Word) (c cf : Bool) (y : Word) :
    Decidable (ValidCode q c cf y) := Classical.propDecidable _

/-- Number of input words realizing a code.  Each inactive position has two
free choices; an active symbol fixes the input bit. -/
def codeMultiplicity : Word → Bool → Bool → Word → ℕ
  | [], c, cf, y => if y = [] ∧ c = cf then 1 else 0
  | t :: q, c, cf, y =>
      if c = t then 2 * codeMultiplicity q c cf y
      else match y with
        | [] => 0
        | x :: xs => codeMultiplicity q (!x) cf xs

theorem validCode_length_le {q y : Word} {c cf : Bool}
    (h : ValidCode q c cf y) : y.length ≤ q.length := by
  induction q generalizing c y with
  | nil => simpa [h.1]
  | cons t q ih =>
      simp only [ValidCode] at h
      split at h
      · exact Nat.le.step (ih h)
      · cases y with
        | nil => contradiction
        | cons x xs =>
            simp only [List.length_cons, Nat.succ_le_succ_iff]
            exact ih h

theorem codeMultiplicity_of_valid {q y : Word} {c cf : Bool}
    (h : ValidCode q c cf y) :
    codeMultiplicity q c cf y = 2 ^ (q.length - y.length) := by
  induction q generalizing c y with
  | nil =>
      rcases h with ⟨rfl, rfl⟩
      simp [codeMultiplicity]
  | cons t q ih =>
      by_cases hct : c = t
      · have htail : ValidCode q c cf y := by simpa [ValidCode, hct] using h
        have hlen := validCode_length_le htail
        cases y with
        | nil =>
            rw [codeMultiplicity, if_pos hct, ih htail]
            simp only [List.length_nil, List.length_cons, Nat.sub_zero]
            rw [pow_succ]
            ring
        | cons x xs =>
            rw [codeMultiplicity, if_pos hct, ih htail]
            have hlen' : xs.length + 1 ≤ q.length := by simpa using hlen
            rw [show (t :: q).length - (x :: xs).length =
                (q.length - (x :: xs).length) + 1 by
              simp only [List.length_cons]
              omega, pow_succ]
            ring
      · have hactive := h
        simp only [ValidCode, hct, if_false] at hactive
        cases y with
        | nil => contradiction
        | cons x xs =>
            change (if c = t then 2 * codeMultiplicity q c cf (x :: xs)
              else codeMultiplicity q (!x) cf xs) = _
            rw [if_neg hct, ih hactive]
            simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]

theorem codeMultiplicity_of_not_valid {q y : Word} {c cf : Bool}
    (h : ¬ ValidCode q c cf y) : codeMultiplicity q c cf y = 0 := by
  induction q generalizing c y with
  | nil =>
      simp only [ValidCode] at h
      simp [codeMultiplicity, h]
  | cons t q ih =>
      by_cases hct : c = t
      · have htail : ¬ ValidCode q c cf y := by simpa [ValidCode, hct] using h
        cases y with
        | nil =>
            rw [codeMultiplicity, if_pos hct, ih htail]
        | cons x xs =>
            rw [codeMultiplicity, if_pos hct, ih htail]
      · cases y with
        | nil =>
            change (if c = t then 2 * codeMultiplicity q c cf [] else 0) = 0
            rw [if_neg hct]
        | cons x xs =>
            change (if c = t then 2 * codeMultiplicity q c cf (x :: xs)
              else codeMultiplicity q (!x) cf xs) = 0
            rw [if_neg hct]
            apply ih
            simpa [ValidCode, hct] using h

private theorem boundary_cons_ne {q xs : Word} {t x b : Bool} (hxt : x ≠ t) :
    Boundary (t :: q) b (x :: xs) ↔ Boundary q b (x :: xs) := by
  constructor
  · rintro ⟨u, hu, hnot, heq⟩
    have huq : u.Sublist q := by
      cases u with
      | nil => exact List.nil_sublist q
      | cons d ds =>
          have hdx : d = x := by simpa using congrArg List.head? heq.symm
          subst d
          simpa [List.sublist_cons_iff, hxt] using hu
    refine ⟨u, huq, ?_, heq⟩
    intro hbad
    exact hnot (hbad.cons t)
  · rintro ⟨u, hu, hnot, heq⟩
    refine ⟨u, hu.cons t, ?_, heq⟩
    intro hbad
    have : (x :: xs).Sublist q := by
      simpa [List.sublist_cons_iff, hxt] using hbad
    exact hnot this

private theorem boundary_cons_same_nonempty {q zs : Word} {t z b : Bool} :
    Boundary (t :: q) b (t :: z :: zs) ↔ Boundary q b (z :: zs) := by
  constructor
  · rintro ⟨u, hu, hnot, heq⟩
    cases u with
    | nil => simp at heq
    | cons d ds =>
        have hdtail : t = d ∧ z :: zs = ds ++ [b] := by simpa using heq
        have hd : t = d := hdtail.1
        subst d
        refine ⟨ds, List.cons_sublist_cons.mp hu, ?_, hdtail.2⟩
        intro hbad
        exact hnot (List.Sublist.cons_cons t hbad)
  · rintro ⟨u, hu, hnot, heq⟩
    refine ⟨t :: u, List.Sublist.cons_cons t hu, ?_, by
      simpa using congrArg (List.cons t) heq⟩
    intro hbad
    exact hnot (List.cons_sublist_cons.mp hbad)

private theorem not_boundary_cons_singleton (q : Word) (t b : Bool) :
    ¬ Boundary (t :: q) b [t] := by
  rintro ⟨u, hu, hnot, heq⟩
  exact hnot (List.Sublist.cons_cons t (List.nil_sublist q))

/-- Once an active symbol `x` has been read, the remainder of a valid cyclic
trace is equivalent to saying that the complete active word first exits the
subsequence ideal of the unread target suffix. -/
theorem validCode_after_active (q : Word) (x cf : Bool) (xs : Word) :
    ValidCode q (!x) cf xs ↔ Boundary q (!cf) (x :: xs) := by
  induction q generalizing x cf xs with
  | nil =>
      cases x <;> cases cf <;> cases xs <;> simp [ValidCode, Boundary]
  | cons t q ih =>
      by_cases hxt : x = t
      · subst x
        cases xs with
        | nil =>
            simp only [ValidCode, Bool.not_eq_self, if_false]
            exact (iff_false_intro (not_boundary_cons_singleton q t (!cf))).symm
        | cons z zs =>
            simp only [ValidCode, Bool.not_eq_self, if_false]
            rw [boundary_cons_same_nonempty]
            exact ih z cf zs
      · have hnotx_eq_t : (!x) = t := by
          cases x <;> cases t <;> simp_all
        simp only [ValidCode, hnotx_eq_t, if_true]
        rw [boundary_cons_ne hxt]
        simpa [hnotx_eq_t] using ih x cf xs

theorem validCode_zero_start (v y : Word) :
    ValidCode (true :: false :: v) false false y ↔
      Boundary (false :: v) true y := by
  cases y with
  | nil =>
      simp [ValidCode, Boundary]
  | cons x xs =>
      change ValidCode (false :: v) (!x) false xs ↔
        Boundary (false :: v) true (x :: xs)
      exact validCode_after_active (false :: v) x false xs

theorem validCode_one_start (v y : Word) :
    ValidCode (true :: false :: v) true true y ↔ Boundary v false y := by
  cases y with
  | nil =>
      simp [ValidCode, Boundary]
  | cons x xs =>
      simp only [ValidCode, if_true, Bool.true_eq_false, if_false]
      simpa using validCode_after_active v x true xs

/-! ## Finite code sets and multiplicities -/

/-- All binary words of length at most `n`. -/
def wordsLe : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 =>
      wordsLe n ∪ (wordsLe n).image (fun w => false :: w) ∪
        (wordsLe n).image (fun w => true :: w)

theorem mem_wordsLe {n : ℕ} {w : Word} : w ∈ wordsLe n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsLe, List.length_eq_zero_iff]
  | succ n ih =>
      cases w with
      | nil =>
          constructor
          · intro _
            simp
          · intro _
            simp only [wordsLe, Finset.mem_union]
            exact Or.inl (Or.inl ((ih (w := [])).mpr (Nat.zero_le n)))
      | cons b w =>
          cases b <;> simp [wordsLe, ih] <;> omega

noncomputable def validCodes (q : Word) (c cf : Bool) : Finset Word :=
  (wordsLe q.length).filter fun y => ValidCode q c cf y

noncomputable def negativeValidCodes (q : Word) (c cf : Bool) : Finset Word :=
  (validCodes q c cf).filter fun y => ones y < zeros y

theorem mem_validCodes {q y : Word} {c cf : Bool} :
    y ∈ validCodes q c cf ↔ ValidCode q c cf y := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_wordsLe.mpr (validCode_length_le h), h⟩

theorem mem_negativeValidCodes {q y : Word} {c cf : Bool} :
    y ∈ negativeValidCodes q c cf ↔
      ValidCode q c cf y ∧ ones y < zeros y := by
  classical
  simp [negativeValidCodes, mem_validCodes]

noncomputable def cyclicNegativeCount (q : Word) : ℕ :=
  (∑ y ∈ negativeValidCodes q false false,
      codeMultiplicity q false false y) +
  (∑ y ∈ negativeValidCodes q true true,
      codeMultiplicity q true true y)

theorem boundary_length_le {q y : Word} {b : Bool} (h : Boundary q b y) :
    y.length ≤ q.length + 1 := by
  rcases h with ⟨u, hu, _, rfl⟩
  simpa using Nat.add_le_add_right hu.length_le 1

theorem negativeValidCodes_zero_start (v : Word) :
    negativeValidCodes (true :: false :: v) false false =
      (boundaryFinset (false :: v) true).filter fun y => ones y < zeros y := by
  classical
  ext y
  simp only [mem_negativeValidCodes, Finset.mem_filter, mem_boundaryFinset]
  rw [validCode_zero_start]

theorem negativeValidCodes_one_start (v : Word) :
    negativeValidCodes (true :: false :: v) true true =
      (boundaryFinset v false).filter fun y => ones y < zeros y := by
  classical
  ext y
  simp only [mem_negativeValidCodes, Finset.mem_filter, mem_boundaryFinset]
  rw [validCode_one_start]

theorem cyclicNegativeCount_special (v : Word) :
    cyclicNegativeCount (true :: false :: v) =
      (∑ y ∈ (boundaryFinset (false :: v) true).filter (fun y => ones y < zeros y),
        2 ^ ((v.length + 2) - y.length)) +
      (∑ y ∈ (boundaryFinset v false).filter (fun y => ones y < zeros y),
        2 ^ ((v.length + 2) - y.length)) := by
  rw [cyclicNegativeCount, negativeValidCodes_zero_start,
    negativeValidCodes_one_start]
  apply congrArg₂ (.+.)
  · apply Finset.sum_congr rfl
    intro y hy
    apply codeMultiplicity_of_valid
    exact (validCode_zero_start v y).mpr (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
  · apply Finset.sum_congr rfl
    intro y hy
    apply codeMultiplicity_of_valid
    exact (validCode_one_start v y).mpr (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)

theorem phiNeg_Benum (q : Word) (b : Bool) :
    phiNeg (Benum q b) =
      ∑ y ∈ (boundaryFinset q b).filter (fun y => ones y < zeros y),
        1 / (2 : ℚ) ^ y.length := by
  rw [Benum, phiNeg_enumerator, ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  rw [zeros_add_ones]

theorem cast_pow_sub_div_pow (k m : ℕ) (hm : m ≤ k) :
    (2 : ℚ) ^ (k - m) / (2 : ℚ) ^ k = 1 / (2 : ℚ) ^ m := by
  rw [show k = (k - m) + m by omega, pow_add]
  field_simp
  congr 1
  omega

/-- Exact normalized first-exit formula for a target already rotated to
`10v`. -/
theorem cyclicNegativeCount_special_normalized (v : Word) :
    (cyclicNegativeCount (true :: false :: v) : ℚ) /
        (2 : ℚ) ^ (v.length + 2) = phiNeg (Cenum v) := by
  rw [cyclicNegativeCount_special, Cenum, phiNeg_add, phiNeg_Benum,
    phiNeg_Benum]
  push_cast
  rw [add_div]
  congr 1
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y hy
    apply cast_pow_sub_div_pow
    have hlen := boundary_length_le (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
    simp only [List.length_cons] at hlen ⊢
    omega
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y hy
    apply cast_pow_sub_div_pow
    have hlen := boundary_length_le (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
    omega

theorem cyclicNegativeCount_special_bound (v : Word) :
    cyclicNegativeCount (true :: false :: v) ≤ 2 ^ (v.length + 1) := by
  have hphi := cross_boundary_halfplane_bound v
  have hnorm := cyclicNegativeCount_special_normalized v
  rw [← hnorm] at hphi
  have hpow : (0 : ℚ) < (2 : ℚ) ^ (v.length + 2) := by positivity
  have hq : (cyclicNegativeCount (true :: false :: v) : ℚ) ≤
      (2 : ℚ) ^ (v.length + 1) := by
    rw [div_le_iff₀ hpow] at hphi
    rw [show v.length + 2 = (v.length + 1) + 1 by omega, pow_succ] at hphi
    norm_num at hphi ⊢
    linarith
  exact_mod_cast hq

/-! ## Executable carry traces -/

structure CarryRun where
  output : Word
  code : Word
  carry : Bool
deriving DecidableEq

/-- Deterministic bitwise addition trace.  The input is assumed to have the
same length as the target; the short-input branch is irrelevant on
`wordsExact`. -/
def carryRun : Word → Bool → Word → CarryRun
  | [], c, _ => ⟨[], [], c⟩
  | _ :: _, c, [] => ⟨[], [], c⟩
  | t :: q, c, a :: A =>
      if c = t then
        let r := carryRun q c A
        ⟨a :: r.output, r.code, r.carry⟩
      else
        let r := carryRun q a A
        ⟨(!a) :: r.output, (!a) :: r.code, r.carry⟩

/-- All binary words of exactly length `n`. -/
def wordsExact : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 =>
      (wordsExact n).image (fun w => false :: w) ∪
        (wordsExact n).image (fun w => true :: w)

theorem mem_wordsExact {n : ℕ} {w : Word} : w ∈ wordsExact n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsExact, List.length_eq_zero_iff]
  | succ n ih =>
      cases w with
      | nil => simp [wordsExact]
      | cons b w => cases b <;> simp [wordsExact, ih]

noncomputable def codeFiber (q : Word) (c cf : Bool) (y : Word) : Finset Word :=
  (wordsExact q.length).filter fun A =>
    (carryRun q c A).code = y ∧ (carryRun q c A).carry = cf

theorem mem_codeFiber {q A y : Word} {c cf : Bool} :
    A ∈ codeFiber q c cf y ↔
      A.length = q.length ∧ (carryRun q c A).code = y ∧
        (carryRun q c A).carry = cf := by
  classical
  simp [codeFiber, mem_wordsExact]

private theorem cons_false_ne_cons_true (S T : Finset Word) :
    Disjoint (S.image fun w => false :: w) (T.image fun w => true :: w) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw₀ hw₁
  rcases Finset.mem_image.mp hw₀ with ⟨u, _, rfl⟩
  simp at hw₁

theorem codeFiber_inactive (q : Word) (t cf : Bool) (y : Word) :
    codeFiber (t :: q) t cf y =
      (codeFiber q t cf y).image (fun A => false :: A) ∪
        (codeFiber q t cf y).image (fun A => true :: A) := by
  classical
  ext A
  cases A with
  | nil => simp [mem_codeFiber]
  | cons a A =>
      cases a <;> simp [mem_codeFiber, carryRun]

theorem codeFiber_active_nil (q : Word) (t c cf : Bool) (hct : c ≠ t) :
    codeFiber (t :: q) c cf [] = ∅ := by
  classical
  ext A
  cases A with
  | nil => simp [mem_codeFiber]
  | cons a A => cases a <;> cases c <;> cases t <;> simp_all [mem_codeFiber, carryRun]

theorem codeFiber_active_cons (q : Word) (t c cf x : Bool) (xs : Word)
    (hct : c ≠ t) :
    codeFiber (t :: q) c cf (x :: xs) =
      (codeFiber q (!x) cf xs).image (fun A => (!x) :: A) := by
  classical
  ext A
  cases A with
  | nil => simp [mem_codeFiber]
  | cons a A =>
      cases a <;> cases x <;> cases c <;> cases t <;>
        simp_all [mem_codeFiber, carryRun]

theorem card_codeFiber (q y : Word) (c cf : Bool) :
    (codeFiber q c cf y).card = codeMultiplicity q c cf y := by
  induction q generalizing c y with
  | nil =>
      cases y <;> cases c <;> cases cf <;> simp [codeFiber, codeMultiplicity,
        wordsExact, carryRun]
  | cons t q ih =>
      by_cases hct : c = t
      · subst c
        rw [codeFiber_inactive, Finset.card_union_of_disjoint
          (cons_false_ne_cons_true _ _)]
        rw [Finset.card_image_of_injective _ List.cons_injective,
          Finset.card_image_of_injective _ List.cons_injective]
        rw [ih]
        cases y <;> rw [codeMultiplicity]
        all_goals simp
        all_goals omega
      · cases y with
        | nil =>
            rw [codeFiber_active_nil q t c cf hct]
            simp [codeMultiplicity, hct]
        | cons x xs =>
            rw [codeFiber_active_cons q t c cf x xs hct]
            rw [Finset.card_image_of_injective _ List.cons_injective, ih]
            rw [codeMultiplicity]
            simp [hct]

noncomputable def cyclicInputs (q : Word) (c : Bool) : Finset Word :=
  (wordsExact q.length).filter fun A =>
    (carryRun q c A).carry = c ∧
      ones (carryRun q c A).code < zeros (carryRun q c A).code

noncomputable def cyclicInputCount (q : Word) : ℕ :=
  (cyclicInputs q false).card + (cyclicInputs q true).card

theorem carryRun_code_valid {q A : Word} {c : Bool} (hA : A.length = q.length) :
    ValidCode q c (carryRun q c A).carry (carryRun q c A).code := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hA)
      subst A
      simp [carryRun, ValidCode]
  | cons t q ih =>
      cases A with
      | nil => simp at hA
      | cons a A =>
          have hlen : A.length = q.length := by simpa using hA
          by_cases hct : c = t
          · simp only [carryRun, hct, if_true, ValidCode]
            exact ih hlen
          · simp only [carryRun, hct, if_false, ValidCode]
            simpa using (ih (c := a) hlen)

private theorem cyclicInputs_fiber (q : Word) (c : Bool)
    (y : Word) (hy : y ∈ negativeValidCodes q c c) :
    (cyclicInputs q c).filter (fun A => (carryRun q c A).code = y) =
      codeFiber q c c y := by
  classical
  ext A
  rcases mem_negativeValidCodes.mp hy with ⟨_, hyneg⟩
  simp only [Finset.mem_filter, cyclicInputs, mem_wordsExact, mem_codeFiber]
  constructor
  · rintro ⟨⟨hA, hcarry, hneg⟩, hcode⟩
    exact ⟨hA, hcode, hcarry⟩
  · rintro ⟨hA, hcode, hcarry⟩
    exact ⟨⟨hA, hcarry, hcode ▸ hyneg⟩, hcode⟩

theorem card_cyclicInputs (q : Word) (c : Bool) :
    (cyclicInputs q c).card =
      ∑ y ∈ negativeValidCodes q c c, codeMultiplicity q c c y := by
  classical
  have hmap : ∀ A ∈ cyclicInputs q c,
      (carryRun q c A).code ∈ negativeValidCodes q c c := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hAlen, hcarry, hneg⟩
    have hlen := mem_wordsExact.mp hAlen
    have hv := carryRun_code_valid (c := c) hlen
    rw [hcarry] at hv
    exact mem_negativeValidCodes.mpr ⟨hv, hneg⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap (fun _A => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_one, Nat.cast_id] at hfiber
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro y hy
  rw [cyclicInputs_fiber q c y hy, card_codeFiber]

theorem cyclicInputCount_eq (q : Word) : cyclicInputCount q = cyclicNegativeCount q := by
  rw [cyclicInputCount, cyclicNegativeCount, card_cyclicInputs, card_cyclicInputs]

/-! ## Cyclic rotation -/

theorem carryRun_append (q₁ q₂ A₁ A₂ : Word) (c : Bool)
    (hlen : A₁.length = q₁.length) :
    carryRun (q₁ ++ q₂) c (A₁ ++ A₂) =
      let r₁ := carryRun q₁ c A₁
      let r₂ := carryRun q₂ r₁.carry A₂
      ⟨r₁.output ++ r₂.output, r₁.code ++ r₂.code, r₂.carry⟩ := by
  induction q₁ generalizing c A₁ with
  | nil =>
      have : A₁ = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A₁
      simp [carryRun]
  | cons t q ih =>
      cases A₁ with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t
          · simp only [List.cons_append, carryRun, hct, if_true]
            rw [ih (c := t) (A₁ := A) htail]
          · simp only [List.cons_append, carryRun, hct, if_false]
            rw [ih (c := a) (A₁ := A) htail]

def stepCarry (t c a : Bool) : Bool := if c = t then c else a

theorem carryRun_cons (t : Bool) (q : Word) (c a : Bool) (A : Word) :
    carryRun (t :: q) c (a :: A) =
      let r := carryRun q (stepCarry t c a) A
      if c = t then ⟨a :: r.output, r.code, r.carry⟩
      else ⟨(!a) :: r.output, (!a) :: r.code, r.carry⟩ := by
  by_cases h : c = t <;> simp [carryRun, stepCarry, h]

noncomputable def cyclicPairs (q : Word) : Finset ((c : Bool) × Word) :=
  Finset.univ.sigma fun c => cyclicInputs q c

theorem card_cyclicPairs (q : Word) : (cyclicPairs q).card = cyclicInputCount q := by
  rw [cyclicPairs, Finset.card_sigma, cyclicInputCount]
  simp
  omega

theorem mem_cyclicPairs {q : Word} {p : (c : Bool) × Word} :
    p ∈ cyclicPairs q ↔ p.2 ∈ cyclicInputs q p.1 := by
  classical
  simp [cyclicPairs]

def rotatePair (t : Bool) : ((c : Bool) × Word) → ((c : Bool) × Word)
  | ⟨c, []⟩ => ⟨c, []⟩
  | ⟨c, a :: A⟩ => ⟨stepCarry t c a, A ++ [a]⟩

theorem carryRun_rotate_closed {t c a : Bool} {q A : Word}
    (hlen : A.length = q.length)
    (hclosed : (carryRun (t :: q) c (a :: A)).carry = c) :
    let c₁ := stepCarry t c a
    let r := carryRun (q ++ [t]) c₁ (A ++ [a])
    r.carry = c₁ ∧
      ones r.code = ones (carryRun (t :: q) c (a :: A)).code ∧
      zeros r.code = zeros (carryRun (t :: q) c (a :: A)).code := by
  dsimp only
  rw [carryRun_append q [t] A [a] (stepCarry t c a) hlen]
  by_cases hct : c = t
  · subst c
    simp only [carryRun, stepCarry] at hclosed ⊢
    simp only [if_true] at hclosed ⊢
    rw [hclosed]
    simp [ones, zeros, List.count_append]
  · simp only [carryRun_cons, stepCarry, hct, if_false] at hclosed ⊢
    have htail : (carryRun q a A).carry = c := hclosed
    rw [htail]
    simp [carryRun, hct, zeros, ones, List.count_append, List.count_cons]

theorem rotatePair_mem {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (t :: q)) : rotatePair t p ∈ cyclicPairs (q ++ [t]) := by
  classical
  rcases p with ⟨c, A⟩
  rw [mem_cyclicPairs] at hp ⊢
  change A ∈ cyclicInputs (t :: q) c at hp
  rcases Finset.mem_filter.mp hp with ⟨hA, hclosed, hneg⟩
  have hlenfull := mem_wordsExact.mp hA
  cases A with
  | nil => simp at hlenfull
  | cons a A =>
      change A ++ [a] ∈ cyclicInputs (q ++ [t]) (stepCarry t c a)
      have hlen : A.length = q.length := by simpa using hlenfull
      rcases carryRun_rotate_closed hlen hclosed with ⟨hclosed', hone, hzero⟩
      apply Finset.mem_filter.mpr
      refine ⟨mem_wordsExact.mpr (by simp [hlen]), hclosed', ?_⟩
      simpa [hone, hzero] using hneg

def unrotatePair (q : Word) : ((c : Bool) × Word) → ((c : Bool) × Word)
  | ⟨c₁, R⟩ =>
      if h : R = [] then ⟨c₁, []⟩
      else
        let a := R.getLast h
        let A := R.dropLast
        let c := (carryRun q c₁ A).carry
        ⟨c, a :: A⟩

theorem unrotate_rotate {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (t :: q)) : unrotatePair q (rotatePair t p) = p := by
  classical
  rcases p with ⟨c, R⟩
  rw [mem_cyclicPairs] at hp
  change R ∈ cyclicInputs (t :: q) c at hp
  rcases Finset.mem_filter.mp hp with ⟨hR, hclosed, hneg⟩
  have hlenfull := mem_wordsExact.mp hR
  cases R with
  | nil => simp at hlenfull
  | cons a A =>
      have hlen : A.length = q.length := by simpa using hlenfull
      by_cases hct : c = t
      · subst c
        have htail : (carryRun q t A).carry = t := by
          simpa [carryRun_cons, stepCarry] using hclosed
        simp [rotatePair, unrotatePair, stepCarry, htail]
      · have htail : (carryRun q a A).carry = c := by
          simpa [carryRun_cons, stepCarry, hct] using hclosed
        simp [rotatePair, unrotatePair, stepCarry, hct, htail]

theorem unrotatePair_mem_and_rotate {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (q ++ [t])) :
    unrotatePair q p ∈ cyclicPairs (t :: q) ∧
      rotatePair t (unrotatePair q p) = p := by
  classical
  rcases p with ⟨c₁, R⟩
  rw [mem_cyclicPairs] at hp ⊢
  change R ∈ cyclicInputs (q ++ [t]) c₁ at hp
  rcases Finset.mem_filter.mp hp with ⟨hR, hclosed, hneg⟩
  have hlenfull := mem_wordsExact.mp hR
  have hRne : R ≠ [] := by
    intro h
    subst R
    simp at hlenfull
  let a := R.getLast hRne
  let A := R.dropLast
  have hdecomp : A ++ [a] = R := by
    exact List.dropLast_append_getLast hRne
  have hlen : A.length = q.length := by
    have := congrArg List.length hdecomp
    simp only [List.length_append, List.length_singleton] at this
    simp only [List.length_append, List.length_singleton] at hlenfull
    omega
  let c := (carryRun q c₁ A).carry
  have happ := carryRun_append q [t] A [a] c₁ hlen
  dsimp only at happ
  have hlast : (carryRun [t] c [a]).carry = c₁ := by
    have hc := congrArg CarryRun.carry happ
    rw [hdecomp, hclosed] at hc
    simpa [c] using hc.symm
  have hstep : stepCarry t c a = c₁ := by
    by_cases hct : c = t <;> simp [carryRun, stepCarry, hct] at hlast ⊢
    all_goals exact hlast
  have horig_closed : (carryRun (t :: q) c (a :: A)).carry = c := by
    rw [carryRun_cons]
    simp only [hstep]
    split <;> rfl
  have hrot := carryRun_rotate_closed hlen horig_closed
  dsimp only at hrot
  rw [hstep, hdecomp] at hrot
  rcases hrot with ⟨_, hone, hzero⟩
  constructor
  · simp only [unrotatePair, dif_neg hRne]
    change a :: A ∈ cyclicInputs (t :: q) c
    apply Finset.mem_filter.mpr
    refine ⟨mem_wordsExact.mpr (by simp [hlen]), horig_closed, ?_⟩
    omega
  · simp [unrotatePair, hRne, rotatePair, hstep, hdecomp, a, A, c]

theorem unrotatePair_mem {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (q ++ [t])) : unrotatePair q p ∈ cyclicPairs (t :: q) :=
  (unrotatePair_mem_and_rotate hp).1

theorem rotate_unrotate {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (q ++ [t])) : rotatePair t (unrotatePair q p) = p :=
  (unrotatePair_mem_and_rotate hp).2

theorem cyclicInputCount_rotate (t : Bool) (q : Word) :
    cyclicInputCount (t :: q) = cyclicInputCount (q ++ [t]) := by
  rw [← card_cyclicPairs, ← card_cyclicPairs]
  apply Finset.card_bij (fun p _ => rotatePair t p)
  · exact fun p hp => rotatePair_mem hp
  · intro p₁ hp₁ p₂ hp₂ heq
    have h₁ := unrotate_rotate hp₁
    have h₂ := unrotate_rotate hp₂
    rw [← h₁, ← h₂, heq]
  · intro p hp
    exact ⟨unrotatePair q p, unrotatePair_mem hp, rotate_unrotate hp⟩

theorem cyclicInputCount_append_comm (a b : Word) :
    cyclicInputCount (a ++ b) = cyclicInputCount (b ++ a) := by
  induction a generalizing b with
  | nil => simp
  | cons t a ih =>
      calc
        cyclicInputCount ((t :: a) ++ b) =
            cyclicInputCount ((a ++ b) ++ [t]) := by
              simpa only [List.cons_append] using cyclicInputCount_rotate t (a ++ b)
        _ = cyclicInputCount ((b ++ [t]) ++ a) := by
              simpa only [List.append_assoc] using ih (b ++ [t])
        _ = cyclicInputCount (b ++ t :: a) := by
              simp only [List.append_assoc, List.singleton_append]

private theorem exists_true_false_after_start (r : Word) (hfalse : false ∈ r) :
    ∃ a b, true :: r = a ++ true :: false :: b := by
  induction r with
  | nil => simp at hfalse
  | cons x r ih =>
      cases x
      · exact ⟨[], r, rfl⟩
      · have htail : false ∈ r := by simpa using hfalse
        obtain ⟨a, b, hab⟩ := ih htail
        exact ⟨true :: a, b, by simpa using congrArg (List.cons true) hab⟩

theorem exists_special_rotation (q : Word) (htrue : true ∈ q)
    (hfalse : false ∈ q) :
    ∃ v, cyclicInputCount q = cyclicInputCount (true :: false :: v) ∧
      q.length = v.length + 2 := by
  obtain ⟨l₁, l₂, hq⟩ := List.mem_iff_append.mp htrue
  have hfalse' : false ∈ l₂ ++ l₁ := by
    rw [hq] at hfalse
    simpa only [List.mem_append, List.mem_cons, Bool.false_eq_true, false_or, or_comm]
      using hfalse
  obtain ⟨a, b, hab⟩ := exists_true_false_after_start (l₂ ++ l₁) hfalse'
  have hrot₁ : cyclicInputCount q = cyclicInputCount (true :: (l₂ ++ l₁)) := by
    rw [hq]
    simpa only [List.cons_append, List.append_assoc] using
      cyclicInputCount_append_comm l₁ (true :: l₂)
  have hrot₂ : cyclicInputCount (true :: (l₂ ++ l₁)) =
      cyclicInputCount (true :: false :: (b ++ a)) := by
    rw [hab]
    simpa only [List.cons_append, List.append_assoc] using
      cyclicInputCount_append_comm a (true :: false :: b)
  refine ⟨b ++ a, hrot₁.trans hrot₂, ?_⟩
  have hlen := congrArg List.length hq
  have hlen' := congrArg List.length hab
  simp only [List.length_append, List.length_cons] at hlen hlen' ⊢
  omega

theorem cyclicInputCount_bound_of_nonconstant (q : Word)
    (htrue : true ∈ q) (hfalse : false ∈ q) :
    cyclicInputCount q ≤ 2 ^ (q.length - 1) := by
  obtain ⟨v, hcount, hlen⟩ := exists_special_rotation q htrue hfalse
  rw [hcount, cyclicInputCount_eq, hlen]
  rw [show v.length + 2 - 1 = v.length + 1 by omega]
  exact cyclicNegativeCount_special_bound v

end TuDeng.FirstExit
