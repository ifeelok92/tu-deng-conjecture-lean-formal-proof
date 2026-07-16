import TuDengFormal.FirstExitCarry
import TuDengFormal.TuDengDefinitions

set_option linter.style.header false

/-!
# Bridge to the original natural-number Tu--Deng count

This module connects the word/carry theorem to `tuDengCount`.  Binary words
are little-endian, matching `Nat.testBit` and the carry scan.
-/

namespace TuDeng.FirstExit

open scoped BigOperators

/-- Natural value of a little-endian binary word. -/
def wordValue : Word → ℕ
  | [] => 0
  | b :: w => Nat.bit b (wordValue w)

/-- The low `k` bits of `n`, least significant bit first. -/
def bitsWord : ℕ → ℕ → Word
  | 0, _ => []
  | k + 1, n => n.testBit 0 :: bitsWord k (n >>> 1)

@[simp] theorem length_bitsWord (k n : ℕ) : (bitsWord k n).length = k := by
  induction k generalizing n <;> simp [bitsWord, *]

theorem wordValue_lt_pow (w : Word) : wordValue w < 2 ^ w.length := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
      cases b <;> simp [wordValue, Nat.bit_false, Nat.bit_true, pow_succ] <;> omega

theorem wordValue_bitsWord {k n : ℕ} (hn : n < 2 ^ k) :
    wordValue (bitsWord k n) = n := by
  induction k generalizing n with
  | zero =>
      have : n = 0 := by simpa using hn
      subst n
      rfl
  | succ k ih =>
      have hshift : n >>> 1 < 2 ^ k := by
        rw [Nat.shiftRight_eq_div_pow]
        simp only [pow_one]
        omega
      simp only [bitsWord, wordValue]
      rw [ih hshift]
      exact Nat.bit_testBit_zero_shiftRight_one n

theorem bitsWord_wordValue (w : Word) : bitsWord w.length (wordValue w) = w := by
  induction w with
  | nil => simp [bitsWord, wordValue]
  | cons b w ih =>
      simp [bitsWord, wordValue, Nat.testBit_bit_zero, Nat.bit_shiftRight_one, ih]

theorem bitsWord_injective_on {k m n : ℕ} (hm : m < 2 ^ k) (hn : n < 2 ^ k)
    (h : bitsWord k m = bitsWord k n) : m = n := by
  rw [← wordValue_bitsWord hm, ← wordValue_bitsWord hn, h]

theorem hammingWeight_succ (k n : ℕ) :
    TuDeng.hammingWeight (k + 1) n =
      (if n.testBit 0 then 1 else 0) + TuDeng.hammingWeight k (n >>> 1) := by
  simp only [TuDeng.hammingWeight, List.range_succ_eq_map, List.map_cons,
    List.map_map, List.sum_cons]
  apply congrArg₂ (.+.) rfl
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  change (if n.testBit (Nat.succ i) then 1 else 0) =
    if (n >>> 1).testBit i then 1 else 0
  rw [Nat.testBit_succ, Nat.shiftRight_eq_div_pow]

theorem ones_bitsWord_eq_hammingWeight (k n : ℕ) :
    ones (bitsWord k n) = TuDeng.hammingWeight k n := by
  induction k generalizing n with
  | zero => simp [bitsWord, ones, TuDeng.hammingWeight]
  | succ k ih =>
      rw [bitsWord, hammingWeight_succ]
      simp only [ones, List.count_cons]
      rw [show List.count true (bitsWord k (n >>> 1)) =
        TuDeng.hammingWeight k (n >>> 1) by exact ih _]
      cases hbit : n.testBit 0 <;> simp [hbit] <;> omega

theorem wordValue_not_add_one (w : Word) :
    wordValue (w.map (!·)) + wordValue w + 1 = 2 ^ w.length := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
      cases b <;>
        simp [wordValue, Nat.bit_false, Nat.bit_true, pow_succ] <;> omega

theorem wordValue_not_add (w : Word) :
    wordValue (w.map (!·)) + wordValue w = 2 ^ w.length - 1 := by
  have h := wordValue_not_add_one w
  have hp : 0 < 2 ^ w.length := by positivity
  omega

theorem wordValue_not (w : Word) :
    wordValue (w.map (!·)) = 2 ^ w.length - 1 - wordValue w := by
  have h := wordValue_not_add w
  omega

theorem ones_map_not (w : Word) : ones (w.map (!·)) = zeros w := by
  induction w with
  | nil => simp [ones, zeros]
  | cons b w ih => cases b <;> simpa [ones, zeros] using ih

@[simp] theorem carryRun_output_length {q A : Word} {c : Bool}
    (hlen : A.length = q.length) : (carryRun q c A).output.length = q.length := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A
      simp [carryRun]
  | cons t q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t <;> simp [carryRun, hct, ih htail]

theorem carryRun_numeric {q A : Word} {c : Bool} (hlen : A.length = q.length) :
    wordValue (carryRun q c A).output +
        2 ^ q.length * (carryRun q c A).carry.toNat =
      wordValue A + wordValue q + c.toNat := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A
      cases c <;> simp [carryRun, wordValue]
  | cons t q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t
          · subst c
            have hrec := ih (c := t) htail
            cases t <;> cases a <;>
              simp [carryRun, wordValue, Nat.bit_false, Nat.bit_true, pow_succ] at hrec ⊢ <;>
              nlinarith
          · have hrec := ih (c := a) htail
            cases t <;> cases c
            all_goals try {simp at hct}
            all_goals cases a <;>
              simp [carryRun, wordValue, Nat.bit_false, Nat.bit_true, pow_succ] at hrec ⊢ <;>
              nlinarith

theorem carryRun_weight {q A : Word} {c : Bool} (hlen : A.length = q.length) :
    ones (carryRun q c A).output + zeros (carryRun q c A).code =
      ones A + ones (carryRun q c A).code := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A
      simp [carryRun, ones, zeros]
  | cons t q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t
          · have hrec := ih (c := c) htail
            cases a <;> simp [carryRun, hct, ones, zeros] at hrec ⊢ <;> omega
          · have hrec := ih (c := a) htail
            cases a <;> simp [carryRun, hct, ones, zeros] at hrec ⊢ <;> omega

theorem carryRun_negative_iff {q A : Word} {c : Bool} (hlen : A.length = q.length) :
    ones (carryRun q c A).code < zeros (carryRun q c A).code ↔
      ones (carryRun q c A).output < ones A := by
  have h := carryRun_weight (c := c) hlen
  omega

theorem wordValue_eq_zero_of_not_true {w : Word} (h : true ∉ w) : wordValue w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hb : b = false := by cases b <;> simp_all
      subst b
      simp [wordValue, ih (by simp_all)]

theorem wordValue_eq_all_ones_of_not_false {w : Word} (h : false ∉ w) :
    wordValue w = 2 ^ w.length - 1 := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
      have hb : b = true := by cases b <;> simp_all
      subst b
      have htail : false ∉ w := by simp_all
      rw [wordValue, ih htail]
      simp only [Nat.bit_true, List.length_cons, pow_succ]
      have hp : 0 < 2 ^ w.length := by positivity
      omega

theorem bitsWord_mem_true {k n : ℕ} (hn0 : 0 < n) (hn : n < 2 ^ k) :
    true ∈ bitsWord k n := by
  by_contra h
  have hv := wordValue_eq_zero_of_not_true h
  rw [wordValue_bitsWord hn] at hv
  omega

theorem bitsWord_mem_false {k n : ℕ} (hn : n < 2 ^ k - 1) :
    false ∈ bitsWord k n := by
  by_contra h
  have hv := wordValue_eq_all_ones_of_not_false h
  rw [wordValue_bitsWord (lt_trans hn (by omega))] at hv
  rw [length_bitsWord] at hv
  omega

theorem bitsWord_modulus_sub (k x : ℕ) (hx : x ≤ 2 ^ k - 1) :
    bitsWord k x = (bitsWord k (2 ^ k - 1 - x)).map (!·) := by
  let A := bitsWord k (2 ^ k - 1 - x)
  have hAval : wordValue A = 2 ^ k - 1 - x := by
    apply wordValue_bitsWord
    have hp : 0 < 2 ^ k := by positivity
    omega
  have hlen : A.length = k := length_bitsWord _ _
  have hnotval : wordValue (A.map (!·)) = x := by
    rw [wordValue_not, hlen, hAval]
    omega
  calc
    bitsWord k x = bitsWord (A.map (!·)).length (wordValue (A.map (!·))) := by
      rw [List.length_map, hlen, hnotval]
    _ = A.map (!·) := bitsWord_wordValue _

def chosenCarry (k A t : ℕ) : Bool := decide (2 ^ k - 1 ≤ A + t)

theorem chosenCarry_run {k A t : ℕ} (hk : 0 < k)
    (hA : A ≤ 2 ^ k - 1) (ht : t < 2 ^ k - 1) :
    let c := chosenCarry k A t
    let r := carryRun (bitsWord k t) c (bitsWord k A)
    r.carry = c ∧ wordValue r.output = (A + t) % (2 ^ k - 1) := by
  dsimp only
  let N := 2 ^ k - 1
  let c := chosenCarry k A t
  let r := carryRun (bitsWord k t) c (bitsWord k A)
  change r.carry = c ∧ wordValue r.output = (A + t) % N
  have hpow : 0 < 2 ^ k := by positivity
  have hN : 0 < N := by dsimp [N]; omega
  have hPN : 2 ^ k = N + 1 := by dsimp [N]; omega
  have htpow : t < 2 ^ k := by omega
  have hApow : A < 2 ^ k := by omega
  have hnum := carryRun_numeric (q := bitsWord k t) (A := bitsWord k A) (c := c)
    (by simp)
  rw [wordValue_bitsWord hApow, wordValue_bitsWord htpow, length_bitsWord] at hnum
  change wordValue r.output + 2 ^ k * r.carry.toNat = A + t + c.toNat at hnum
  have hout : wordValue r.output < 2 ^ k := by
    have hlenout : r.output.length = k := by
      simpa [r] using carryRun_output_length
        (q := bitsWord k t) (A := bitsWord k A) (c := c) (by simp)
    simpa [hlenout] using wordValue_lt_pow r.output
  by_cases hs : N ≤ A + t
  · have hc : c = true := by simp [c, chosenCarry, N, hs]
    have hsum : A + t < 2 * N := by omega
    have hcarry : r.carry = true := by
      by_contra h
      have : r.carry = false := Bool.eq_false_of_not_eq_true h
      rw [hc, this] at hnum
      norm_num at hnum
      change 2 ^ k - 1 ≤ A + t at hs
      omega
    refine ⟨hcarry.trans hc.symm, ?_⟩
    have houtval : wordValue r.output = A + t - N := by
      rw [hc, hcarry] at hnum
      norm_num at hnum
      dsimp [N]
      omega
    rw [houtval, Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
  · have hc : c = false := by simp [c, chosenCarry, N, hs]
    have hsum : A + t < N := by omega
    have hcarry : r.carry = false := by
      by_contra h
      have : r.carry = true := Bool.eq_true_of_not_eq_false h
      rw [hc, this] at hnum
      norm_num at hnum
      change A + t < 2 ^ k - 1 at hsum
      omega
    refine ⟨hcarry.trans hc.symm, ?_⟩
    have houtval : wordValue r.output = A + t := by
      rw [hc, hcarry] at hnum
      norm_num at hnum
      exact hnum
    rw [houtval, Nat.mod_eq_of_lt hsum]

theorem hamming_modulus_sub_add_ones (k x : ℕ) (hx : x ≤ 2 ^ k - 1) :
    TuDeng.hammingWeight k x + ones (bitsWord k (2 ^ k - 1 - x)) = k := by
  rw [← ones_bitsWord_eq_hammingWeight, bitsWord_modulus_sub k x hx,
    ones_map_not]
  have hcount := zeros_add_ones (bitsWord k (2 ^ k - 1 - x))
  rw [length_bitsWord] at hcount
  omega

theorem hamming_eq_ones_of_value {k n : ℕ} {w : Word}
    (hlen : w.length = k) (hval : wordValue w = n) :
    TuDeng.hammingWeight k n = ones w := by
  rw [← ones_bitsWord_eq_hammingWeight]
  calc
    ones (bitsWord k n) = ones (bitsWord w.length (wordValue w)) := by rw [hlen, hval]
    _ = ones w := by rw [bitsWord_wordValue]

noncomputable def tdFinset (k t : ℕ) : Finset ℕ :=
  (Finset.range (TuDeng.modulus k)).filter fun x =>
    TuDeng.hammingWeight k x + TuDeng.hammingWeight k (TuDeng.partner k t x) ≤ k - 1

theorem tuDengCount_eq_card (k t : ℕ) :
    TuDeng.tuDengCount k t = (tdFinset k t).card := by
  have hnodup :
      ((List.range (TuDeng.modulus k)).filter (fun x =>
        TuDeng.hammingWeight k x +
          TuDeng.hammingWeight k (TuDeng.partner k t x) ≤ k - 1)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hcard := List.toFinset_card_of_nodup hnodup
  rw [List.toFinset_filter, List.toFinset_range] at hcard
  simpa [TuDeng.tuDengCount, tdFinset] using hcard.symm

def originalToPair (k t x : ℕ) : ((c : Bool) × Word) :=
  let N := 2 ^ k - 1
  let A := N - x
  ⟨chosenCarry k A t, bitsWord k A⟩

theorem partner_eq_A_mod {k t x : ℕ} (hx : x ≤ 2 ^ k - 1) :
    TuDeng.partner k t x = (2 ^ k - 1 - x + t) % (2 ^ k - 1) := by
  unfold TuDeng.partner TuDeng.modulus
  congr 1
  omega

theorem originalToPair_mem {k t x : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) (hx : x ∈ tdFinset k t) :
    originalToPair k t x ∈ cyclicPairs (bitsWord k t) := by
  classical
  rcases Finset.mem_filter.mp hx with ⟨hxrange, hxweight⟩
  have hxlt : x < 2 ^ k - 1 := by simpa [TuDeng.modulus] using Finset.mem_range.mp hxrange
  let N := 2 ^ k - 1
  let A := N - x
  let c := chosenCarry k A t
  let r := carryRun (bitsWord k t) c (bitsWord k A)
  have hA : A ≤ 2 ^ k - 1 := by dsimp [A, N]; omega
  have hrun := chosenCarry_run hk hA ht
  dsimp only at hrun
  change r.carry = c ∧ wordValue r.output = (A + t) % N at hrun
  rcases hrun with ⟨hclosed, houtval⟩
  have hpartner : TuDeng.partner k t x = (A + t) % N := by
    simpa [A, N, add_comm] using partner_eq_A_mod (k := k) (t := t) (le_of_lt hxlt)
  have houtweight : ones r.output = TuDeng.hammingWeight k (TuDeng.partner k t x) := by
    symm
    apply hamming_eq_ones_of_value (w := r.output)
    · simpa [r] using carryRun_output_length
        (q := bitsWord k t) (A := bitsWord k A) (c := c) (by simp)
    · rw [houtval, hpartner]
  have hcomp := hamming_modulus_sub_add_ones k x (le_of_lt hxlt)
  change TuDeng.hammingWeight k x + ones (bitsWord k A) = k at hcomp
  have hnegOut : ones r.output < ones (bitsWord k A) := by
    rw [houtweight]
    omega
  rw [mem_cyclicPairs]
  change bitsWord k A ∈ cyclicInputs (bitsWord k t) c
  apply Finset.mem_filter.mpr
  refine ⟨mem_wordsExact.mpr (by simp), hclosed, ?_⟩
  exact (carryRun_negative_iff (q := bitsWord k t) (A := bitsWord k A) (c := c)
    (by simp)).mpr hnegOut

def pairToOriginal (k : ℕ) (p : ((c : Bool) × Word)) : ℕ :=
  2 ^ k - 1 - wordValue p.2

theorem hammingWeight_modulus (k : ℕ) :
    TuDeng.hammingWeight k (2 ^ k - 1) = k := by
  have h := hamming_modulus_sub_add_ones k 0 (Nat.zero_le _)
  rw [show 2 ^ k - 1 - 0 = 2 ^ k - 1 by omega,
    ones_bitsWord_eq_hammingWeight] at h
  have hz : TuDeng.hammingWeight k 0 = 0 := by
    simp [TuDeng.hammingWeight]
  rw [hz, Nat.zero_add] at h
  exact h

theorem pairToOriginal_mem_and_inverse {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) {p : ((c : Bool) × Word)}
    (hp : p ∈ cyclicPairs (bitsWord k t)) :
    pairToOriginal k p ∈ tdFinset k t ∧
      originalToPair k t (pairToOriginal k p) = p := by
  classical
  rcases p with ⟨c, W⟩
  rw [mem_cyclicPairs] at hp
  rcases Finset.mem_filter.mp hp with ⟨hWset, hclosed, hneg⟩
  have hWlen : W.length = k := by
    simpa using mem_wordsExact.mp hWset
  let A := wordValue W
  let r := carryRun (bitsWord k t) c W
  let B := wordValue r.output
  let N := 2 ^ k - 1
  have hApow : A < 2 ^ k := by
    dsimp [A]
    simpa [hWlen] using wordValue_lt_pow W
  have hA : A ≤ N := by dsimp [N]; omega
  have hrunlen : W.length = (bitsWord k t).length := by simp [hWlen]
  have hnegOut : ones r.output < ones W :=
    (carryRun_negative_iff (q := bitsWord k t) (A := W) (c := c) hrunlen).mp hneg
  have hApos : 0 < A := by
    by_contra h
    have hAzero : A = 0 := by omega
    have hw : TuDeng.hammingWeight k A = ones W :=
      hamming_eq_ones_of_value hWlen rfl
    rw [hAzero] at hw
    have : TuDeng.hammingWeight k 0 = 0 := by simp [TuDeng.hammingWeight]
    omega
  have houtlen : r.output.length = k := by
    simpa [r] using carryRun_output_length (q := bitsWord k t) (A := W) (c := c) hrunlen
  have hBpow : B < 2 ^ k := by
    dsimp [B]
    simpa [houtlen] using wordValue_lt_pow r.output
  have hB : B ≤ N := by dsimp [N]; omega
  have hBlt : B < N := by
    by_contra h
    have hBeq : B = N := by omega
    have hbweight : ones r.output = k := by
      rw [← hammingWeight_modulus k]
      symm
      apply hamming_eq_ones_of_value houtlen
      simpa [B, N] using hBeq
    have hwle : ones W ≤ k := by
      have hwle' : List.count true W ≤ W.length := List.count_le_length
      simpa [ones, hWlen] using hwle'
    omega
  have hnum := carryRun_numeric (q := bitsWord k t) (A := W) (c := c) hrunlen
  rw [hclosed, length_bitsWord] at hnum
  have htPow : t < 2 ^ k := by omega
  rw [wordValue_bitsWord htPow] at hnum
  change B + 2 ^ k * c.toNat = A + t + c.toNat at hnum
  have hPN : 2 ^ k = N + 1 := by
    dsimp [N]
    have : 0 < 2 ^ k := by positivity
    omega
  have hmod : (A + t) % N = B := by
    cases c
    · simp at hnum
      rw [← hnum, Nat.mod_eq_of_lt hBlt]
    · simp at hnum
      have heq : A + t = B + N := by omega
      rw [heq, Nat.add_mod, Nat.mod_eq_of_lt hBlt]
      simp [Nat.mod_self, Nat.add_mod, Nat.mod_eq_of_lt hBlt]
  let x := N - A
  have hxlt : x < N := by dsimp [x]; omega
  have hxle : x ≤ 2 ^ k - 1 := by dsimp [x, N]; omega
  have hpartner : TuDeng.partner k t x = B := by
    rw [partner_eq_A_mod hxle]
    change (N - x + t) % N = B
    have hNA : N - x = A := by dsimp [x]; omega
    rw [hNA, hmod]
  have hcomp := hamming_modulus_sub_add_ones k x hxle
  have hbitsA : bitsWord k A = W := by
    simpa [A, hWlen] using bitsWord_wordValue W
  change TuDeng.hammingWeight k x + ones (bitsWord k (2 ^ k - 1 - x)) = k at hcomp
  have hNx : 2 ^ k - 1 - x = A := by change N - x = A; dsimp [x]; omega
  rw [hNx, hbitsA] at hcomp
  have hbweight : TuDeng.hammingWeight k B = ones r.output :=
    hamming_eq_ones_of_value houtlen rfl
  have hweight : TuDeng.hammingWeight k x +
      TuDeng.hammingWeight k (TuDeng.partner k t x) ≤ k - 1 := by
    rw [hpartner, hbweight]
    omega
  have hxmem : x ∈ tdFinset k t := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by simpa [TuDeng.modulus, N] using hxlt), hweight⟩
  have hcarryChosen : chosenCarry k A t = c := by
    cases c
    · have hs : ¬ N ≤ A + t := by
        intro hs
        simp at hnum
        omega
      simp [chosenCarry, N, hs]
    · have hs : N ≤ A + t := by
        simp at hnum
        omega
      simp [chosenCarry, N, hs]
  constructor
  · simpa [pairToOriginal, x, N] using hxmem
  · change originalToPair k t x = ⟨c, W⟩
    simp only [originalToPair]
    rw [hNx, hcarryChosen, hbitsA]

theorem originalToPair_injective_on {k t x₁ x₂ : ℕ}
    (hx₁ : x₁ ∈ tdFinset k t) (hx₂ : x₂ ∈ tdFinset k t)
    (hp : originalToPair k t x₁ = originalToPair k t x₂) : x₁ = x₂ := by
  have hx₁lt : x₁ < 2 ^ k - 1 := by
    have := (Finset.mem_filter.mp hx₁).1
    simpa [TuDeng.modulus] using Finset.mem_range.mp this
  have hx₂lt : x₂ < 2 ^ k - 1 := by
    have := (Finset.mem_filter.mp hx₂).1
    simpa [TuDeng.modulus] using Finset.mem_range.mp this
  have hA₁pow : 2 ^ k - 1 - x₁ < 2 ^ k := by omega
  have hA₂pow : 2 ^ k - 1 - x₂ < 2 ^ k := by omega
  have hv := congrArg (fun p => wordValue p.2) hp
  change wordValue (bitsWord k (2 ^ k - 1 - x₁)) =
    wordValue (bitsWord k (2 ^ k - 1 - x₂)) at hv
  rw [wordValue_bitsWord hA₁pow, wordValue_bitsWord hA₂pow] at hv
  omega

theorem tdFinset_card_eq_cyclicPairs {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) :
    (tdFinset k t).card = (cyclicPairs (bitsWord k t)).card := by
  classical
  apply Finset.card_bij (fun x _ => originalToPair k t x)
  · intro x hx
    exact originalToPair_mem hk ht hx
  · intro x₁ hx₁ x₂ hx₂ hp
    exact originalToPair_injective_on hx₁ hx₂ hp
  · intro p hp
    have hrev := pairToOriginal_mem_and_inverse hk ht hp
    exact ⟨pairToOriginal k p, hrev.1, hrev.2⟩

theorem tuDengCount_eq_cyclicInputCount {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) :
    TuDeng.tuDengCount k t = cyclicInputCount (bitsWord k t) := by
  calc
    TuDeng.tuDengCount k t = (tdFinset k t).card := tuDengCount_eq_card k t
    _ = (cyclicPairs (bitsWord k t)).card := tdFinset_card_eq_cyclicPairs hk ht
    _ = cyclicInputCount (bitsWord k t) := card_cyclicPairs _

/-- The Tu--Deng bound, obtained from the first-exit/carry proof. -/
theorem tuDengCount_bound {k t : ℕ} (hk : 2 ≤ k)
    (ht₀ : 0 < t) (ht : t < 2 ^ k - 1) :
    TuDeng.tuDengCount k t ≤ 2 ^ (k - 1) := by
  rw [tuDengCount_eq_cyclicInputCount (by omega) ht]
  have htrue : true ∈ bitsWord k t := bitsWord_mem_true ht₀ (by omega)
  have hfalse : false ∈ bitsWord k t := bitsWord_mem_false ht
  simpa using cyclicInputCount_bound_of_nonconstant (bitsWord k t) htrue hfalse

/-- Full symbolic proof of the Tu--Deng conjecture in its stated range `k ≥ 2`. -/
theorem tu_deng_conjecture_full (k t : ℕ) (hk : 2 ≤ k) :
    TuDeng.TuDengConjecture k t := by
  intro ht₀ ht
  apply tuDengCount_bound hk ht₀
  simpa [TuDeng.modulus] using ht

end TuDeng.FirstExit
