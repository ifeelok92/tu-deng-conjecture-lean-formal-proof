import Mathlib

set_option linter.style.header false

/-!
# Basic definitions for the Tu--Deng conjecture

This module contains the statement-level definitions used by the first-exit
proof.
-/

namespace TuDeng

/-- The Tu--Deng modulus `2^k - 1`. -/
def modulus (k : ℕ) : ℕ :=
  2 ^ k - 1

/-- Hamming weight of the low `k` binary bits of `n`. -/
def hammingWeight (k n : ℕ) : ℕ :=
  ((List.range k).map (fun i => if Nat.testBit n i then 1 else 0)).sum

/-- The unique representative `y` with `x + y ≡ t mod 2^k-1`. -/
def partner (k t x : ℕ) : ℕ :=
  (t + modulus k - x) % modulus k

/-- Number of Tu--Deng-valid pairs for a fixed `k,t`, counted by `x`. -/
def tuDengCount (k t : ℕ) : ℕ :=
  ((List.range (modulus k)).filter (fun x =>
    hammingWeight k x + hammingWeight k (partner k t x) ≤ k - 1)).length

/-- The Tu--Deng bound for fixed `k,t`. -/
def TuDengConjecture (k t : ℕ) : Prop :=
  0 < t → t < modulus k → tuDengCount k t ≤ 2 ^ (k - 1)

end TuDeng
