-- import Init.Data.Nat.Basic
-- import Mathlib.Algebra.Group.Basic
-- import Init.PropLemmas
import Mathlib
import Aesop

def hello := "world"
/- If I define addition of natural number as below -/
inductive addI : Nat → Nat → Nat → Prop
| zero : addI 0 n n
| succ :
  addI n m k →
  addI (Nat.succ n) m (Nat.succ k)

lemma add_succ (n m k : Nat) : addI (n + 1) m k → ∃ k', k = k' + 1 ∧ addI n m k' := by
  intro h
  cases h
  aesop

lemma add_unique : ∀ {n m k k'}, addI n m k → addI n m k' → k = k' := by
  intro n m k k' h₁ h₂
  induction h₁ generalizing k'
  case zero =>
    cases h₂
    rfl
  case succ =>
    cases h₂
    aesop

def addf (n m : Nat) := ∃ k, addI n m k

instance : Decidable (addf n m) := by
  simp [addf]
  induction n
  . apply isTrue
    apply Exists.intro m
    apply addI.zero
  . rename_i n h
    cases h
    . rename_i h₁
      apply isFalse
      simp_all only [not_exists]
      by_contra h
      simp at h
      obtain ⟨k, h⟩ := h
      have h' := add_succ n m k h
      simp_all only [and_false, exists_const]
    . rename_i h₁
      apply isTrue
      obtain ⟨k, h⟩ := h₁
      apply Exists.intro (Nat.succ k)
      apply addI.succ
      exact h

#eval addf 0 8
