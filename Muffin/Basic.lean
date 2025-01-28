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

inductive subI : Nat → Nat → Nat → Prop
| zero : subI n 0 n
| succ :
  subI n m k →
  subI n (Nat.succ m) (Nat.pred k)

lemma sub_unique (n m k k' : Nat) : subI n m k → subI n m k' → k = k' := by
  intro h₁ h₂
  induction h₁ generalizing k'
  case zero =>
    cases h₂
    rfl
  case succ a h =>
    rename_i m₁ k₁
    cases h₂
    rename_i k₂ h₂
    have h' := h k₂ h₂
    subst h'
    simp_all only [Nat.pred_eq_sub_one]

lemma le_succ_le (n m : Nat) : Nat.succ n ≤ m → n ≤ Nat.succ m := by
  intro h
  induction m
  case zero =>
    aesop
  case succ m h' =>
    simp_all
    have h₁ := Nat.le_step (Nat.le_step h)
    exact h₁

lemma le_succ (n m : Nat) : Nat.succ n ≤ m → n ≤ m := by
  intro h
  induction m
  case zero =>
    aesop
  case succ m h' =>
    simp_all
    have h₁ := Nat.le_step h
    exact h₁

lemma sub_exists (n m : Nat) : m ≤ n → ∃ k : Nat, subI n m k := by
  induction m
  case zero =>
    intro h
    apply Exists.intro n
    exact subI.zero
  case succ m h =>
    intro h'
    have le := le_succ m n h'
    have h'' := h le
    have ⟨ k, h''⟩ := h''
    apply Exists.intro (Nat.pred k)
    exact subI.succ h''
-- #print prefix Exists
-- #print prefix PSigma
def sub_exists_p (n m : Nat) : m ≤ n → Σ' k : Nat, subI n m k := by
  induction m
  case zero =>
    intro h
    exact ⟨n, subI.zero⟩
  case succ m h =>
    intro h'
    have le := le_succ m n h'
    have h'' := h le
    exact ⟨Nat.pred h''.1, subI.succ h''.2⟩

lemma add_succ (n m k : Nat) : addI (n + 1) m k → ∃ k', k = k' + 1 ∧ addI n m k' := by
  intro h
  cases h
  aesop

lemma add_unique (n m k k': Nat) : addI n m k → addI n m k' → k = k' := by
  intro h₁ h₂
  induction h₁ generalizing k'
  case zero =>
    cases h₂
    rfl
  case succ =>
    cases h₂
    aesop

/-
  Begin: the version that does not compute
-/
lemma add_exists (n m : Nat) : ∃ k, addI n m k := by
  induction n
  case zero =>
    apply Exists.intro m
    apply addI.zero
  case succ n h =>
    obtain ⟨k, h⟩ := h
    apply Exists.intro (Nat.succ k)
    apply addI.succ
    exact h

-- choose is not computable
noncomputable def addmuffin_bad (n m : Nat) : Nat := by
  have h := add_exists n m
  have k := h.choose
  exact k
/- End -/

/-
  Using PSigma for encoding the existential quantifier
-/
def add_exists_good (n m : Nat) : Σ' k: Nat, addI n m k := by
  induction n
  case zero =>
    exact PSigma.mk m (addI.zero)
  case succ n h =>
    obtain ⟨k, h⟩ := h
    exact PSigma.mk (Nat.succ k) (addI.succ h)

def addmuffin (n m : Nat) : Nat := by
  have h := add_exists_good n m
  have ⟨ k, h ⟩ := h

  exact k
  --exact h.1

#eval addmuffin 2 8
/- This can be evaluated -/


-- Old stuff that are wrong
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
