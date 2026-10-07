import Mathlib

namespace StoneGame

def pPos (m : Nat) : (r : Nat) → Option Nat → Prop
  | 0, _ => True
  | r+1, last =>
      ∀ i : Nat, i ≤ min m (r+1) → 0 < i → last ≠ some i →
        ¬ pPos m (r+1-i) (some i)
termination_by r _ => r
decreasing_by
  omega

def inT (m r i : Nat) : Prop :=
  i ≤ min m r ∧ 0 < i ∧ pPos m (r-i) (some i)

theorem stateP_iff_T (m r j : Nat) :
    pPos m r (some j) ↔ ∀ i, inT m r i → i = j := by
  cases r with
  | zero =>
      simp [pPos, inT]
  | succ r =>
      simp only [pPos]
      constructor
      · intro hp i hi
        rcases hi with ⟨hbound, hpos, hchild⟩
        by_contra hne
        have hlast : some j ≠ some i := by
          intro heq
          apply hne
          exact (Option.some.inj heq).symm
        exact (hp i hbound hpos hlast) hchild
      · intro hT i hbound hpos hlast hchild
        have hiT : inT m (r+1) i := ⟨hbound, hpos, hchild⟩
        have hij : i = j := hT i hiT
        apply hlast
        exact congrArg some hij.symm

theorem initialP_iff_noT (m r : Nat) :
    pPos m r none ↔ ∀ i, ¬ inT m r i := by
  cases r with
  | zero =>
      simp [pPos, inT]
  | succ r =>
      simp only [pPos]
      constructor
      · intro hp i hi
        rcases hi with ⟨hbound, hpos, hchild⟩
        have hlast : none ≠ some i := by simp
        exact (hp i hbound hpos hlast) hchild
      · intro hT i hbound hpos hlast hchild
        exact hT i ⟨hbound, hpos, hchild⟩

theorem inT_iff_recurrence (m r i : Nat) :
    inT m r i ↔
      i ≤ min m r ∧ 0 < i ∧ (∀ k, inT m (r-i) k → k = i) := by
  constructor
  · rintro ⟨hbound, hpos, hchild⟩
    exact ⟨hbound, hpos, (stateP_iff_T m (r-i) i).mp hchild⟩
  · rintro ⟨hbound, hpos, hsub⟩
    exact ⟨hbound, hpos, (stateP_iff_T m (r-i) i).mpr hsub⟩

theorem not_pPos_has_winning_take (m r : Nat) (last : Option Nat)
    (hN : ¬ pPos m r last) :
    ∃ i, inT m r i ∧ last ≠ some i := by
  classical
  cases r with
  | zero =>
      simp [pPos] at hN
  | succ r =>
      simp only [pPos] at hN
      push Not at hN
      rcases hN with ⟨i, hbound, hpos, hlast, hchild⟩
      exact ⟨i, ⟨hbound, hpos, hchild⟩, hlast⟩

end StoneGame
