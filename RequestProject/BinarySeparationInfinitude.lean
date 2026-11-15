import RequestProject.BinarySeparationMain
import RequestProject.BinarySeparationExistence
import RequestProject.GenericComplexity

/-!
# Infinitely many binary words separating exact and unique complexity

The final statement concerns finite lists of Boolean letters. The witnesses
have strictly increasing lengths, so the result also gives infinitely many
words up to any alphabet renaming, which necessarily preserves length.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

/-- Strict separation for a finite binary word. -/
def Separates (w : List Bool) : Prop :=
  ANe w.length (fun t => w.getD t false) < AN w.length (fun t => w.getD t false)

theorem toList_separates {n : ℕ} {x : ℕ → Bool} (h : ANe n x < AN n x) :
    Separates (Generic.toList n x) := by
  unfold Separates
  rw [Generic.length_toList]
  have heq : ∀ t, t < n → (Generic.toList n x).getD t false = x t :=
    fun _ ht => Generic.getD_toList ht
  rw [Generic.ANe_congr_word heq, Generic.AN_congr_word heq]
  exact h

/-- There is a binary separating word of length `3 * 2^m + 7` for every `m ≥ 64`. -/
theorem separation_at_exponential_lengths {m : ℕ} (hm : 64 ≤ m) :
    ∃ w : List Bool, w.length = 3 * 2 ^ m + 7 ∧ Separates w := by
  obtain ⟨u, hg, hu1, hu2, hu3⟩ := exists_good_with_prefix_on_subsequence hm
  have hsep := binary_family_separation (familyLength_ge_six hm) (budget_ge_three m)
    (budget_le_length_sub_two hm) (familyLength_mod_four hm) hg
    (walk_numeric_bound_loose hm) hu1 hu2 hu3
  refine ⟨Generic.toList (3 * familyLength m + 1) (word (familyLength m) u), ?_,
    toList_separates hsep⟩
  rw [Generic.length_toList]
  unfold familyLength
  omega

/-- A choice of one separating word at each of the proved lengths. -/
noncomputable def separatingWord (m : ℕ) : List Bool :=
  (separation_at_exponential_lengths (m := m + 64) (by omega)).choose

@[simp] theorem separatingWord_length (m : ℕ) :
    (separatingWord m).length = 3 * 2 ^ (m + 64) + 7 :=
  (separation_at_exponential_lengths (m := m + 64) (by omega)).choose_spec.1

theorem separatingWord_separates (m : ℕ) : Separates (separatingWord m) :=
  (separation_at_exponential_lengths (m := m + 64) (by omega)).choose_spec.2

theorem separatingWord_lengths_strictMono : StrictMono (fun m => (separatingWord m).length) := by
  intro i j hij
  change (separatingWord i).length < (separatingWord j).length
  rw [separatingWord_length, separatingWord_length]
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) (show i + 64 < j + 64 by omega)
  omega

theorem separatingWord_injective : Function.Injective separatingWord := by
  intro i j he
  exact separatingWord_lengths_strictMono.injective (congrArg List.length he)

/-- Separating binary words have unbounded lengths. -/
theorem binary_separations_unbounded_lengths (N : ℕ) :
    ∃ w : List Bool, N < w.length ∧ Separates w := by
  refine ⟨separatingWord N, ?_, separatingWord_separates N⟩
  rw [separatingWord_length]
  have hp : N + 64 < 2 ^ (N + 64) := Nat.lt_two_pow_self
  omega

/-- There are infinitely many finite binary words with `A_Ne < A_N`. -/
theorem infinite_binary_separations : Set.Infinite {w : List Bool | Separates w} := by
  exact Set.infinite_of_injective_forall_mem separatingWord_injective separatingWord_separates

/-- Infinitely many distinct lengths occur, making the nonisomorphism consequence explicit. -/
theorem infinite_binary_separation_lengths :
    Set.Infinite {n : ℕ | ∃ w : List Bool, w.length = n ∧ Separates w} := by
  apply Set.infinite_of_injective_forall_mem separatingWord_lengths_strictMono.injective
  intro m
  exact ⟨separatingWord m, rfl, separatingWord_separates m⟩

end AneVsAn.BinarySeparation
