import RequestProject.GenericWalkTools

/-! # Arithmetic progressions of visits in a uniquely accepting walk -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}

/-- Finite set of visit times of a state. -/
def visitTimes [DecidableEq S] (n : ℕ) (c : ℕ → S) (s : S) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun t => c t = s)

@[simp] theorem mem_visitTimes [DecidableEq S] {s : S} {t : ℕ} :
    t ∈ visitTimes n c s ↔ t ≤ n ∧ c t = s := by
  simp only [visitTimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- A sorted, exhaustive list of visits has a single common gap. -/
theorem ordered_visits_progression (huaw : IsUAWalk x n c) {s : S}
    {v : ℕ} (hv : 2 ≤ v) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < v → f i < f j)
    (hvisit : ∀ i, i < v → f i ≤ n ∧ c (f i) = s)
    (hcover : ∀ t, t ≤ n → c t = s → ∃ i, i < v ∧ f i = t) :
    ∃ p, 1 ≤ p ∧ ∀ i, i < v → f i = f 0 + i * p := by
  have hmid (i : ℕ) (hi : i + 1 < v) :
      ∀ t, f i < t → t < f (i + 1) → c t ≠ c (f i) := by
    intro t hit hti hct
    have htn : t ≤ n := by have := (hvisit (i + 1) hi).1; omega
    obtain ⟨j, hj, hfj⟩ := hcover t htn (hct.trans (hvisit i (by omega)).2)
    have hjgt : i < j := by
      by_contra hn
      rcases lt_or_eq_of_le (show j ≤ i by omega) with hji | rfl
      · have := hmono j i hji (by omega); omega
      · omega
    have hjlt : j < i + 1 := by
      by_contra hn
      rcases lt_or_eq_of_le (show i + 1 ≤ j by omega) with hij | hij
      · have := hmono (i + 1) j hij hj; omega
      · subst j; omega
    omega
  have hgap (i : ℕ) (hi : i + 2 < v) :
      f (i + 1) - f i = f (i + 2) - f (i + 1) := by
    apply equal_gaps huaw (hmono i (i + 1) (by omega) (by omega))
      (hmono (i + 1) (i + 2) (by omega) hi) (hvisit (i + 2) hi).1
      ((hvisit i (by omega)).2.trans (hvisit (i + 1) (by omega)).2.symm)
      ((hvisit (i + 1) (by omega)).2.trans (hvisit (i + 2) hi).2.symm)
      (hmid i (by omega))
    exact hmid (i + 1) (by omega)
  let p := f 1 - f 0
  have hp : 1 ≤ p := by have := hmono 0 1 (by omega) (by omega); dsimp [p]; omega
  have hallgap : ∀ i, i + 1 < v → f (i + 1) - f i = p := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hg := hgap i (by omega)
      have hi' := ih (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hg.symm.trans hi'
  refine ⟨p, hp, ?_⟩
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hg := hallgap i hi
    have hlt := hmono i (i + 1) (by omega) hi
    rw [Nat.succ_mul]
    omega

/-- Every state visited at least twice has an arithmetic progression of visits.
The number of visits is exactly `visitTimes.card`; the periodicity conclusions include
all intermediate letters and states, not merely the repeated state itself. -/
theorem visits_progression [DecidableEq S] (huaw : IsUAWalk x n c) (s : S)
    (hv : 2 ≤ (visitTimes n c s).card) :
    ∃ a p, 1 ≤ p ∧ a + ((visitTimes n c s).card - 1) * p ≤ n ∧
      (∀ t, t ≤ n → (c t = s ↔
        ∃ i, i < (visitTimes n c s).card ∧ t = a + i * p)) ∧
      (∀ t, a ≤ t → t + p < a + ((visitTimes n c s).card - 1) * p →
        x t = x (t + p)) ∧
      (∀ t, a ≤ t → t + p ≤ a + ((visitTimes n c s).card - 1) * p →
        c t = c (t + p)) := by
  set V := visitTimes n c s with hV
  set v := V.card with hvdef
  let emb : Fin v ↪o ℕ := V.orderEmbOfFin rfl
  let f : ℕ → ℕ := fun i => if hi : i < v then emb ⟨i, hi⟩ else 0
  have hf (i : ℕ) (hi : i < v) : f i = emb ⟨i, hi⟩ := by simp only [f, dif_pos hi]
  have hmono (i j : ℕ) (hij : i < j) (hj : j < v) : f i < f j := by
    rw [hf i (by omega), hf j hj]
    exact emb.strictMono (show (⟨i, by omega⟩ : Fin v) < ⟨j, hj⟩ from hij)
  have hvisit (i : ℕ) (hi : i < v) : f i ≤ n ∧ c (f i) = s := by
    have hh := V.orderEmbOfFin_mem rfl (⟨i, hi⟩ : Fin v)
    rw [← hf i hi] at hh
    exact mem_visitTimes.mp hh
  have hcover (t : ℕ) (ht : t ≤ n) (hct : c t = s) : ∃ i, i < v ∧ f i = t := by
    have htV : t ∈ V := mem_visitTimes.mpr ⟨ht, hct⟩
    have hr : t ∈ Set.range emb := by
      simpa only [emb, Finset.range_orderEmbOfFin, Finset.mem_coe] using htV
    obtain ⟨i, hi⟩ := hr
    exact ⟨i.val, i.isLt, (hf i.val i.isLt).trans hi⟩
  obtain ⟨p, hp, hfp⟩ := ordered_visits_progression (v := v) huaw hv f hmono hvisit hcover
  let a := f 0
  have hlast : a + (v - 1) * p ≤ n := by
    rw [← hfp (v - 1) (by omega)]
    exact (hvisit (v - 1) (by omega)).1
  have hcfirst : c a = s := (hvisit 0 (by omega)).2
  have hcperiod : c (a + p) = s := by
    have hh := (hvisit 1 (by omega)).2
    simpa only [hfp 1 (by omega), one_mul] using hh
  refine ⟨a, p, hp, hlast, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro hct
      obtain ⟨i, hi, hit⟩ := hcover t ht hct
      exact ⟨i, hi, hit.symm.trans (hfp i hi)⟩
    · rintro ⟨i, hi, rfl⟩
      rw [← hfp i hi]
      exact (hvisit i hi).2
  · intro t hat htp
    have hv3 : 3 ≤ v := by
      by_contra hn
      have hv2 : v = 2 := by omega
      simp only [hv2, Nat.reduceSub, one_mul] at htp
      omega
    have hpen : f (v - 2) + p = a + (v - 1) * p := by
      rw [hfp (v - 2) (by omega)]
      have hidx : v - 1 = (v - 2) + 1 := by omega
      rw [hidx, Nat.add_mul]
      simp [a, Nat.add_assoc]
    have hstart : a < f (v - 2) := hmono 0 (v - 2) (by omega) (by omega)
    have hend : c (f (v - 2)) = c (f (v - 2) + p) := by
      rw [hpen, ← hfp (v - 1) (by omega)]
      exact (hvisit (v - 2) (by omega)).2.trans (hvisit (v - 1) (by omega)).2.symm
    exact (rotation huaw hstart hp (by omega) (hcfirst.trans hcperiod.symm) hend).1
      t hat (by omega)
  · intro t hat htp
    by_cases hv2 : v = 2
    · have ht : t = a := by simp only [hv2, Nat.reduceSub, one_mul] at htp; omega
      subst t
      exact hcfirst.trans hcperiod.symm
    · have hv3 : 3 ≤ v := by omega
      have hpen : f (v - 2) + p = a + (v - 1) * p := by
        rw [hfp (v - 2) (by omega)]
        have hidx : v - 1 = (v - 2) + 1 := by omega
        rw [hidx, Nat.add_mul]
        simp [a, Nat.add_assoc]
      have hstart : a < f (v - 2) := hmono 0 (v - 2) (by omega) (by omega)
      have hend : c (f (v - 2)) = c (f (v - 2) + p) := by
        rw [hpen, ← hfp (v - 1) (by omega)]
        exact (hvisit (v - 2) (by omega)).2.trans (hvisit (v - 1) (by omega)).2.symm
      exact (rotation huaw hstart hp (by omega) (hcfirst.trans hcperiod.symm) hend).2
        t hat (by omega)

end AneVsAn.Generic
