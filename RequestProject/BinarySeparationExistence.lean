import RequestProject.BinarySeparationDefs
import RequestProject.BinarySeparationCounting
import RequestProject.BinarySeparationNumerics

/-!
# Finite counting of good binary seeds

We use the finite space of assignments to `Fin (L - 2)`. A bad periodic factor
provides many nontrivial equations involving these bits. Every bit occurs in at
most four equations, so the sparse-constraint bound applies uniformly to all
factors. Taking a union over all endpoint/period triples avoids both minimal
windows and an infinite geometric series.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

open Finset
open scoped Classical

def extendSeed (L : ℕ) (a : Fin (L - 2) → Bool) (k : ℕ) : Bool :=
  if h : k - 1 < L - 2 then a ⟨k - 1, h⟩ else false

def positionTerm (L t : ℕ) : BitTerm (Fin (L - 2)) :=
  if h : 1 ≤ t ∧ t ≤ L - 2 then Sum.inr ⟨t - 1, by omega⟩
  else if h : 2 * L + 2 ≤ t ∧ t < 3 * L then
    Sum.inr ⟨t - (2 * L + 2), by omega⟩
  else Sum.inl (decide (t = L - 1 ∨ t = 2 * L + 1))

theorem positionTerm_left {L t : ℕ} (ht : 1 ≤ t) (htL : t ≤ L - 2) :
    positionTerm L t = Sum.inr ⟨t - 1, by omega⟩ := by
  simp [positionTerm, ht, htL]

theorem positionTerm_right {L t : ℕ} (ht : 2 * L + 2 ≤ t) (htL : t < 3 * L) :
    positionTerm L t = Sum.inr ⟨t - (2 * L + 2), by omega⟩ := by
  simp [positionTerm, show ¬(1 ≤ t ∧ t ≤ L - 2) by omega, ht, htL]

theorem positionTerm_var_iff {L t : ℕ} (hL : 2 ≤ L) (v : Fin (L - 2)) :
    positionTerm L t = Sum.inr v ↔ t = v.val + 1 ∨ t = 2 * L + 2 + v.val := by
  have hv := v.isLt
  unfold positionTerm
  split_ifs with hleft hright
  · simp only [Sum.inr.injEq, Fin.ext_iff]
    omega
  · simp only [Sum.inr.injEq, Fin.ext_iff]
    omega
  · simp only [false_iff]
    omega

theorem mem_positionTerm_vars {L t : ℕ} (hL : 2 ≤ L) (v : Fin (L - 2)) :
    v ∈ (positionTerm L t).vars ↔ t = v.val + 1 ∨ t = 2 * L + 2 + v.val := by
  have h : v ∈ (positionTerm L t).vars ↔ positionTerm L t = Sum.inr v := by
    cases positionTerm L t <;> simp [BitTerm.vars, eq_comm]
  exact h.trans (positionTerm_var_iff hL v)

theorem positionTerm_eval {L t : ℕ} (hL : 2 ≤ L) (a : Fin (L - 2) → Bool) :
    (positionTerm L t).eval a = word L (extendSeed L a) t := by
  unfold positionTerm
  split_ifs with hleft hright
  · rw [word_left hleft.1 hleft.2 hL]
    simp [BitTerm.eval, extendSeed, show t - 1 < L - 2 by omega]
  · have ht : t = 2 * L + 1 + (t - (2 * L + 1)) := by omega
    have hw := word_right (u := extendSeed L a) (t := t - (2 * L + 1))
      (by omega) (by omega) hL
    have hw' : word L (extendSeed L a) t = extendSeed L a (t - (2 * L + 1)) := by
      simpa only [← ht] using hw
    rw [hw']
    simp only [BitTerm.eval, extendSeed,
      dif_pos (show t - (2 * L + 1) - 1 < L - 2 by omega)]
    congr 1
  · by_cases ht0 : t = 0
    · subst t
      simp [BitTerm.eval, word, show (0 : ℕ) ≠ L - 1 by omega]
    · by_cases hdel : t = L - 1
      · subst t
        rw [word_left_delimiter hL]
        simp [BitTerm.eval]
      · by_cases hrun : t ≤ 2 * L
        · rw [word_run hL (by omega) hrun]
          simp [BitTerm.eval, hdel, show t ≠ 2 * L + 1 by omega]
        · by_cases hdel' : t = 2 * L + 1
          · subst t
            rw [word_right_delimiter hL]
            simp [BitTerm.eval]
          · have ht3 : 3 * L ≤ t := by omega
            simp [BitTerm.eval, hdel, hdel', word, ht0,
              show ¬t < L - 1 by omega, show ¬t < 2 * L + 1 by omega,
              show ¬t < 3 * L by omega]

def comparisonSupport (L p t : ℕ) : Finset (Fin (L - 2)) :=
  (positionTerm L t).vars ∪ (positionTerm L (t + p)).vars

theorem comparisonSupport_card (L p t : ℕ) : (comparisonSupport L p t).card ≤ 2 := by
  have hleft : (positionTerm L t).vars.card ≤ 1 := by
    cases positionTerm L t <;> simp [BitTerm.vars]
  have hright : (positionTerm L (t + p)).vars.card ≤ 1 := by
    cases positionTerm L (t + p) <;> simp [BitTerm.vars]
  have h := Finset.card_union_le (positionTerm L t).vars (positionTerm L (t + p)).vars
  unfold comparisonSupport
  omega

theorem comparisonSupport_degree {L p : ℕ} (hL : 2 ≤ L)
    (s : Finset ℕ) (v : Fin (L - 2)) :
    (s.filter (fun t => v ∈ comparisonSupport L p t)).card ≤ 4 := by
  have hsub : s.filter (fun t => v ∈ comparisonSupport L p t) ⊆
      {v.val + 1, 2 * L + 2 + v.val, v.val + 1 - p, 2 * L + 2 + v.val - p} := by
    intro t ht
    have hv := (Finset.mem_filter.mp ht).2
    simp only [comparisonSupport, Finset.mem_union, mem_positionTerm_vars hL] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc
    _ ≤ ({v.val + 1, 2 * L + 2 + v.val, v.val + 1 - p,
        2 * L + 2 + v.val - p} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 4 := by
      have h := Finset.card_insert_le (v.val + 1)
        ({2 * L + 2 + v.val, v.val + 1 - p, 2 * L + 2 + v.val - p} : Finset ℕ)
      have h' := Finset.card_insert_le (2 * L + 2 + v.val)
        ({v.val + 1 - p, 2 * L + 2 + v.val - p} : Finset ℕ)
      have h'' := Finset.card_insert_le (v.val + 1 - p)
        ({2 * L + 2 + v.val - p} : Finset ℕ)
      simp only [Finset.card_singleton] at h''
      omega

theorem comparison_terms_ne {L p t : ℕ} (hL : 2 ≤ L) (hp : 1 ≤ p)
    (hpL : p < 2 * L + 1) (hne : (comparisonSupport L p t).Nonempty) :
    positionTerm L t ≠ positionTerm L (t + p) := by
  intro heq
  obtain ⟨v, hv⟩ := hne
  have hv' : v ∈ (positionTerm L t).vars := by
    simpa [comparisonSupport, heq] using hv
  have hv'' : v ∈ (positionTerm L (t + p)).vars := heq ▸ hv'
  rw [mem_positionTerm_vars hL] at hv' hv''
  omega

theorem positionTerm_vars_empty_iff (L t : ℕ) :
    (positionTerm L t).vars = ∅ ↔
      ¬(1 ≤ t ∧ t ≤ L - 2) ∧ ¬(2 * L + 2 ≤ t ∧ t < 3 * L) := by
  unfold positionTerm
  split_ifs <;> simp_all [BitTerm.vars]

/-- In a consistent factor crossing a run boundary, a comparison of two fixed
bits can start only at `0`, at the left delimiter, or end at the final bit.
In particular there are at most three such comparisons. -/
theorem fixed_comparison_positions {L i j p t : ℕ} {u : ℕ → Bool}
    (hL : 2 ≤ L) (hp : 1 ≤ p) (hjn : j ≤ 3 * L + 1)
    (hout : ¬(L ≤ i ∧ j ≤ 2 * L + 1))
    (hperiod : HasPeriod (word L u) i j p)
    (hti : i ≤ t) (htj : t + p < j)
    (hleft : (positionTerm L t).vars = ∅)
    (hright : (positionTerm L (t + p)).vars = ∅) :
    t = 0 ∨ t = L - 1 ∨ t + p = 3 * L := by
  have hnv := (positionTerm_vars_empty_iff L t).mp hleft
  have hnv' := (positionTerm_vars_empty_iff L (t + p)).mp hright
  by_contra hbad
  push_neg at hbad
  have htlo : L ≤ t := by omega
  have hthi : t ≤ 2 * L := by omega
  have htplo : L ≤ t + p := by omega
  have htphi : t + p ≤ 2 * L := by
    have hpos : t + p ≤ 2 * L ∨ t + p = 2 * L + 1 := by omega
    rcases hpos with h | h
    · exact h
    · have heq := hperiod t hti htj
      rw [word_run hL htlo hthi, h, word_right_delimiter hL] at heq
      contradiction
  have hple : p ≤ L := by omega
  by_cases hi : i < L
  · have heq := hperiod (L - 1) (by omega) (by omega)
    rw [word_left_delimiter hL, word_run hL (by omega) (by omega)] at heq
    contradiction
  · have hj : 2 * L + 1 < j := by omega
    have heq := hperiod (2 * L + 1 - p) (by omega) (by omega)
    have he : 2 * L + 1 - p + p = 2 * L + 1 := by omega
    rw [word_run hL (by omega) (by omega), he, word_right_delimiter hL] at heq
    contradiction

noncomputable def activeComparisons (L i j p : ℕ) : Finset ℕ :=
  (Finset.Ico i (j - p)).filter (fun t => (comparisonSupport L p t).Nonempty)

theorem activeComparisons_card {L i j p : ℕ} {u : ℕ → Bool}
    (hL : 2 ≤ L) (hp : 1 ≤ p) (hij : i + p ≤ j) (hjn : j ≤ 3 * L + 1)
    (hout : ¬(L ≤ i ∧ j ≤ 2 * L + 1))
    (hperiod : HasPeriod (word L u) i j p) :
    j - i - p ≤ (activeComparisons L i j p).card + 3 := by
  let fixed := (Finset.Ico i (j - p)).filter
    (fun t => ¬(comparisonSupport L p t).Nonempty)
  have hsub : fixed ⊆ {0, L - 1, 3 * L - p} := by
    intro t ht
    obtain ⟨ht, hf⟩ := Finset.mem_filter.mp ht
    obtain ⟨hti, htj⟩ := Finset.mem_Ico.mp ht
    have hempty : comparisonSupport L p t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    have hparts := Finset.union_eq_empty.mp hempty
    have hpos := fixed_comparison_positions hL hp hjn hout hperiod hti
      (by omega) hparts.1 hparts.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hfixed : fixed.card ≤ 3 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le 0 ({L - 1, 3 * L - p} : Finset ℕ)
    have h3 := Finset.card_insert_le (L - 1) ({3 * L - p} : Finset ℕ)
    simp only [Finset.card_singleton] at h3
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.Ico i (j - p)) (fun t => (comparisonSupport L p t).Nonempty)
  have hIco : (Finset.Ico i (j - p)).card = j - i - p := by
    rw [Nat.card_Ico]
    omega
  change (activeComparisons L i j p).card + fixed.card = _ at hsplit
  omega

/-- One periodic factor removes at least `r` binary degrees of freedom whenever
its excess length over its period is at least `8*r + 3`. -/
theorem periodic_factor_count {L i j p r : ℕ}
    (hL3 : 3 ≤ L) (hp : 1 ≤ p) (hij : i ≤ j) (hjn : j ≤ 3 * L + 1)
    (hp2 : 2 * p ≤ j - i) (hout : ¬(L ≤ i ∧ j ≤ 2 * L + 1))
    (hr : 8 * r + 3 ≤ j - i - p) :
    (Finset.univ.filter (fun a : Fin (L - 2) → Bool =>
      HasPeriod (word L (extendSeed L a)) i j p)).card ≤ 2 ^ (L - 2 - r) := by
  classical
  have hL : 2 ≤ L := by omega
  by_cases hex : ∃ a : Fin (L - 2) → Bool,
      HasPeriod (word L (extendSeed L a)) i j p
  · obtain ⟨a0, ha0⟩ := hex
    let s := activeComparisons L i j p
    have hne : ∀ t ∈ s, (comparisonSupport L p t).Nonempty := by
      intro t ht
      exact (Finset.mem_filter.mp ht).2
    obtain ⟨q, hqs, hdisj, hcard⟩ := exists_disjoint_supports s
      (comparisonSupport L p) 2 4 hne (fun t _ => comparisonSupport_card L p t)
      (comparisonSupport_degree hL s)
    have hs := activeComparisons_card hL hp (by omega) hjn hout ha0
    have hrq : r ≤ q.card := by dsimp [s] at hcard; omega
    have hpL : p < 2 * L + 1 := by omega
    have hpiv : ∀ t ∈ q, ∃ v ∈ comparisonSupport L p t,
        ∀ a b : Fin (L - 2) → Bool,
          (positionTerm L t).eval a = (positionTerm L (t + p)).eval a →
          (positionTerm L t).eval b = (positionTerm L (t + p)).eval b →
          (∀ w ∈ comparisonSupport L p t, w ≠ v → a w = b w) → a v = b v := by
      intro t ht
      exact BitTerm.exists_pivot (positionTerm L t) (positionTerm L (t + p))
        (hne t (hqs ht)) (comparison_terms_ne hL hp hpL (hne t (hqs ht)))
    let pivot : ℕ → Fin (L - 2) := fun t =>
      if ht : t ∈ q then Classical.choose (hpiv t ht) else ⟨0, by omega⟩
    have hpivot : ∀ t ∈ q, pivot t ∈ comparisonSupport L p t := by
      intro t ht
      simpa [pivot, ht] using (Classical.choose_spec (hpiv t ht)).1
    let C := fun t (a : Fin (L - 2) → Bool) =>
      (positionTerm L t).eval a = (positionTerm L (t + p)).eval a
    have hdet : ∀ t ∈ q, ∀ a b : Fin (L - 2) → Bool, C t a → C t b →
        (∀ w ∈ comparisonSupport L p t, w ≠ pivot t → a w = b w) →
        a (pivot t) = b (pivot t) := by
      intro t ht
      simpa [pivot, ht, C] using (Classical.choose_spec (hpiv t ht)).2
    have hcount := card_solutions_le_of_disjoint_supports q
      (comparisonSupport L p) pivot C hpivot hdisj hdet
    have hsubset : (Finset.univ.filter (fun a : Fin (L - 2) → Bool =>
        HasPeriod (word L (extendSeed L a)) i j p)) ⊆
        Finset.univ.filter (fun a => ∀ t ∈ q, C t a) := by
      intro a ha
      have hper := (Finset.mem_filter.mp ha).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro t ht
      have ht' := (Finset.mem_filter.mp (hqs ht)).1
      have hbounds := Finset.mem_Ico.mp ht'
      have h := hper t hbounds.1 (by omega)
      simpa [C, positionTerm_eval hL] using h
    calc
      _ ≤ (Finset.univ.filter (fun a => ∀ t ∈ q, C t a)).card :=
        Finset.card_le_card hsubset
      _ ≤ 2 ^ (Fintype.card (Fin (L - 2)) - q.card) := by
        convert hcount using 1
        congr 1
        ext a
        simp
      _ ≤ 2 ^ (L - 2 - r) := by
        simp only [Fintype.card_fin]
        exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  · have hempty : (Finset.univ.filter (fun a : Fin (L - 2) → Bool =>
        HasPeriod (word L (extendSeed L a)) i j p)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a _ ha
      exact hex ⟨a, ha⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

def BadFactor (L B i j p : ℕ) (a : Fin (L - 2) → Bool) : Prop :=
  1 ≤ p ∧ i ≤ j ∧ j ≤ 3 * L + 1 ∧ 2 * p ≤ j - i ∧
    ¬(L ≤ i ∧ j ≤ 2 * L + 1) ∧ p + B ≤ j - i ∧
    HasPeriod (word L (extendSeed L a)) i j p

/-- A purely finite existence criterion. Its generous constants are chosen to
keep the infinitude proof independent of small-length computations. -/
theorem exists_good_of_large_space {L B r : ℕ}
    (hL : 3 ≤ L) (hrlen : r ≤ L - 2) (hrB : 8 * r + 3 ≤ B)
    (hspace : (3 * L + 2) ^ 3 < 2 ^ r) :
    ∃ u : ℕ → Bool, BGood L B u := by
  classical
  let I := Fin (3 * L + 2) × Fin (3 * L + 2) × Fin (3 * L + 2)
  let C : I → (Fin (L - 2) → Bool) → Prop := fun v a =>
    BadFactor L B v.1.val v.2.1.val v.2.2.val a
  let R := 2 ^ (L - 2 - r)
  have hcount : ∀ v : I, (Finset.univ.filter (C v)).card ≤ R := by
    intro v
    by_cases hex : ∃ a, C v a
    · obtain ⟨a0, ha0⟩ := hex
      obtain ⟨hp, hij, hjn, hp2, hout, hlong, _⟩ := ha0
      have hper := periodic_factor_count hL hp hij hjn hp2 hout
        (by omega : 8 * r + 3 ≤ v.2.1.val - v.1.val - v.2.2.val)
      have hsub : Finset.univ.filter (C v) ⊆
          Finset.univ.filter (fun a : Fin (L - 2) → Bool =>
            HasPeriod (word L (extendSeed L a)) v.1.val v.2.1.val v.2.2.val) := by
        intro a ha
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact (Finset.mem_filter.mp ha).2.2.2.2.2.2.2
      exact (Finset.card_le_card hsub).trans hper
    · have hempty : Finset.univ.filter (C v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a _ ha
        exact hex ⟨a, ha⟩
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  have hI : Fintype.card I = (3 * L + 2) ^ 3 := by
    simp only [I, Fintype.card_prod, Fintype.card_fin]
    ring
  have hA : Fintype.card (Fin (L - 2) → Bool) = 2 ^ (L - 2) := by simp
  have hsize : Fintype.card I * R < Fintype.card (Fin (L - 2) → Bool) := by
    rw [hI, hA]
    have hpos : 0 < R := by dsimp [R]; positivity
    have hmul := Nat.mul_lt_mul_of_pos_right hspace hpos
    have hpows : 2 ^ r * R = 2 ^ (L - 2) := by
      dsimp [R]
      rw [← pow_add, show r + (L - 2 - r) = L - 2 by omega]
    omega
  obtain ⟨a, ha⟩ := exists_avoiding_all C R hcount hsize
  refine ⟨extendSeed L a, ?_⟩
  intro i j p hp hij hjn hp2 hout hperiod
  by_contra hbad
  have hi' : i < 3 * L + 2 := by omega
  have hj' : j < 3 * L + 2 := by omega
  have hp' : p < 3 * L + 2 := by omega
  apply ha (⟨i, hi'⟩, ⟨j, hj'⟩, ⟨p, hp'⟩)
  change BadFactor L B i j p a
  exact ⟨hp, hij, hjn, hp2, hout, by omega, hperiod⟩

/-- Good binary seeds exist along the explicit cofinal sequence used in the
infinitude theorem. -/
theorem exists_good_on_subsequence {m : ℕ} (hm : 64 ≤ m) :
    ∃ u : ℕ → Bool, BGood (familyLength m) (goodnessBudget m) u := by
  apply exists_good_of_large_space (r := 8 * m)
  · have := familyLength_ge_six hm
    omega
  · exact seed_length_ge_rank hm
  · unfold goodnessBudget
    omega
  · exact window_count_lt_pow_rank hm

/-- Install the fixed prefix `001` and use the remaining coordinates freely. -/
def prefixAssignment (N : ℕ) (a : Fin (N - 3) → Bool) (v : Fin N) : Bool :=
  if h : v.val < 3 then decide (v.val = 2)
  else a ⟨v.val - 3, by omega⟩

theorem prefixAssignment_injective (N : ℕ) : Function.Injective (prefixAssignment N) := by
  intro a b hab
  funext v
  have hv : v.val + 3 < N := by have := v.isLt; omega
  have he := congrFun hab ⟨v.val + 3, hv⟩
  simpa [prefixAssignment, show ¬v.val + 3 < 3 by omega] using he

theorem badFactor_count {L B i j p r : ℕ} (hL : 3 ≤ L) (hrB : 8 * r + 3 ≤ B) :
    (Finset.univ.filter (BadFactor L B i j p)).card ≤ 2 ^ (L - 2 - r) := by
  classical
  by_cases hex : ∃ a, BadFactor L B i j p a
  · obtain ⟨a0, hp, hij, hjn, hp2, hout, hlong, _⟩ := hex
    have hper := periodic_factor_count hL hp hij hjn hp2 hout
      (by omega : 8 * r + 3 ≤ j - i - p)
    have hsub : Finset.univ.filter (BadFactor L B i j p) ⊆
        Finset.univ.filter (fun a : Fin (L - 2) → Bool =>
          HasPeriod (word L (extendSeed L a)) i j p) := by
      intro a ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (Finset.mem_filter.mp ha).2.2.2.2.2.2.2
    exact (Finset.card_le_card hsub).trans hper
  · have hempty : Finset.univ.filter (BadFactor L B i j p) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a _ ha
      exact hex ⟨a, ha⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

theorem exists_good_with_prefix_of_large_space {L B r : ℕ}
    (hL : 5 ≤ L) (hr : 3 ≤ r) (hrlen : r ≤ L - 2) (hrB : 8 * r + 3 ≤ B)
    (hspace : (3 * L + 2) ^ 3 < 2 ^ (r - 3)) :
    ∃ u : ℕ → Bool, BGood L B u ∧ u 1 = false ∧ u 2 = false ∧ u 3 = true := by
  classical
  let I := Fin (3 * L + 2) × Fin (3 * L + 2) × Fin (3 * L + 2)
  let C : I → (Fin (L - 2 - 3) → Bool) → Prop := fun v a =>
    BadFactor L B v.1.val v.2.1.val v.2.2.val (prefixAssignment (L - 2) a)
  let R := 2 ^ (L - 2 - r)
  have hcount : ∀ v : I, (Finset.univ.filter (C v)).card ≤ R := by
    intro v
    let bad := Finset.univ.filter (C v)
    have hsub : bad.image (prefixAssignment (L - 2)) ⊆
        Finset.univ.filter (BadFactor L B v.1.val v.2.1.val v.2.2.val) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    calc
      _ = (bad.image (prefixAssignment (L - 2))).card :=
        (Finset.card_image_of_injective bad (prefixAssignment_injective (L - 2))).symm
      _ ≤ (Finset.univ.filter (BadFactor L B v.1.val v.2.1.val v.2.2.val)).card :=
        Finset.card_le_card hsub
      _ ≤ R := badFactor_count (by omega) hrB
  have hI : Fintype.card I = (3 * L + 2) ^ 3 := by
    simp only [I, Fintype.card_prod, Fintype.card_fin]
    ring
  have hA : Fintype.card (Fin (L - 2 - 3) → Bool) = 2 ^ (L - 2 - 3) := by simp
  have hsize : Fintype.card I * R < Fintype.card (Fin (L - 2 - 3) → Bool) := by
    rw [hI, hA]
    have hpos : 0 < R := by dsimp [R]; positivity
    have hmul := Nat.mul_lt_mul_of_pos_right hspace hpos
    have hpows : 2 ^ (r - 3) * R = 2 ^ (L - 2 - 3) := by
      dsimp [R]
      rw [← pow_add, show r - 3 + (L - 2 - r) = L - 2 - 3 by omega]
    omega
  obtain ⟨a, ha⟩ := exists_avoiding_all C R hcount hsize
  refine ⟨extendSeed L (prefixAssignment (L - 2) a), ?_, ?_, ?_, ?_⟩
  · intro i j p hp hij hjn hp2 hout hperiod
    by_contra hbad
    have hi' : i < 3 * L + 2 := by omega
    have hj' : j < 3 * L + 2 := by omega
    have hp' : p < 3 * L + 2 := by omega
    apply ha (⟨i, hi'⟩, ⟨j, hj'⟩, ⟨p, hp'⟩)
    change BadFactor L B i j p (prefixAssignment (L - 2) a)
    exact ⟨hp, hij, hjn, hp2, hout, by omega, hperiod⟩
  · simp [extendSeed, prefixAssignment, show 0 < L - 2 by omega]
  · simp [extendSeed, prefixAssignment, show 1 < L - 2 by omega]
  · simp [extendSeed, prefixAssignment, show 2 < L - 2 by omega]

theorem exists_good_with_prefix_on_subsequence {m : ℕ} (hm : 64 ≤ m) :
    ∃ u : ℕ → Bool, BGood (familyLength m) (goodnessBudget m) u ∧
      u 1 = false ∧ u 2 = false ∧ u 3 = true := by
  apply exists_good_with_prefix_of_large_space (r := 8 * m)
  · have := familyLength_ge_six hm
    omega
  · omega
  · exact seed_length_ge_rank hm
  · unfold goodnessBudget
    omega
  · exact window_count_lt_pow_rank_sub_three hm

end AneVsAn.BinarySeparation
