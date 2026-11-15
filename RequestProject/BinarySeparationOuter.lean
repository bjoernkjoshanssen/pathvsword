import RequestProject.BinarySeparationCount
import RequestProject.GenericVisitProgression

/-!
# Outer states have at most two visits

For the infinitude theorem a coarse cubic surplus estimate suffices. It applies
uniformly to all positive periods, so this argument does not split off periods
one and two. An exchange with an outer first-return cycle bounds the number of
visits to each state confined to the central run.
-/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {L B : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

def visitCount (L : ℕ) (c : ℕ → S) (s : S) : ℕ :=
  (visitTimes (3 * L + 1) c s).card

theorem visitTimes_partition (s : S) :
    visitTimes (3 * L + 1) c s = nvis L c s ∪ rvis L c s := by
  ext t
  simp only [mem_visitTimes, Finset.mem_union, nvis, rvis, nonRunTimes,
    times, runTimes, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨ht, hct⟩
    by_cases hr : L ≤ t ∧ t ≤ 2 * L + 1
    · exact Or.inr ⟨hr, hct⟩
    · exact Or.inl ⟨⟨by omega, hr⟩, hct⟩
  · rintro (⟨⟨ht, _⟩, hct⟩ | ⟨⟨ha, hb⟩, hct⟩) <;> exact ⟨by omega, hct⟩

theorem visits_disjoint (s : S) : Disjoint (nvis L c s) (rvis L c s) := by
  apply Finset.disjoint_left.mpr
  intro t ht ht'
  simp only [nvis, rvis, nonRunTimes, Finset.mem_filter, Finset.mem_sdiff] at ht ht'
  exact ht.1.2 ht'.1

theorem visitCount_eq (s : S) : visitCount L c s = (nvis L c s).card + (rvis L c s).card := by
  rw [visitCount, visitTimes_partition, Finset.card_union_of_disjoint (visits_disjoint s)]

theorem outside_visit {s : S} (h : 1 ≤ (nvis L c s).card) :
    ∃ t, t ≤ 3 * L + 1 ∧ c t = s ∧ (t < L ∨ 2 * L + 1 < t) := by
  obtain ⟨t, ht⟩ := Finset.card_pos.mp h
  simp only [nvis, nonRunTimes, times, runTimes, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc] at ht
  exact ⟨t, by omega, ht.2, by omega⟩

theorem run_of_no_outside {s : S} (h : (nvis L c s).card = 0)
    {t : ℕ} (ht : t ≤ 3 * L + 1) (hct : c t = s) : L ≤ t ∧ t ≤ 2 * L + 1 := by
  by_contra hn
  have hmem : t ∈ nvis L c s := by
    simp only [nvis, nonRunTimes, times, runTimes, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
    exact ⟨⟨by omega, hn⟩, hct⟩
  rw [Finset.card_eq_zero.mp h] at hmem
  exact Finset.notMem_empty _ hmem

/-- All visits and the intervening letters follow one arithmetic progression. -/
structure VisitPattern (L : ℕ) (u : ℕ → Bool) (c : ℕ → S) (s : S) where
  first : ℕ
  period : ℕ
  two_visits : 2 ≤ visitCount L c s
  period_pos : 1 ≤ period
  last_le : first + (visitCount L c s - 1) * period ≤ 3 * L + 1
  visit_iff : ∀ t, t ≤ 3 * L + 1 → (c t = s ↔
    ∃ i, i < visitCount L c s ∧ t = first + i * period)
  word_period : ∀ t, first ≤ t → t + period < first + (visitCount L c s - 1) * period →
    word L u t = word L u (t + period)
  state_period : ∀ t, first ≤ t → t + period ≤ first + (visitCount L c s - 1) * period →
    c t = c (t + period)

noncomputable def visitPattern (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (s : S) (hv : 2 ≤ visitCount L c s) : VisitPattern L u c s :=
  Classical.choice (by
    obtain ⟨a, p, hp, hlast, hvis, hword, hstate⟩ := visits_progression huaw s hv
    exact ⟨⟨a, p, hv, hp, hlast, hvis, hword, hstate⟩⟩)

namespace VisitPattern

variable {s : S} (d : VisitPattern L u c s)

theorem first_le : d.first ≤ 3 * L + 1 := by have := d.last_le; omega

theorem visit (i : ℕ) (hi : i < visitCount L c s) : c (d.first + i * d.period) = s := by
  have hm := Nat.mul_le_mul_right d.period (show i ≤ visitCount L c s - 1 by omega)
  apply (d.visit_iff _ (by have := d.last_le; omega)).2
  exact ⟨i, hi, rfl⟩

theorem first_visit : c d.first = s := by
  have hh := d.visit 0 (by have := d.two_visits; omega)
  simpa using hh

theorem last_visit : c (d.first + (visitCount L c s - 1) * d.period) = s :=
  d.visit _ (by have := d.two_visits; omega)

theorem first_le_visit {t : ℕ} (ht : t ≤ 3 * L + 1) (hct : c t = s) : d.first ≤ t := by
  obtain ⟨i, _, rfl⟩ := (d.visit_iff t ht).1 hct
  omega

theorem visit_le_last {t : ℕ} (ht : t ≤ 3 * L + 1) (hct : c t = s) :
    t ≤ d.first + (visitCount L c s - 1) * d.period := by
  obtain ⟨i, hi, rfl⟩ := (d.visit_iff t ht).1 hct
  exact Nat.add_le_add_left (Nat.mul_le_mul_right d.period (by omega)) _

theorem not_in_run (hout : 1 ≤ (nvis L c s).card) :
    ¬(L ≤ d.first ∧ d.first + (visitCount L c s - 1) * d.period ≤ 2 * L + 1) := by
  obtain ⟨t, ht, hct, hto⟩ := outside_visit hout
  have ha := d.first_le_visit ht hct
  have hb := d.visit_le_last ht hct
  omega

theorem good_bounds (hg : BGood L B u) (hout : 1 ≤ (nvis L c s).card)
    (hv : 3 ≤ visitCount L c s) : d.period < B ∧ visitCount L c s - 2 ≤ B := by
  have hp := d.period_pos
  have hm : 2 * d.period ≤ (visitCount L c s - 1) * d.period :=
    Nat.mul_le_mul_right d.period (by omega)
  have hgood := hg d.first (d.first + (visitCount L c s - 1) * d.period)
    d.period hp (by omega) d.last_le (by omega) (d.not_in_run hout) d.word_period
  rw [Nat.add_sub_cancel_left] at hgood
  have hsplit : visitCount L c s - 1 = (visitCount L c s - 2) + 1 := by omega
  rw [hsplit, Nat.add_mul, Nat.one_mul] at hgood
  have hmul : visitCount L c s - 2 ≤ (visitCount L c s - 2) * d.period := by
    simpa using Nat.mul_le_mul_left (visitCount L c s - 2) hp
  have hperiod : d.period ≤ (visitCount L c s - 2) * d.period := by
    simpa using Nat.mul_le_mul_right d.period (show 1 ≤ visitCount L c s - 2 by omega)
  constructor <;> omega

/-- First visits of distinct states with the same period lie less than one period apart. -/
theorem first_gap {t : S} (e : VisitPattern L u c t)
    (hv : 3 ≤ visitCount L c t) (hp : d.period = e.period)
    (hfirst : d.first < e.first)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) : e.first - d.first < d.period := by
  have hp0 := d.period_pos
  have hep0 := e.period_pos
  have hfirstn := e.first_le
  have htwo : e.first + 2 * d.period ≤ 3 * L + 1 := by
    have hm := Nat.mul_le_mul_right e.period (show 2 ≤ visitCount L c t - 1 by omega)
    have := e.last_le
    rw [hp]
    omega
  have hca : c d.first = c (d.first + d.period) := by
    exact d.first_visit.trans (by simpa using (d.visit 1 (by have := d.two_visits; omega)).symm)
  have hcb : c (e.first + d.period) = c (e.first + d.period + d.period) := by
    rw [hp]
    have h1 := e.visit 1 (by omega)
    have h2 := e.visit 2 hv
    simpa [two_mul, Nat.add_assoc] using h1.trans h2.symm
  have hr := (rotation huaw (show d.first < e.first + d.period by omega)
    hp0 (by omega) hca hcb).2
  by_contra hn
  have heq := hr (e.first - d.period) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : d.period ≤ e.first)] at heq
  have hbefore := e.first_le_visit (t := e.first - d.period) (by omega)
    (heq.trans e.first_visit)
  omega

end VisitPattern

/-- A deliberately coarse bound for the total excess of repeated outer states.
There are fewer than `B` possible periods, at most `B` states of each period,
and at most `B` excess visits per state. -/
theorem outer_surplus_bound (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hg : BGood L B u) (C : Finset S)
    (hout : ∀ s ∈ C, 1 ≤ (nvis L c s).card)
    (hv : ∀ s ∈ C, 3 ≤ visitCount L c s) :
    ∑ s ∈ C, (visitCount L c s - 2) ≤ B ^ 3 := by
  classical
  let D (s : S) (hs : s ∈ C) : VisitPattern L u c s :=
    visitPattern huaw s (by have := hv s hs; omega)
  let p : S → ℕ := fun s => if hs : s ∈ C then (D s hs).period else 0
  let a : S → ℕ := fun s => if hs : s ∈ C then (D s hs).first else 0
  have hp_spec (s : S) (hs : s ∈ C) : p s = (D s hs).period := by simp [p, hs]
  have ha_spec (s : S) (hs : s ∈ C) : a s = (D s hs).first := by simp [a, hs]
  have hp (s : S) (hs : s ∈ C) : p s < B := by
    rw [hp_spec s hs]
    exact ((D s hs).good_bounds hg (hout s hs) (hv s hs)).1
  have h_excess (s : S) (hs : s ∈ C) : visitCount L c s - 2 ≤ B :=
    ((D s hs).good_bounds hg (hout s hs) (hv s hs)).2
  have ha_inj : Set.InjOn a (↑C : Set S) := by
    intro s hs t ht heq
    rw [ha_spec s hs, ha_spec t ht] at heq
    exact (D s hs).first_visit.symm.trans (heq ▸ (D t ht).first_visit)
  have hfiber (k : ℕ) : (C.filter (fun s => p s = k)).card ≤ B := by
    let T := C.filter (fun s => p s = k)
    by_cases hne : T.Nonempty
    · obtain ⟨s0, hs0, hmin⟩ := T.exists_min_image a hne
      have hs0C : s0 ∈ C := (Finset.mem_filter.mp hs0).1
      have hs0p : p s0 = k := (Finset.mem_filter.mp hs0).2
      have hBp : 1 ≤ B := by have := hp s0 hs0C; omega
      have hspan (s : S) (hs : s ∈ T) : a s0 ≤ a s ∧ a s < a s0 + B := by
        have hsC : s ∈ C := (Finset.mem_filter.mp hs).1
        have hsp : p s = k := (Finset.mem_filter.mp hs).2
        have hlow := hmin s hs
        refine ⟨hlow, ?_⟩
        by_cases heq : a s0 = a s
        · omega
        · have hperiod : (D s0 hs0C).period = (D s hsC).period := by
            rw [← hp_spec s0 hs0C, ← hp_spec s hsC, hs0p, hsp]
          have hfirst : (D s0 hs0C).first < (D s hsC).first := by
            rw [← ha_spec s0 hs0C, ← ha_spec s hsC]; omega
          have hgap := (D s0 hs0C).first_gap (D s hsC) (hv s hsC) hperiod hfirst huaw
          rw [← ha_spec s0 hs0C, ← ha_spec s hsC, ← hp_spec s0 hs0C] at hgap
          have := hp s0 hs0C
          omega
      have hinj : Set.InjOn a (↑T : Set S) := by
        intro s hs t ht heq
        exact ha_inj (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1 heq
      calc T.card = (T.image a).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Ico (a s0) (a s0 + B)).card := by
          apply Finset.card_le_card
          intro b hb
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
          exact Finset.mem_Ico.mpr (hspan s hs)
        _ = B := by simp
    · have hzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change T.card ≤ B
      simp [hzero]
  have hcard : C.card ≤ B * B := by
    have hsum : C.card = ∑ k ∈ Finset.range B, (C.filter (fun s => p s = k)).card :=
      Finset.card_eq_sum_card_fiberwise (fun s hs => Finset.mem_range.mpr (hp s hs))
    calc C.card = ∑ k ∈ Finset.range B, (C.filter (fun s => p s = k)).card := hsum
      _ ≤ ∑ _k ∈ Finset.range B, B := Finset.sum_le_sum (fun k _ => hfiber k)
      _ = B * B := by simp
  calc (∑ s ∈ C, (visitCount L c s - 2)) ≤ ∑ _s ∈ C, B :=
      Finset.sum_le_sum h_excess
    _ = C.card * B := by simp
    _ ≤ (B * B) * B := Nat.mul_le_mul_right B hcard
    _ = B ^ 3 := by ring

private theorem edge_exists_of_count_ne_zero {len : ℕ} {τ : ℕ → ℕ} {e : S × Bool × S}
    (h : edgeCount (word L u) c len τ e ≠ 0) :
    ∃ j, j < len ∧ edge (word L u) c (τ j) = e := by
  classical
  by_contra hn
  apply h
  apply edgeCount_eq_zero_iff.mpr
  intro j hj heq
  exact hn ⟨j, hj, heq⟩

/-- Exchanging a long central chord with repetitions of an outer cycle bounds
the visits of every state confined to the run. This holds even when the outer
period is one or two. -/
theorem run_only_visits_le_period (hL : 2 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) {s : S}
    (d : VisitPattern L u c s) (hout : 1 ≤ (nvis L c s).card)
    (r : S) (hr : (nvis L c r).card = 0) : visitCount L c r ≤ d.period := by
  classical
  by_contra hn
  have hrv : d.period + 1 ≤ visitCount L c r := by omega
  have hp := d.period_pos
  let e := visitPattern huaw r (by omega : 2 ≤ visitCount L c r)
  have hep := e.period_pos
  obtain ⟨σ, hσn, hσ, hσout⟩ := outside_visit hout
  have hfirst := run_of_no_outside hr e.first_le e.first_visit
  have hlast := run_of_no_outside hr e.last_le e.last_visit
  have hmul : d.period * e.period ≤ (visitCount L c r - 1) * e.period :=
    Nat.mul_le_mul_right e.period (by omega)
  have hendn : e.first + d.period * e.period ≤ 3 * L + 1 := by
    have := e.last_le; omega
  have hendrun : e.first + d.period * e.period ≤ 2 * L + 1 := by omega
  have hend : c (e.first + d.period * e.period) = r := e.visit d.period (by omega)
  have hchord : c e.first = c (e.first + d.period * e.period) :=
    e.first_visit.trans hend.symm
  have hpos : σ ≤ e.first ∨ e.first + d.period * e.period ≤ σ := by omega
  have dsecondn : d.first + d.period ≤ 3 * L + 1 := by
    have hm := Nat.mul_le_mul_right d.period (show 1 ≤ visitCount L c s - 1 by
      have := d.two_visits; omega)
    have := d.last_le
    simp only [one_mul] at hm
    omega
  have dsecond : c (d.first + d.period) = s := by
    simpa using d.visit 1 (by have := d.two_visits; omega)
  have hcycle : Seg (3 * L + 1) c (c σ) (c σ) d.period (fun j => d.first + j) := by
    have hh := segW c (show d.first ≤ d.first + d.period by omega) dsecondn
    simpa only [hσ, d.first_visit, dsecond, Nat.add_sub_cancel_left] using hh
  have hC : Seg (3 * L + 1) c (c σ) (c σ)
      (e.first + d.period * e.period - e.first)
      (repit e.period d.period (fun j => d.first + j)) := by
    simpa only [Nat.add_sub_cancel_left, Nat.mul_comm] using seg_repit hcycle e.period
  have htransfer (j : ℕ) (hj : j < d.period) :
      ∃ k, k < d.period * e.period ∧
        edge (word L u) c (e.first + k) = edge (word L u) c (d.first + j) := by
    have hbase : edgeCount (word L u) c d.period (fun i => d.first + i)
        (edge (word L u) c (d.first + j)) ≠ 0 := by
      intro hzero
      exact (edgeCount_eq_zero_iff.mp hzero) j hj rfl
    have heq := exchange_one huaw (show e.first ≤ e.first + d.period * e.period by omega)
      hendn hσn hchord hpos hC (edge (word L u) c (d.first + j))
    rw [Nat.add_sub_cancel_left, Nat.mul_comm d.period e.period, edgeCount_repit] at heq
    have hremoved : edgeCount (word L u) c (e.period * d.period) (fun i => e.first + i)
        (edge (word L u) c (d.first + j)) ≠ 0 := by
      rw [heq]
      exact Nat.mul_ne_zero (by omega) hbase
    obtain ⟨k, hk, he⟩ := edge_exists_of_count_ne_zero hremoved
    exact ⟨k, by simpa only [Nat.mul_comm] using hk, he⟩
  have hcyclezero (j : ℕ) (hj : j < d.period) : word L u (d.first + j) = false := by
    obtain ⟨k, hk, he⟩ := htransfer j hj
    have hlabel := congrArg (fun e : S × Bool × S => e.2.1) he
    change word L u (e.first + k) = word L u (d.first + j) at hlabel
    rw [word_run hL (by omega) (by omega)] at hlabel
    exact hlabel.symm
  obtain ⟨k, hk, he⟩ := htransfer (d.period - 1) (by omega)
  have hhead := congrArg (fun e : S × Bool × S => e.2.2) he
  change c (e.first + k + 1) = c (d.first + (d.period - 1) + 1) at hhead
  rw [show d.first + (d.period - 1) + 1 = d.first + d.period by omega, dsecond] at hhead
  have hτn : e.first + k + 1 ≤ 3 * L + 1 := by omega
  have hτrun : L ≤ e.first + k + 1 ∧ e.first + k + 1 ≤ 2 * L + 1 := by omega
  have hzero : ∀ j, d.first + j < d.first + (visitCount L c s - 1) * d.period →
      word L u (d.first + j) = false := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hjp : j < d.period
      · exact hcyclezero j hjp
      · have hper := d.word_period (d.first + (j - d.period)) (by omega) (by omega)
        rw [show d.first + (j - d.period) + d.period = d.first + j by omega] at hper
        exact hper.symm.trans (ih (j - d.period) (by omega) (by omega))
  have hσfirst := d.first_le_visit hσn hσ
  have hσlast := d.visit_le_last hσn hσ
  have hτfirst := d.first_le_visit hτn hhead
  have hτlast := d.visit_le_last hτn hhead
  rcases hσout with hleft | hright
  · have hz := hzero (L - 1 - d.first) (by omega)
    rw [show d.first + (L - 1 - d.first) = L - 1 by omega, word_left_delimiter hL] at hz
    cases hz
  · have hz := hzero (2 * L + 1 - d.first) (by omega)
    rw [show d.first + (2 * L + 1 - d.first) = 2 * L + 1 by omega,
      word_right_delimiter hL] at hz
    cases hz

theorem sum_visitCount : ∑ s ∈ states L c, visitCount L c s = 3 * L + 2 := by
  simp_rw [visitCount_eq]
  rw [Finset.sum_add_distrib, sum_nvis, sum_rvis]
  omega

/-- Under a convenient sufficient numerical hypothesis, every outer state is
visited at most twice. This is the form used for the infinite subsequence. -/
theorem outer_at_most_two (hL : 2 ≤ L) (hB : 3 ≤ B) (hg : BGood L B u)
    (hnumeric : 2 * (B - 1) * (B ^ 3 + 4) < 4 * (L + 2))
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) : OuterAtMostTwo L c := by
  classical
  intro s hs
  by_contra hn
  have hv : 3 ≤ visitCount L c s := by rw [visitCount_eq]; omega
  let d := visitPattern huaw s (by omega : 2 ≤ visitCount L c s)
  have hdp : d.period < B := (d.good_bounds hg hs hv).1
  let K := cluster L c
  let O := states L c \ K
  let C := O.filter (fun t => 3 ≤ visitCount L c t)
  let N := ∑ t ∈ K, visitCount L c t
  have hKsub : K ⊆ states L c := Finset.filter_subset _ _
  have hKzero (t : S) (ht : t ∈ K) : (nvis L c t).card = 0 :=
    (Finset.mem_filter.mp ht).2
  have hOpos (t : S) (ht : t ∈ O) : 1 ≤ (nvis L c t).card := by
    obtain ⟨htS, htK⟩ := Finset.mem_sdiff.mp ht
    by_contra h
    apply htK
    exact Finset.mem_filter.mpr ⟨htS, by omega⟩
  have hCout (t : S) (ht : t ∈ C) : 1 ≤ (nvis L c t).card :=
    hOpos t (Finset.mem_filter.mp ht).1
  have hCv (t : S) (ht : t ∈ C) : 3 ≤ visitCount L c t :=
    (Finset.mem_filter.mp ht).2
  have hsurplus := outer_surplus_bound huaw hg C hCout hCv
  have hNcap : N ≤ (B - 1) * K.card := by
    calc N = ∑ t ∈ K, visitCount L c t := rfl
      _ ≤ ∑ _t ∈ K, (B - 1) := by
        apply Finset.sum_le_sum
        intro t ht
        have hh := run_only_visits_le_period hL huaw d hs t (hKzero t ht)
        omega
      _ = (B - 1) * K.card := by simp [Nat.mul_comm]
  have hNrun : N ≤ L + 2 := by
    have heq : N = ∑ t ∈ K, (rvis L c t).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [visitCount_eq, hKzero t ht, Nat.zero_add]
    rw [heq, ← sum_rvis (c := c)]
    exact Finset.sum_le_sum_of_subset hKsub
  have hOsum : (∑ t ∈ O, visitCount L c t) ≤ 2 * O.card + B ^ 3 := by
    have hpoint (t : S) : visitCount L c t ≤
        2 + (if 3 ≤ visitCount L c t then visitCount L c t - 2 else 0) := by
      split_ifs <;> omega
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ O) => hpoint t)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
    have htwo : (∑ _t ∈ O, (2 : ℕ)) = 2 * O.card := by simp [Nat.mul_comm]
    rw [htwo] at hsum
    change (∑ t ∈ O, visitCount L c t) ≤
      2 * O.card + (∑ t ∈ C, (visitCount L c t - 2)) at hsum
    omega
  have htotal : 3 * L + 2 ≤ N + 2 * O.card + B ^ 3 := by
    have hsplit := Finset.sum_sdiff (f := fun t => visitCount L c t) hKsub
    rw [sum_visitCount] at hsplit
    change (∑ t ∈ O, visitCount L c t) + N = 3 * L + 2 at hsplit
    omega
  have hq : K.card + O.card ≤ L + 2 := by
    have hh := Finset.card_sdiff_add_card_eq_card hKsub
    change O.card + K.card = (states L c).card at hh
    have hq' : (states L c).card ≤ L + 2 := hcard
    omega
  have hwtotal := Nat.mul_le_mul_left (B - 1) htotal
  have hwrun := Nat.mul_le_mul_left (B - 3) hNrun
  have hwq := Nat.mul_le_mul_left (2 * (B - 1)) hq
  have hsplitB : B - 1 = (B - 3) + 2 := by omega
  rw [hsplitB] at hwtotal hNcap hwq hnumeric
  nlinarith

end AneVsAn.BinarySeparation
