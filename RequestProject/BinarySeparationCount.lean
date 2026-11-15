import RequestProject.BinarySeparationDefs
import RequestProject.GenericWalk

/-!
# Counting states in a putative small unique walk for the binary family

The run contains `L + 2` state times, and there are `2 * L` outside times.
Once every outer state has at most two visits, the state budget leaves
at most two states confined to the run. All counting in this file is finite
and independent of the surgery arguments establishing the two-visit property.
-/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

section

variable {L : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}


def times (L : ℕ) : Finset ℕ := Finset.range (3 * L + 2)


def runTimes (L : ℕ) : Finset ℕ := Finset.Icc L (2 * L + 1)


def nonRunTimes (L : ℕ) : Finset ℕ := times L \ runTimes L


def states (L : ℕ) (c : ℕ → S) : Finset S := walkStates (3 * L + 1) c


def rvis (L : ℕ) (c : ℕ → S) (s : S) : Finset ℕ := (runTimes L).filter (fun t => c t = s)


def nvis (L : ℕ) (c : ℕ → S) (s : S) : Finset ℕ := (nonRunTimes L).filter (fun t => c t = s)

theorem runTimes_subset : runTimes L ⊆ times L := by
  intro t ht
  simp only [runTimes, Finset.mem_Icc] at ht
  simp only [times, Finset.mem_range]
  omega

theorem card_times : (times L).card = 3 * L + 2 := by simp [times]

theorem card_runTimes : (runTimes L).card = L + 2 := by
  simp only [runTimes, Nat.card_Icc]
  omega

theorem card_nonRunTimes : (nonRunTimes L).card = 2 * L := by
  rw [nonRunTimes, Finset.card_sdiff_of_subset runTimes_subset, card_times, card_runTimes]
  omega

theorem mem_states {t : ℕ} (ht : t ∈ times L) : c t ∈ states L c := by
  simp only [times, Finset.mem_range] at ht
  simp only [states, walkStates, Finset.mem_image]
  exact ⟨t, Finset.mem_range.2 (by omega), rfl⟩


theorem sum_rvis : ∑ s ∈ states L c, (rvis L c s).card = L + 2 := by
  rw [← card_runTimes (L := L)]
  exact (Finset.card_eq_sum_card_fiberwise
    (fun t ht => mem_states (runTimes_subset ht))).symm


theorem sum_nvis : ∑ s ∈ states L c, (nvis L c s).card = 2 * L := by
  rw [← card_nonRunTimes (L := L)]
  refine (Finset.card_eq_sum_card_fiberwise ?_).symm
  intro t ht
  simp only [Finset.mem_coe, nonRunTimes, Finset.mem_sdiff] at ht
  exact mem_states ht.1


def OuterAtMostTwo (L : ℕ) (c : ℕ → S) : Prop :=
  ∀ s, 1 ≤ (nvis L c s).card → (nvis L c s).card + (rvis L c s).card ≤ 2


def cluster (L : ℕ) (c : ℕ → S) : Finset S :=
  (states L c).filter (fun s => (nvis L c s).card = 0)


def onceSet (L : ℕ) (c : ℕ → S) : Finset S :=
  (states L c).filter (fun s => (nvis L c s).card = 1)


def twiceSet (L : ℕ) (c : ℕ → S) : Finset S :=
  (states L c).filter (fun s => (nvis L c s).card = 2)


def bridgeCount (L : ℕ) (c : ℕ → S) : ℕ :=
  ((onceSet L c).filter (fun s => (rvis L c s).card = 1)).card


def singleCount (L : ℕ) (c : ℕ → S) : ℕ :=
  ((onceSet L c).filter (fun s => (rvis L c s).card = 0)).card


def clusterVisits (L : ℕ) (c : ℕ → S) : ℕ :=
  ∑ s ∈ cluster L c, (rvis L c s).card

theorem nvis_card_le_two (houter : OuterAtMostTwo L c) (s : S) :
    (nvis L c s).card ≤ 2 := by
  rcases Nat.eq_zero_or_pos (nvis L c s).card with h | h
  · omega
  · have := houter s h; omega


theorem states_union (houter : OuterAtMostTwo L c) :
    states L c = (cluster L c ∪ onceSet L c) ∪ twiceSet L c := by
  ext s
  simp only [Finset.mem_union, cluster, onceSet, twiceSet, Finset.mem_filter]
  constructor
  · intro hs
    have h := nvis_card_le_two houter s
    rcases (by omega : (nvis L c s).card = 0 ∨ (nvis L c s).card = 1 ∨ (nvis L c s).card = 2)
      with h' | h' | h'
    exacts [Or.inl (Or.inl ⟨hs, h'⟩), Or.inl (Or.inr ⟨hs, h'⟩), Or.inr ⟨hs, h'⟩]
  · rintro ((⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩) <;> exact hs

theorem disj_cluster_once : Disjoint (cluster L c) (onceSet L c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hs'
  simp only [cluster, onceSet, Finset.mem_filter] at hs hs'
  omega

theorem disj_union_twice : Disjoint (cluster L c ∪ onceSet L c) (twiceSet L c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hs'
  simp only [cluster, onceSet, twiceSet, Finset.mem_union, Finset.mem_filter] at hs hs'
  omega


theorem sum_split (houter : OuterAtMostTwo L c) (g : S → ℕ) :
    ∑ s ∈ states L c, g s =
      (∑ s ∈ cluster L c, g s) + (∑ s ∈ onceSet L c, g s) + ∑ s ∈ twiceSet L c, g s := by
  rw [states_union houter, Finset.sum_union disj_union_twice,
    Finset.sum_union disj_cluster_once]


theorem count_nonrun (houter : OuterAtMostTwo L c) :
    (onceSet L c).card + 2 * (twiceSet L c).card = 2 * L := by
  have h := sum_split houter (fun s => (nvis L c s).card)
  rw [sum_nvis] at h
  have h0 : ∑ s ∈ cluster L c, (nvis L c s).card = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    simp only [cluster, Finset.mem_filter] at hs
    exact hs.2
  have h1 : ∑ s ∈ onceSet L c, (nvis L c s).card = (onceSet L c).card := by
    rw [Finset.sum_congr rfl (fun s hs => by
      simp only [onceSet, Finset.mem_filter] at hs; exact hs.2)]
    simp
  have h2 : ∑ s ∈ twiceSet L c, (nvis L c s).card = 2 * (twiceSet L c).card := by
    rw [Finset.sum_congr rfl (fun s hs => by
      simp only [twiceSet, Finset.mem_filter] at hs; exact hs.2)]
    simp [Nat.mul_comm]
  omega


theorem rvis_le_one_of_once (houter : OuterAtMostTwo L c) {s : S}
    (hs : s ∈ onceSet L c) : (rvis L c s).card ≤ 1 := by
  simp only [onceSet, Finset.mem_filter] at hs
  have := houter s (by omega)
  omega


theorem rvis_eq_zero_of_twice (houter : OuterAtMostTwo L c) {s : S}
    (hs : s ∈ twiceSet L c) : (rvis L c s).card = 0 := by
  simp only [twiceSet, Finset.mem_filter] at hs
  have := houter s (by omega)
  omega

theorem card_onceSet (houter : OuterAtMostTwo L c) :
    (onceSet L c).card = bridgeCount L c + singleCount L c := by
  classical
  rw [bridgeCount, singleCount,
    ← Finset.card_filter_add_card_filter_not
      (s := onceSet L c) (p := fun s => (rvis L c s).card = 1)]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr ?_).symm
  intro s hs
  have := rvis_le_one_of_once houter hs
  constructor <;> intro <;> omega


theorem count_run (houter : OuterAtMostTwo L c) :
    clusterVisits L c + bridgeCount L c = L + 2 := by
  classical
  have h := sum_split houter (fun s => (rvis L c s).card)
  rw [sum_rvis] at h
  have h2 : ∑ s ∈ twiceSet L c, (rvis L c s).card = 0 :=
    Finset.sum_eq_zero (fun s hs => rvis_eq_zero_of_twice houter hs)
  have h1 : ∑ s ∈ onceSet L c, (rvis L c s).card = bridgeCount L c := by
    rw [← Finset.sum_filter_add_sum_filter_not (onceSet L c) (fun s => (rvis L c s).card = 1)]
    have ha : ∑ s ∈ (onceSet L c).filter (fun s => (rvis L c s).card = 1), (rvis L c s).card
        = bridgeCount L c := by
      rw [Finset.sum_congr rfl (fun s hs => by
        simp only [Finset.mem_filter] at hs; exact hs.2)]
      simp [bridgeCount]
    have hb : ∑ s ∈ (onceSet L c).filter (fun s => ¬ (rvis L c s).card = 1),
        (rvis L c s).card = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      simp only [Finset.mem_filter] at hs
      have := rvis_le_one_of_once houter hs.1
      omega
    omega
  rw [clusterVisits]
  omega


theorem budget (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) :
    2 * (cluster L c).card + bridgeCount L c + singleCount L c ≤ 4 := by
  have hpart : (cluster L c).card + (onceSet L c).card + (twiceSet L c).card
      = (states L c).card := by
    rw [states_union houter, Finset.card_union_of_disjoint disj_union_twice,
      Finset.card_union_of_disjoint disj_cluster_once]
  have h1 := count_nonrun houter
  have h2 := card_onceSet houter
  have h3 : (states L c).card ≤ L + 2 := hcard
  omega


theorem cluster_card_le (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) : (cluster L c).card ≤ 2 := by
  have := budget houter hcard
  omega


theorem cluster_nonempty (hL : 3 ≤ L) (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) : 1 ≤ (cluster L c).card := by
  by_contra hcon
  have hz : (cluster L c).card = 0 := by omega
  have : clusterVisits L c = 0 := by
    rw [clusterVisits, Finset.card_eq_zero.1 hz, Finset.sum_empty]
  have h1 := count_run houter
  have h2 := budget houter hcard
  omega


theorem clusterVisits_ge (hL : 3 ≤ L) (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) : L ≤ clusterVisits L c := by
  have h1 := count_run houter
  have h2 := budget houter hcard
  have h3 := cluster_nonempty hL houter hcard
  omega

/-- Under the small-state assumption there are one or two states confined to the run. -/
theorem cluster_card_cases (hL : 3 ≤ L) (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) :
    (cluster L c).card = 1 ∨ (cluster L c).card = 2 := by
  have := cluster_card_le houter hcard
  have := cluster_nonempty hL houter hcard
  omega

/-- Two run-only states consume the entire state budget: every outer state is a pair. -/
theorem cluster_two_budget (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hc : (cluster L c).card = 2) :
    bridgeCount L c = 0 ∧ singleCount L c = 0 ∧
      (onceSet L c).card = 0 ∧ (twiceSet L c).card = L ∧
      clusterVisits L c = L + 2 := by
  have h1 := budget houter hcard
  have h2 := card_onceSet houter
  have h3 := count_nonrun houter
  have h4 := count_run houter
  omega

/-- In the one-state case there are at most two mixed states. -/
theorem cluster_one_budget (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hc : (cluster L c).card = 1) :
    bridgeCount L c ≤ 2 ∧
      (bridgeCount L c = 1 → singleCount L c = 1) ∧
      (bridgeCount L c = 2 → singleCount L c = 0) := by
  have h1 := budget houter hcard
  have h2 := card_onceSet houter
  have h3 := count_nonrun houter
  omega

theorem mem_nvis_iff {s : S} {t : ℕ} :
    t ∈ nvis L c s ↔ t ≤ 3 * L + 1 ∧ (t < L ∨ 2 * L + 1 < t) ∧ c t = s := by
  simp only [nvis, nonRunTimes, times, runTimes, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨ht, hout⟩, hs⟩
    exact ⟨by omega, by omega, hs⟩
  · rintro ⟨ht, hout, hs⟩
    exact ⟨⟨by omega, by omega⟩, hs⟩

theorem mem_rvis_iff {s : S} {t : ℕ} :
    t ∈ rvis L c s ↔ L ≤ t ∧ t ≤ 2 * L + 1 ∧ c t = s := by
  simp only [rvis, runTimes, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- A state belongs to the cluster exactly when every visit lies in the run. -/
theorem mem_cluster_iff {s : S} :
    s ∈ cluster L c ↔ s ∈ states L c ∧
      ∀ t, t ≤ 3 * L + 1 → c t = s → L ≤ t ∧ t ≤ 2 * L + 1 := by
  simp only [cluster, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hz⟩
    refine ⟨hs, ?_⟩
    intro t ht hct
    by_contra h
    have hm : t ∈ nvis L c s := mem_nvis_iff.mpr ⟨ht, by omega, hct⟩
    have := Finset.card_pos.mpr ⟨t, hm⟩
    omega
  · rintro ⟨hs, h⟩
    refine ⟨hs, Finset.card_eq_zero.mpr ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, hout, hct⟩ := mem_nvis_iff.mp ht
    have := h t ht hct
    omega

theorem run_state_mem_cluster_of_no_mixed (houter : OuterAtMostTwo L c)
    (hm : bridgeCount L c = 0) {t : ℕ} (ht : L ≤ t) (ht' : t ≤ 2 * L + 1) :
    c t ∈ cluster L c := by
  have hs : c t ∈ states L c := mem_states (by simp only [times, Finset.mem_range]; omega)
  have hr : 1 ≤ (rvis L c (c t)).card :=
    Finset.card_pos.mpr ⟨t, mem_rvis_iff.mpr ⟨ht, ht', rfl⟩⟩
  by_cases hn : (nvis L c (c t)).card = 0
  · exact Finset.mem_filter.mpr ⟨hs, hn⟩
  · have hbound := houter (c t) (by omega)
    have hnon : c t ∈ onceSet L c := Finset.mem_filter.mpr ⟨hs, by omega⟩
    have hbridge : c t ∈ (onceSet L c).filter (fun s => (rvis L c s).card = 1) :=
      Finset.mem_filter.mpr ⟨hnon, by omega⟩
    have : 0 < bridgeCount L c := Finset.card_pos.mpr ⟨c t, hbridge⟩
    omega

end

end AneVsAn.BinarySeparation
