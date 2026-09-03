import RequestProject.WalkTools

/-!
# The cluster and the budget (Section 5.1 of `anevsanseparationv4.tex`)

This file formalizes Section 5.1 (`sec:budget`) of `anevsanseparationv4.tex`: the partition
of the state set `Q = 𝒜 ⊔ ℬ` into the *cluster* `𝒜` (states all of whose visits are at run
times) and the rest, the counting identities `eq:count`, and the budget inequality
`eq:budget`

  `|𝒜| + (b₁ + s₀)/2 ≤ 4`,

together with `eq:vA`: `v_𝒜 = k + 6 - b₁`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The times `0,…,n` of the walk (`n = 3k+7`). -/
def times (k : ℕ) : Finset ℕ := Finset.range (3 * k + 8)

/-- The *run times* `[k, 2k+5]` of `z_k` (Section 5.1, `sec:budget`). -/
def runTimes (k : ℕ) : Finset ℕ := Finset.Icc k (2 * k + 5)

/-- The non-run times of `z_k`: the prefix times `[0,k-1]` and the tail times
`[2k+6, n]` (Section 5.1, `sec:budget`). -/
def nonRunTimes (k : ℕ) : Finset ℕ := times k \ runTimes k

/-- The set of states of the walk. -/
def states (k : ℕ) (c : ℕ → S) : Finset S := walkStates (3 * k + 7) c

/-- The run visits of a state. -/
def rvis (k : ℕ) (c : ℕ → S) (s : S) : Finset ℕ := (runTimes k).filter (fun t => c t = s)

/-- The non-run visits of a state. -/
def nvis (k : ℕ) (c : ℕ → S) (s : S) : Finset ℕ := (nonRunTimes k).filter (fun t => c t = s)

theorem runTimes_subset : runTimes k ⊆ times k := by
  intro t ht
  simp only [runTimes, Finset.mem_Icc] at ht
  simp only [times, Finset.mem_range]
  omega

theorem card_times : (times k).card = 3 * k + 8 := by simp [times]

theorem card_runTimes : (runTimes k).card = k + 6 := by
  simp only [runTimes, Nat.card_Icc]
  omega

theorem card_nonRunTimes : (nonRunTimes k).card = 2 * k + 2 := by
  rw [nonRunTimes, Finset.card_sdiff_of_subset runTimes_subset, card_times, card_runTimes]
  omega

theorem mem_states {t : ℕ} (ht : t ∈ times k) : c t ∈ states k c := by
  simp only [times, Finset.mem_range] at ht
  simp only [states, walkStates, Finset.mem_image]
  exact ⟨t, Finset.mem_range.2 (by omega), rfl⟩

/-- Summing the run visits over all states counts the `k+6` run times (`eq:count`). -/
theorem sum_rvis : ∑ s ∈ states k c, (rvis k c s).card = k + 6 := by
  rw [← card_runTimes (k := k)]
  exact (Finset.card_eq_sum_card_fiberwise
    (fun t ht => mem_states (runTimes_subset ht))).symm

/-- Summing the non-run visits over all states counts the `2k+2` non-run times
(`eq:count`). -/
theorem sum_nvis : ∑ s ∈ states k c, (nvis k c s).card = 2 * k + 2 := by
  rw [← card_nonRunTimes (k := k)]
  refine (Finset.card_eq_sum_card_fiberwise ?_).symm
  intro t ht
  simp only [Finset.mem_coe, nonRunTimes, Finset.mem_sdiff] at ht
  exact mem_states ht.1

/-- A state with at least three visits has all of them at run times: the counting form of
the Two-visit Lemma 4.5 (`lem:twovisit`). -/
theorem nvis_rvis_le (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) (s : S)
    (hs : 1 ≤ (nvis k c s).card) : (nvis k c s).card + (rvis k c s).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  -- there are three visits of `s`, one of them at a non-run time
  set V : Finset ℕ := (times k).filter (fun t => c t = s) with hV
  have hsub1 : nvis k c s ⊆ V := by
    intro t ht
    simp only [nvis, Finset.mem_filter] at ht
    exact Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 ht.1).1, ht.2⟩
  have hsub2 : rvis k c s ⊆ V := by
    intro t ht
    simp only [rvis, Finset.mem_filter] at ht
    exact Finset.mem_filter.2 ⟨runTimes_subset ht.1, ht.2⟩
  have hdisj : Disjoint (nvis k c s) (rvis k c s) := by
    refine Finset.disjoint_left.2 ?_
    intro t ht ht'
    simp only [nvis, Finset.mem_filter] at ht
    simp only [rvis, Finset.mem_filter] at ht'
    exact (Finset.mem_sdiff.1 ht.1).2 ht'.1
  have hcard : 3 ≤ V.card := by
    have : (nvis k c s ∪ rvis k c s).card ≤ V.card :=
      Finset.card_le_card (Finset.union_subset hsub1 hsub2)
    rw [Finset.card_union_of_disjoint hdisj] at this
    omega
  -- pick the smallest, the largest and an intermediate visit
  have hne : V.Nonempty := Finset.card_pos.1 (by omega)
  set t₁ := V.min' hne with ht₁
  set t₃ := V.max' hne with ht₃
  have ht₁V : t₁ ∈ V := V.min'_mem hne
  have ht₃V : t₃ ∈ V := V.max'_mem hne
  have hlt : t₁ < t₃ := by
    rcases eq_or_lt_of_le (V.min'_le t₃ ht₃V) with h | h
    · exfalso
      have : V ⊆ {t₁} := by
        intro x hx
        have h1 := V.min'_le x hx
        have h2 := V.le_max' x hx
        simp only [Finset.mem_singleton]
        omega
      have := Finset.card_le_card this
      simp at this
      omega
    · exact h
  obtain ⟨t₂, ht₂V, ht₂a, ht₂b⟩ : ∃ t₂ ∈ V, t₁ < t₂ ∧ t₂ < t₃ := by
    by_contra hno
    push_neg at hno
    have : V ⊆ {t₁, t₃} := by
      intro x hx
      have h1 := V.min'_le x hx
      have h2 := V.le_max' x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (le_antisymm h2 (hno x hx h))
    have := Finset.card_le_card this
    have hc2 : ({t₁, t₃} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    omega
  have hmem : ∀ x ∈ V, x < 3 * k + 8 ∧ c x = s := by
    intro x hx
    simp only [hV, Finset.mem_filter, times, Finset.mem_range] at hx
    exact hx
  have e1 : c t₁ = c t₂ := ((hmem _ ht₁V).2).trans ((hmem _ ht₂V).2).symm
  have e2 : c t₂ = c t₃ := ((hmem _ ht₂V).2).trans ((hmem _ ht₃V).2).symm
  have h3n : t₃ ≤ 3 * k + 7 := by have := (hmem _ ht₃V).1; omega
  obtain ⟨hlow, hhigh⟩ := twovisit_run hk huaw ht₂a ht₂b h3n e1 e2
  -- but `s` has a non-run visit, which must lie in `[t₁,t₃] ⊆ [k,2k+5]`
  have hnv : (nvis k c s).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨u, hu⟩ := hnv
  have huV : u ∈ V := hsub1 hu
  have h1 := V.min'_le u huV
  have h2 := V.le_max' u huV
  simp only [nvis, Finset.mem_filter, nonRunTimes, Finset.mem_sdiff, runTimes,
    Finset.mem_Icc] at hu
  exact hu.1.2 ⟨by omega, by omega⟩

/-- The *cluster* `𝒜` of Section 5.1 (`sec:budget`): the states all of whose visits are at
run times. -/
def cluster (k : ℕ) (c : ℕ → S) : Finset S :=
  (states k c).filter (fun s => (nvis k c s).card = 0)

/-- The states with exactly one non-run visit (the *bridges* and the *singletons* of
Section 5.1, `sec:budget`). -/
def onceSet (k : ℕ) (c : ℕ → S) : Finset S :=
  (states k c).filter (fun s => (nvis k c s).card = 1)

/-- The *doubles* of Section 5.1 (`sec:budget`): states with two non-run visits. -/
def twiceSet (k : ℕ) (c : ℕ → S) : Finset S :=
  (states k c).filter (fun s => (nvis k c s).card = 2)

/-- The number `b₁` of *bridges* (Section 5.1, `sec:budget`): states with one run visit and
one non-run visit. -/
def bridgeCount (k : ℕ) (c : ℕ → S) : ℕ :=
  ((onceSet k c).filter (fun s => (rvis k c s).card = 1)).card

/-- The number `s₀` of *singletons* (Section 5.1, `sec:budget`): states with a single
visit, at a non-run time. -/
def singleCount (k : ℕ) (c : ℕ → S) : ℕ :=
  ((onceSet k c).filter (fun s => (rvis k c s).card = 0)).card

/-- The total number `v_𝒜` of visits to cluster states (Section 5.1, `sec:budget`). -/
def clusterVisits (k : ℕ) (c : ℕ → S) : ℕ :=
  ∑ s ∈ cluster k c, (rvis k c s).card

theorem nvis_card_le_two (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) (s : S) :
    (nvis k c s).card ≤ 2 := by
  rcases Nat.eq_zero_or_pos (nvis k c s).card with h | h
  · omega
  · have := nvis_rvis_le hk huaw s h; omega

/-- The partition `Q = 𝒜 ⊔ ℱ ⊔ ℱ'` of Section 5.1 (`sec:budget`) into the cluster, the
states with one non-run visit, and the doubles. -/
theorem states_union (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) :
    states k c = (cluster k c ∪ onceSet k c) ∪ twiceSet k c := by
  ext s
  simp only [Finset.mem_union, cluster, onceSet, twiceSet, Finset.mem_filter]
  constructor
  · intro hs
    have h := nvis_card_le_two hk huaw s
    rcases (by omega : (nvis k c s).card = 0 ∨ (nvis k c s).card = 1 ∨ (nvis k c s).card = 2)
      with h' | h' | h'
    exacts [Or.inl (Or.inl ⟨hs, h'⟩), Or.inl (Or.inr ⟨hs, h'⟩), Or.inr ⟨hs, h'⟩]
  · rintro ((⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩) <;> exact hs

theorem disj_cluster_once : Disjoint (cluster k c) (onceSet k c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hs'
  simp only [cluster, onceSet, Finset.mem_filter] at hs hs'
  omega

theorem disj_union_twice : Disjoint (cluster k c ∪ onceSet k c) (twiceSet k c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hs'
  simp only [cluster, onceSet, twiceSet, Finset.mem_union, Finset.mem_filter] at hs hs'
  omega

/-- Summation split along the partition `Q = 𝒜 ⊔ ℱ ⊔ ℱ'` (Section 5.1, `sec:budget`). -/
theorem sum_split (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) (g : S → ℕ) :
    ∑ s ∈ states k c, g s =
      (∑ s ∈ cluster k c, g s) + (∑ s ∈ onceSet k c, g s) + ∑ s ∈ twiceSet k c, g s := by
  rw [states_union hk huaw, Finset.sum_union disj_union_twice,
    Finset.sum_union disj_cluster_once]

/-- The first counting identity of `eq:count`: `2f + b₁ + s₀ = 2k+2`. -/
theorem count_nonrun (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) :
    (onceSet k c).card + 2 * (twiceSet k c).card = 2 * k + 2 := by
  have h := sum_split hk huaw (fun s => (nvis k c s).card)
  rw [sum_nvis] at h
  have h0 : ∑ s ∈ cluster k c, (nvis k c s).card = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    simp only [cluster, Finset.mem_filter] at hs
    exact hs.2
  have h1 : ∑ s ∈ onceSet k c, (nvis k c s).card = (onceSet k c).card := by
    rw [Finset.sum_congr rfl (fun s hs => by
      simp only [onceSet, Finset.mem_filter] at hs; exact hs.2)]
    simp
  have h2 : ∑ s ∈ twiceSet k c, (nvis k c s).card = 2 * (twiceSet k c).card := by
    rw [Finset.sum_congr rfl (fun s hs => by
      simp only [twiceSet, Finset.mem_filter] at hs; exact hs.2)]
    simp [Nat.mul_comm]
  omega

/-- Every state with one non-run visit has at most one run visit (Lemma 4.5,
`lem:twovisit`). -/
theorem rvis_le_one_of_once (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {s : S}
    (hs : s ∈ onceSet k c) : (rvis k c s).card ≤ 1 := by
  simp only [onceSet, Finset.mem_filter] at hs
  have := nvis_rvis_le hk huaw s (by omega)
  omega

/-- A double has no run visit (Lemma 4.5, `lem:twovisit`). -/
theorem rvis_eq_zero_of_twice (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {s : S}
    (hs : s ∈ twiceSet k c) : (rvis k c s).card = 0 := by
  simp only [twiceSet, Finset.mem_filter] at hs
  have := nvis_rvis_le hk huaw s (by omega)
  omega

theorem card_onceSet (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) :
    (onceSet k c).card = bridgeCount k c + singleCount k c := by
  classical
  rw [bridgeCount, singleCount,
    ← Finset.card_filter_add_card_filter_not
      (s := onceSet k c) (p := fun s => (rvis k c s).card = 1)]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr ?_).symm
  intro s hs
  have := rvis_le_one_of_once hk huaw hs
  constructor <;> intro <;> omega

/-- The second counting identity of `eq:count`, i.e. `eq:vA`: `v_𝒜 + b₁ = k+6`. -/
theorem count_run (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) :
    clusterVisits k c + bridgeCount k c = k + 6 := by
  classical
  have h := sum_split hk huaw (fun s => (rvis k c s).card)
  rw [sum_rvis] at h
  have h2 : ∑ s ∈ twiceSet k c, (rvis k c s).card = 0 :=
    Finset.sum_eq_zero (fun s hs => rvis_eq_zero_of_twice hk huaw hs)
  have h1 : ∑ s ∈ onceSet k c, (rvis k c s).card = bridgeCount k c := by
    rw [← Finset.sum_filter_add_sum_filter_not (onceSet k c) (fun s => (rvis k c s).card = 1)]
    have ha : ∑ s ∈ (onceSet k c).filter (fun s => (rvis k c s).card = 1), (rvis k c s).card
        = bridgeCount k c := by
      rw [Finset.sum_congr rfl (fun s hs => by
        simp only [Finset.mem_filter] at hs; exact hs.2)]
      simp [bridgeCount]
    have hb : ∑ s ∈ (onceSet k c).filter (fun s => ¬ (rvis k c s).card = 1),
        (rvis k c s).card = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      simp only [Finset.mem_filter] at hs
      have := rvis_le_one_of_once hk huaw hs.1
      omega
    omega
  rw [clusterVisits]
  omega

/-- **The budget inequality `eq:budget` of Section 5.1 (`sec:budget`)**:
`2|𝒜| + b₁ + s₀ ≤ 8`, i.e. `|𝒜| + (b₁+s₀)/2 ≤ 4`. -/
theorem budget (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    2 * (cluster k c).card + bridgeCount k c + singleCount k c ≤ 8 := by
  have hpart : (cluster k c).card + (onceSet k c).card + (twiceSet k c).card
      = (states k c).card := by
    rw [states_union hk huaw, Finset.card_union_of_disjoint disj_union_twice,
      Finset.card_union_of_disjoint disj_cluster_once]
  have h1 := count_nonrun hk huaw
  have h2 := card_onceSet hk huaw
  have h3 : (states k c).card ≤ k + 5 := hcard
  omega

/-- `|𝒜| ≤ 4` (Section 5.1, `sec:budget`). -/
theorem cluster_card_le (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) : (cluster k c).card ≤ 4 := by
  have := budget hk huaw hcard
  omega

/-- The cluster is nonempty (Section 5.1, `sec:budget`). -/
theorem cluster_nonempty (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) : 1 ≤ (cluster k c).card := by
  by_contra hcon
  have hz : (cluster k c).card = 0 := by omega
  have : clusterVisits k c = 0 := by
    rw [clusterVisits, Finset.card_eq_zero.1 hz, Finset.sum_empty]
  have h1 := count_run hk huaw
  have h2 := budget hk huaw hcard
  omega

/-- `v_𝒜 ≥ k` (`eq:vA` of Section 5.1, `sec:budget`). -/
theorem clusterVisits_ge (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) : k ≤ clusterVisits k c := by
  have h1 := count_run hk huaw
  have h2 := budget hk huaw hcard
  have h3 := cluster_nonempty hk huaw hcard
  omega

end

end AneVsAn
