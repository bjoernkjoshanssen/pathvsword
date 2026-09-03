import RequestProject.WalkCount

/-!
# The cycle `γ` (Section 5.2 of `anevsanseparationv4.tex`)

This file formalizes Step 1 of the proof of Lemma 5.3 (`lem:gamma`) of
`anevsanseparationv4.tex`: some cluster state has at least five visits, its consecutive
visits are equally spaced by a common gap `ℓ = |γ|`, and the walk is `ℓ`-periodic between
the first and last of these visits.  The periodic stretch is the interval `S` of the
paper, and `ℓ ≤ |𝒜| ≤ 4`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

theorem mem_rvis {s : S} {v : ℕ} :
    v ∈ rvis k c s ↔ (k ≤ v ∧ v ≤ 2 * k + 5) ∧ c v = s := by
  simp only [rvis, Finset.mem_filter, runTimes, Finset.mem_Icc]

/-- A cluster state has all of its visits at run times (Section 5.1, `sec:budget`). -/
theorem cluster_all_visits {s : S} (hs : s ∈ cluster k c) {u : ℕ} (hu : u ≤ 3 * k + 7)
    (hcu : c u = s) : u ∈ rvis k c s := by
  by_contra hcon
  have hnr : u ∈ nonRunTimes k := by
    simp only [nonRunTimes, Finset.mem_sdiff, times, Finset.mem_range, runTimes, Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    intro hmem
    exact hcon (mem_rvis.2 ⟨by simpa [runTimes, Finset.mem_Icc] using hmem, hcu⟩)
  have : u ∈ nvis k c s := Finset.mem_filter.2 ⟨hnr, hcu⟩
  simp only [cluster, Finset.mem_filter, Finset.card_eq_zero] at hs
  rw [hs.2] at this
  simp at this

/-- **Step 1 of Lemma 5.3 (`lem:gamma`)**: the consecutive visits of a cluster state with
at least two visits are all separated by one and the same gap `ℓ ≥ 1`. -/
theorem consecutive_gap_const (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {s : S} (hs : s ∈ cluster k c) (h2 : 2 ≤ (rvis k c s).card) :
    ∃ ell, 1 ≤ ell ∧ ∀ v ∈ rvis k c s, ∀ w ∈ rvis k c s, v < w →
      (∀ x ∈ rvis k c s, ¬ (v < x ∧ x < w)) → w - v = ell := by
  classical
  set V := rvis k c s with hV
  have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
  set t₁ := V.min' hVne with ht₁
  have ht₁V : t₁ ∈ V := V.min'_mem hVne
  have hEne : (V.erase t₁).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ht₁V]
    omega
  set t₂ := (V.erase t₁).min' hEne with ht₂
  have ht₂V : t₂ ∈ V := Finset.mem_of_mem_erase ((V.erase t₁).min'_mem hEne)
  have ht₂ne : t₂ ≠ t₁ := Finset.ne_of_mem_erase ((V.erase t₁).min'_mem hEne)
  have ht₁t₂ : t₁ < t₂ := lt_of_le_of_ne (V.min'_le t₂ ht₂V) (Ne.symm ht₂ne)
  refine ⟨t₂ - t₁, by omega, ?_⟩
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hvV w hwV hvw hmid
    rcases eq_or_lt_of_le (V.min'_le v hvV) with hbase | hlt
    · -- `v` is the smallest visit, so `w` is the second one
      have hvt₁ : v = t₁ := hbase.symm
      subst hvt₁
      have hwt₂ : w = t₂ := by
        by_contra hne
        rcases Nat.lt_or_ge w t₂ with h | h
        · have : w ∈ V.erase t₁ := Finset.mem_erase.2 ⟨by omega, hwV⟩
          have := (V.erase t₁).min'_le w this
          omega
        · exact hmid t₂ ht₂V ⟨ht₁t₂, by omega⟩
      rw [hwt₂]
    · -- `v` is not the smallest visit: use the previous one
      have hPne : (V.filter (fun x => x < v)).Nonempty :=
        ⟨t₁, Finset.mem_filter.2 ⟨ht₁V, hlt⟩⟩
      set u := (V.filter (fun x => x < v)).max' hPne with hu
      have huMem := (V.filter (fun x => x < v)).max'_mem hPne
      rw [Finset.mem_filter] at huMem
      obtain ⟨huV, huv⟩ := huMem
      have hnone : ∀ x ∈ V, ¬ (u < x ∧ x < v) := by
        intro x hxV ⟨hx1, hx2⟩
        have : x ∈ V.filter (fun y => y < v) := Finset.mem_filter.2 ⟨hxV, hx2⟩
        have := (V.filter (fun y => y < v)).le_max' x this
        omega
      have hprev : v - u = t₂ - t₁ := ih u huv huV v hvV huv hnone
      -- now apply the equal-gaps lemma to `u < v < w`
      have hbounds : ∀ x ∈ V, k ≤ x ∧ x ≤ 2 * k + 5 := fun x hx => (mem_rvis.1 hx).1
      have hcv : ∀ x ∈ V, c x = s := fun x hx => (mem_rvis.1 hx).2
      have e1 : c u = c v := (hcv u huV).trans (hcv v hvV).symm
      have e2 : c v = c w := (hcv v hvV).trans (hcv w hwV).symm
      have hmid1 : ∀ x, u < x → x < v → c x ≠ c u := by
        intro x h1 h2 hcx
        have hxle : x ≤ 3 * k + 7 := by have := hbounds v hvV; omega
        have : x ∈ V := cluster_all_visits hs hxle (hcx.trans (hcv u huV))
        exact hnone x this ⟨h1, h2⟩
      have hmid2 : ∀ x, v < x → x < w → c x ≠ c v := by
        intro x h1 h2 hcx
        have hxle : x ≤ 3 * k + 7 := by have := hbounds w hwV; omega
        have : x ∈ V := cluster_all_visits hs hxle (hcx.trans (hcv v hvV))
        exact hmid x this ⟨h1, h2⟩
      have := equal_gaps hk huaw huv hvw (by have := hbounds w hwV; omega) e1 e2 hmid1 hmid2
      omega

/-- **Step 1 of Lemma 5.3 (`lem:gamma`)**: a cluster state with at least three visits
determines a period `ℓ` and a *stretch* `[t₁, t_r]` of run times on which the walk is
`ℓ`-periodic; the stretch contains `|V| - 1` full turns of the cycle `γ`. -/
theorem cluster_cycle (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {s : S} (hs : s ∈ cluster k c) (h3 : 3 ≤ (rvis k c s).card) :
    ∃ ell t₁ tr, 1 ≤ ell ∧ k ≤ t₁ ∧ tr ≤ 2 * k + 5 ∧
      t₁ + ((rvis k c s).card - 1) * ell ≤ tr ∧
      (∀ x, t₁ ≤ x → x + ell ≤ tr → c x = c (x + ell)) ∧ c t₁ = s := by
  classical
  obtain ⟨ell, hell, hgap⟩ := consecutive_gap_const hk huaw hs (by omega)
  set V := rvis k c s with hV
  have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
  set t₁ := V.min' hVne with ht₁
  set tr := V.max' hVne with htr
  have ht₁V : t₁ ∈ V := V.min'_mem hVne
  have htrV : tr ∈ V := V.max'_mem hVne
  have hbounds : ∀ x ∈ V, k ≤ x ∧ x ≤ 2 * k + 5 := fun x hx => (mem_rvis.1 hx).1
  have hcv : ∀ x ∈ V, c x = s := fun x hx => (mem_rvis.1 hx).2
  -- the successor of a visit is `ell` later
  have hsucc : ∀ v ∈ V, v < tr → v + ell ∈ V := by
    intro v hvV hvtr
    have hNe : (V.filter (fun x => v < x)).Nonempty :=
      ⟨tr, Finset.mem_filter.2 ⟨htrV, hvtr⟩⟩
    set w := (V.filter (fun x => v < x)).min' hNe with hw
    have hwMem := (V.filter (fun x => v < x)).min'_mem hNe
    rw [Finset.mem_filter] at hwMem
    obtain ⟨hwV, hvw⟩ := hwMem
    have hnone : ∀ x ∈ V, ¬ (v < x ∧ x < w) := by
      intro x hxV ⟨hx1, hx2⟩
      have hmem : x ∈ V.filter (fun y => v < y) := Finset.mem_filter.2 ⟨hxV, hx1⟩
      have := (V.filter (fun y => v < y)).min'_le x hmem
      omega
    have := hgap v hvV w hwV hvw hnone
    rw [show v + ell = w by omega]
    exact hwV
  -- the predecessor of a visit is `ell` earlier
  have hpred : ∀ v ∈ V, t₁ < v → v - ell ∈ V := by
    intro v hvV htv
    have hNe : (V.filter (fun x => x < v)).Nonempty :=
      ⟨t₁, Finset.mem_filter.2 ⟨ht₁V, htv⟩⟩
    set u := (V.filter (fun x => x < v)).max' hNe with hu
    have huMem := (V.filter (fun x => x < v)).max'_mem hNe
    rw [Finset.mem_filter] at huMem
    obtain ⟨huV, huv⟩ := huMem
    have hnone : ∀ x ∈ V, ¬ (u < x ∧ x < v) := by
      intro x hxV ⟨hx1, hx2⟩
      have hmem : x ∈ V.filter (fun y => y < v) := Finset.mem_filter.2 ⟨hxV, hx2⟩
      have := (V.filter (fun y => y < v)).le_max' x hmem
      omega
    have := hgap u huV v hvV huv hnone
    rw [show v - ell = u by omega]
    exact huV
  have ht₁k : k ≤ t₁ := (hbounds t₁ ht₁V).1
  -- every visit is `t₁` plus a multiple of `ell`
  have hdvd : ∀ v, v ∈ V → ell ∣ (v - t₁) := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hvV
      rcases eq_or_lt_of_le (V.min'_le v hvV) with hb | hlt
      · rw [show v - t₁ = 0 by omega]
        exact Dvd.intro 0 rfl
      · have hp := hpred v hvV hlt
        have hple : t₁ ≤ v - ell := V.min'_le _ hp
        obtain ⟨j, hj⟩ := ih (v - ell) (by omega) hp
        refine ⟨j + 1, ?_⟩
        rw [Nat.mul_add, Nat.mul_one]
        omega
  -- hence `V` has at most `(tr - t₁)/ell + 1` elements
  have hcardle : V.card ≤ (tr - t₁) / ell + 1 := by
    have hinj : Set.InjOn (fun v => (v - t₁) / ell) (V : Set ℕ) := by
      intro a ha b hb hab
      simp only at hab
      obtain ⟨i, hi⟩ := hdvd a ha
      obtain ⟨j, hj⟩ := hdvd b hb
      have hia : t₁ ≤ a := V.min'_le a ha
      have hib : t₁ ≤ b := V.min'_le b hb
      rw [hi, hj] at hab
      rw [Nat.mul_div_cancel_left i (by omega), Nat.mul_div_cancel_left j (by omega)] at hab
      rw [hab] at hi
      omega
    have hmaps : Set.MapsTo (fun v => (v - t₁) / ell) (V : Set ℕ)
        ((Finset.range ((tr - t₁) / ell + 1) : Finset ℕ) : Set ℕ) := by
      intro v hv
      simp only [Finset.mem_coe, Finset.mem_range] at hv ⊢
      have hvtr : v ≤ tr := V.le_max' v hv
      have := Nat.div_le_div_right (c := ell) (show v - t₁ ≤ tr - t₁ by omega)
      omega
    have := Finset.card_le_card_of_injOn (fun v => (v - t₁) / ell) hmaps hinj
    simpa using this
  have hlen : t₁ + (V.card - 1) * ell ≤ tr := by
    have h1 : (V.card - 1) ≤ (tr - t₁) / ell := by omega
    have h2 : (V.card - 1) * ell ≤ ((tr - t₁) / ell) * ell := Nat.mul_le_mul_right ell h1
    have h3 : ((tr - t₁) / ell) * ell ≤ tr - t₁ := Nat.div_mul_le_self _ _
    have h4 : t₁ ≤ tr := V.min'_le tr htrV
    omega
  -- periodicity by the Rotation Lemma 4.2 (`lem:rotation`)
  refine ⟨ell, t₁, tr, hell, (hbounds t₁ ht₁V).1, (hbounds tr htrV).2, hlen, ?_, hcv t₁ ht₁V⟩
  have hgeq : t₁ + 2 * ell ≤ tr := by
    have : (2 : ℕ) * ell ≤ (V.card - 1) * ell := Nat.mul_le_mul_right ell (by omega)
    omega
  have hA : c t₁ = c (t₁ + ell) := by
    have := hsucc t₁ ht₁V (by omega)
    exact (hcv t₁ ht₁V).trans (hcv _ this).symm
  have hB : c (tr - ell) = c (tr - ell + ell) := by
    have hp := hpred tr htrV (by omega)
    rw [show tr - ell + ell = tr by omega]
    exact (hcv _ hp).trans (hcv tr htrV).symm
  have := (rotation hk huaw (show t₁ < tr - ell by omega) hell
    (by have := (hbounds tr htrV).2; omega) hA hB).2
  intro x hx1 hx2
  exact this x hx1 (by omega)

/-- Some cluster state has at least five visits: the pigeonhole step at the beginning of
the proof of Lemma 5.3 (`lem:gamma`), using `v_𝒜 ≥ k ≥ 18` and `|𝒜| ≤ 4`. -/
theorem exists_frequent_cluster_state (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    ∃ s ∈ cluster k c, 5 ≤ (rvis k c s).card := by
  by_contra hcon
  push_neg at hcon
  have h1 : clusterVisits k c ≤ 4 * (cluster k c).card := by
    rw [clusterVisits]
    calc ∑ s ∈ cluster k c, (rvis k c s).card ≤ ∑ _s ∈ cluster k c, 4 :=
          Finset.sum_le_sum (fun s hs => by have := hcon s hs; omega)
      _ = 4 * (cluster k c).card := by rw [Finset.sum_const]; ring
  have h2 := clusterVisits_ge (by omega) huaw hcard
  have h3 := cluster_card_le (by omega) huaw hcard
  omega

/-- **Step 1 of Lemma 5.3 (`lem:gamma`)**, final form: for `k ≥ 18`, a uniquely accepting
walk with at most `k+5` states has a *stretch* of run times, of length at least four full
turns, on which the walk is periodic with some period `ℓ ≥ 1`. -/
theorem exists_stretch (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    ∃ ell t₁ tr, 1 ≤ ell ∧ k ≤ t₁ ∧ tr ≤ 2 * k + 5 ∧ t₁ + 4 * ell ≤ tr ∧
      (∀ x, t₁ ≤ x → x + ell ≤ tr → c x = c (x + ell)) := by
  obtain ⟨s, hs, h5⟩ := exists_frequent_cluster_state hk huaw hcard
  obtain ⟨ell, t₁, tr, h1, h2, h3, h4, h5', -⟩ :=
    cluster_cycle (by omega) huaw hs (by omega)
  refine ⟨ell, t₁, tr, h1, h2, h3, ?_, h5'⟩
  have : (4 : ℕ) * ell ≤ ((rvis k c s).card - 1) * ell := Nat.mul_le_mul_right ell (by omega)
  omega

omit [DecidableEq S] in
/-- Refinement of the period: if the walk is `d`-periodic on `[t₁,tr]` and two positions of
one period are visited by the same state, then the walk is already periodic with the
smaller period.  This is the formal counterpart of the primitivity argument in Step 1 of
the proof of Lemma 5.3 (`lem:gamma`). -/
theorem period_refine (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {t₁ tr d e x₀ : ℕ} (he : 1 ≤ e) (hed : e < d)
    (hlen : t₁ + 4 * d ≤ tr) (htr : tr ≤ 3 * k + 7)
    (hper : ∀ x, t₁ ≤ x → x + d ≤ tr → c x = c (x + d))
    (hx₀1 : t₁ ≤ x₀) (hx₀2 : x₀ < t₁ + d) (hx₀ : c x₀ = c (x₀ + e)) :
    ∀ y, t₁ ≤ y → y + e ≤ tr → c y = c (y + e) := by
  have h2d : x₀ + 2 * d ≤ tr := by omega
  have h1 : c x₀ = c (x₀ + 2 * d) := period_iter hper 2 x₀ hx₀1 (by omega)
  have h2 : c (x₀ + e) = c (x₀ + e + 2 * d) :=
    period_iter hper 2 (x₀ + e) (by omega) (by omega)
  have hchord2 : c (x₀ + 2 * d) = c (x₀ + 2 * d + e) := by
    rw [← h1, hx₀, h2, show x₀ + e + 2 * d = x₀ + 2 * d + e by ring]
  have hloc := (rotation hk huaw (show x₀ < x₀ + 2 * d by omega) he
    (by omega) hx₀ hchord2).2
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy1 hy2
    rcases Nat.lt_or_ge y (t₁ + 2 * d) with hsmall | hbig
    · rcases Nat.lt_or_ge y x₀ with hlt | hge
      · have ha : c y = c (y + d) := hper y hy1 (by omega)
        have hb : c (y + e) = c (y + e + d) := hper (y + e) (by omega) (by omega)
        have hc' : c (y + d) = c (y + d + e) := hloc (y + d) (by omega) (by omega)
        rw [ha, hc', ← show y + e + d = y + d + e by ring, ← hb]
      · exact hloc y hge (by omega)
    · have ha : c (y - d) = c (y - d + d) := hper (y - d) (by omega) (by omega)
      rw [show y - d + d = y by omega] at ha
      have hb : c (y - d + e) = c (y - d + e + d) := hper (y - d + e) (by omega) (by omega)
      rw [show y - d + e + d = y + e by omega] at hb
      have hc' : c (y - d) = c (y - d + e) := ih (y - d) (by omega) (by omega) (by omega)
      rw [← ha, hc', hb]

/-- **Step 1 of Lemma 5.3 (`lem:gamma`)**: the stretch may be taken with a *minimal*
period. -/
theorem exists_stretch_min (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    ∃ ell t₁ tr, 1 ≤ ell ∧ k ≤ t₁ ∧ tr ≤ 2 * k + 5 ∧ t₁ + 4 * ell ≤ tr ∧
      (∀ x, t₁ ≤ x → x + ell ≤ tr → c x = c (x + ell)) ∧
      (∀ d, 1 ≤ d → d < ell → ¬ (∀ x, t₁ ≤ x → x + d ≤ tr → c x = c (x + d))) := by
  classical
  obtain ⟨ell₀, t₁, tr, h1, h2, h3, h4, h5⟩ := exists_stretch hk huaw hcard
  have hex : ∃ d, 1 ≤ d ∧ (∀ x, t₁ ≤ x → x + d ≤ tr → c x = c (x + d)) := ⟨ell₀, h1, h5⟩
  obtain ⟨hfind1, hfind2⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ ell₀ := Nat.find_le ⟨h1, h5⟩
  refine ⟨Nat.find hex, t₁, tr, hfind1, h2, h3, ?_, hfind2, ?_⟩
  · have : 4 * Nat.find hex ≤ 4 * ell₀ := Nat.mul_le_mul_left 4 hle
    omega
  · intro d hd1 hd2 hd3
    exact Nat.find_min hex hd2 ⟨hd1, hd3⟩

/-- **Step 1 of Lemma 5.3 (`lem:gamma`)**: the states of the cycle `γ` are pairwise
distinct, so `ℓ = |γ| ≤ |𝒜| ≤ 4`. -/
theorem ell_le_four (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5)
    {ell t₁ tr : ℕ} (h1 : 1 ≤ ell) (h2 : k ≤ t₁) (h3 : tr ≤ 2 * k + 5)
    (h4 : t₁ + 4 * ell ≤ tr)
    (hper : ∀ x, t₁ ≤ x → x + ell ≤ tr → c x = c (x + ell))
    (hmin : ∀ d, 1 ≤ d → d < ell → ¬ (∀ x, t₁ ≤ x → x + d ≤ tr → c x = c (x + d))) :
    ell ≤ 4 := by
  classical
  -- the `ℓ` states of one period lie in the cluster
  have hmem : ∀ i, i < ell → c (t₁ + i) ∈ cluster k c := by
    intro i hi
    have e1 : c (t₁ + i) = c (t₁ + i + ell) := hper (t₁ + i) (by omega) (by omega)
    have e2 : c (t₁ + i + ell) = c (t₁ + i + ell + ell) :=
      hper (t₁ + i + ell) (by omega) (by omega)
    have hsub : ({t₁ + i, t₁ + i + ell, t₁ + i + ell + ell} : Finset ℕ)
        ⊆ rvis k c (c (t₁ + i)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_rvis.2 ⟨⟨by omega, by omega⟩, rfl⟩
      · exact mem_rvis.2 ⟨⟨by omega, by omega⟩, e1.symm⟩
      · exact mem_rvis.2 ⟨⟨by omega, by omega⟩, (e1.trans e2).symm⟩
    have hc3 : 3 ≤ (rvis k c (c (t₁ + i))).card := by
      have hcards : ({t₁ + i, t₁ + i + ell, t₁ + i + ell + ell} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    have hnv : (nvis k c (c (t₁ + i))).card = 0 := by
      by_contra hne
      have := nvis_rvis_le (by omega) huaw (c (t₁ + i)) (by omega)
      omega
    exact Finset.mem_filter.2 ⟨mem_states (by simp [times, Finset.mem_range]; omega), hnv⟩
  -- and they are pairwise distinct, by minimality of the period
  have hinj : ∀ i j, i < ell → j < ell → c (t₁ + i) = c (t₁ + j) → i = j := by
    have key : ∀ i j, i < j → j < ell → c (t₁ + i) = c (t₁ + j) → False := by
      intro i j hij hj hc'
      refine hmin (j - i) (by omega) (by omega) ?_
      refine period_refine (by omega) huaw (x₀ := t₁ + i) (by omega) (by omega) h4
        (by omega) hper (by omega) (by omega) ?_
      rw [show t₁ + i + (j - i) = t₁ + j by omega]
      exact hc'
    intro i j hi hj hc'
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (key i j h hj hc') (by simp)
    · exact h
    · exact absurd (key j i h hi hc'.symm) (by simp)
  have himg : (Finset.range ell).card ≤ (cluster k c).card := by
    refine Finset.card_le_card_of_injOn (fun i => c (t₁ + i)) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_range] at hi
      exact_mod_cast hmem i hi
    · intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact hinj i j hi hj hij
  have := cluster_card_le (by omega) huaw hcard
  simp only [Finset.card_range] at himg
  omega

end

end AneVsAn
