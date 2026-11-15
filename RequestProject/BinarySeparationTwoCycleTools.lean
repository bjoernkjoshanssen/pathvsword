import RequestProject.BinarySeparationConfigurations
import RequestProject.BinarySeparationLayered
import RequestProject.GenericWalkTools

/-!
# Excluding the confined central two-cycle

The central two-cycle can exchange any even number of edges with a closed path
through outer states. This constrains the pairing permutation to the impossible
layered permutation described in `BinarySeparationLayered`.
-/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

variable {L : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

omit [DecidableEq S] in
theorem confined_round_seg (hL : 2 ≤ L) (htwo : ConfinedTwoCycle L c)
    {len : ℕ} (heven : len % 2 = 0) :
    Seg (3 * L + 1) c (c L) (c L) len (repit (len / 2) 2 (fun j => L + j)) := by
  have hreturn : c (L + 2) = c L := by
    simpa using htwo.2.2 2 (by omega)
  have hround := segW c (show L ≤ L + 2 by omega) (show L + 2 ≤ 3 * L + 1 by omega)
  rw [hreturn, show L + 2 - L = 2 by omega] at hround
  have hr := seg_repit hround (len / 2)
  simpa only [show len / 2 * 2 = len by omega] using hr

theorem confined_round_count_pos (_hL : 2 ≤ L) {len : ℕ} (hlen : 0 < len)
    (heven : len % 2 = 0) :
    0 < edgeCount (word L u) c len (repit (len / 2) 2 (fun j => L + j))
      (edge (word L u) c (L + 1)) := by
  have hround : 0 < edgeCount (word L u) c 2 (fun j => L + j)
      (edge (word L u) c (L + 1)) := by
    by_contra h
    have hz : edgeCount (word L u) c 2 (fun j => L + j)
        (edge (word L u) c (L + 1)) = 0 := by omega
    exact (edgeCount_eq_zero_iff.mp hz 1 (by omega)) rfl
  have heq := edgeCount_repit (x := word L u) (c := c) (len / 2) 2
    (fun j => L + j) (edge (word L u) c (L + 1))
  rw [show len / 2 * 2 = len by omega] at heq
  rw [heq]
  exact Nat.mul_pos (by omega) hround

theorem outer_itinerary_count_zero (htwo : ConfinedTwoCycle L c)
    {len : ℕ} {τ : ℕ → ℕ}
    (hbound : ∀ j, j < len → τ j ≤ 3 * L + 1)
    (hout : ∀ j, j < len → τ j < L ∨ 2 * L + 1 < τ j) :
    edgeCount (word L u) c len τ (edge (word L u) c (L + 1)) = 0 := by
  apply edgeCount_eq_zero_iff.mpr
  intro j hj heq
  have hc : c (τ j) = c (L + 1) := congrArg Prod.fst heq
  have hconf := htwo.2.1 (τ j) (hbound j hj) (Or.inr hc)
  have ho := hout j hj
  omega

theorem same_side_chord_odd (hL : 2 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    {a b : ℕ} (hab : a < b) (hbn : b ≤ 3 * L + 1)
    (hside : b < L ∨ 2 * L + 1 < a) (hchord : c a = c b) : (b - a) % 2 = 1 := by
  have hmod : (b - a) % 2 < 2 := Nat.mod_lt _ (by omega)
  by_contra hn
  have heven : (b - a) % 2 = 0 := by omega
  have hseg := confined_round_seg hL htwo heven
  have hex := exchange_one huaw (show a ≤ b by omega) hbn
    (show L ≤ 3 * L + 1 by omega) hchord (show L ≤ a ∨ b ≤ L by omega)
    hseg (edge (word L u) c (L + 1))
  have hz : edgeCount (word L u) c (b - a) (fun j => a + j)
      (edge (word L u) c (L + 1)) = 0 := by
    apply outer_itinerary_count_zero htwo
    · intro j hj; omega
    · intro j hj; omega
  have hp := confined_round_count_pos (u := u) (c := c) hL (show 0 < b - a by omega) heven
  omega

theorem no_simultaneous_side_chords (hL : 2 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    {a b s t : ℕ} (hab : a < b) (hb : b < L)
    (hs : 2 * L + 1 < s) (hst : s < t) (ht : t ≤ 3 * L + 1)
    (habc : c a = c b) (hstc : c s = c t) : False := by
  have hodd1 := same_side_chord_odd hL huaw htwo hab (by omega) (Or.inl hb) habc
  have hodd2 := same_side_chord_odd hL huaw htwo hst ht (Or.inr hs) hstc
  have heven : ((b - a) + (t - s)) % 2 = 0 := by omega
  have hseg := confined_round_seg hL htwo heven
  have hex := exchange_two_between huaw (show a ≤ b by omega)
    (show b ≤ L by omega) (show L ≤ s by omega) (show s ≤ t by omega)
    ht habc hstc hseg (edge (word L u) c (L + 1))
  have hz1 : edgeCount (word L u) c (b - a) (fun j => a + j)
      (edge (word L u) c (L + 1)) = 0 := by
    apply outer_itinerary_count_zero htwo
    · intro j hj; omega
    · intro j hj; omega
  have hz2 : edgeCount (word L u) c (t - s) (fun j => s + j)
      (edge (word L u) c (L + 1)) = 0 := by
    apply outer_itinerary_count_zero htwo
    · intro j hj; omega
    · intro j hj; omega
  have hp := confined_round_count_pos (u := u) (c := c) hL
    (show 0 < (b - a) + (t - s) by omega) heven
  omega

theorem no_short_even_outer_closed (_hL : 2 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    {a len : ℕ} {τ : ℕ → ℕ} (ha : a < L) (hlen : 0 < len) (hlenL : len ≤ L)
    (heven : len % 2 = 0) (hseg : Seg (3 * L + 1) c (c a) (c a) len τ)
    (hzero : edgeCount (word L u) c len τ (edge (word L u) c (L + 1)) = 0) : False := by
  have hreturn : c (L + len) = c L := by
    simpa only [heven, ite_true] using htwo.2.2 len (by omega)
  have hseg' : Seg (3 * L + 1) c (c a) (c a) (L + len - L) τ := by
    simpa only [show L + len - L = len by omega] using hseg
  have hex := exchange_one huaw (show L ≤ L + len by omega)
    (show L + len ≤ 3 * L + 1 by omega) (show a ≤ 3 * L + 1 by omega)
    hreturn.symm (Or.inl (show a ≤ L by omega)) hseg'
    (edge (word L u) c (L + 1))
  rw [show L + len - L = len by omega, hzero] at hex
  exact (edgeCount_eq_zero_iff.mp hex 1 (by omega)) rfl

theorem outer_closed_constraints (hL : 2 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    {a len : ℕ} {τ : ℕ → ℕ} (ha : a < L) (hlen : 0 < len) (hlenL : len ≤ L)
    (hseg : Seg (3 * L + 1) c (c a) (c a) len τ)
    (hzero : edgeCount (word L u) c len τ (edge (word L u) c (L + 1)) = 0) :
    len % 2 = 1 ∧ L < 2 * len := by
  constructor
  · have hm : len % 2 < 2 := Nat.mod_lt _ (by omega)
    by_contra hn
    exact no_short_even_outer_closed hL huaw htwo ha hlen hlenL (by omega) hseg hzero
  · by_contra hn
    have hseg2 := seg_repit hseg 2
    have hzero2 : edgeCount (word L u) c (2 * len) (repit 2 len τ)
        (edge (word L u) c (L + 1)) = 0 := by
      rw [edgeCount_repit, hzero, Nat.mul_zero]
    exact no_short_even_outer_closed hL huaw htwo ha (by omega) (by omega)
      (by omega) hseg2 hzero2

def shortenedCrossItinerary (L s j : ℕ) : ℕ → ℕ :=
  cat (L - s + (1 + 2 * j))
    (cat (L - s) (fun k => s + k) (fun k => L + k)) (fun k => 2 * L + 1 + k)

theorem shortenedCrossItinerary_zero {s j : ℕ} (hs : s < L) :
    shortenedCrossItinerary L s j 0 = s := by
  simp [shortenedCrossItinerary, cat, show 0 < L - s by omega,
    show 0 < L - s + (1 + 2 * j) by omega]

omit [DecidableEq S] in
theorem shortened_cross_seg (hL : 2 ≤ L) (heven : L % 2 = 0)
    (htwo : ConfinedTwoCycle L c) {s t j : ℕ}
    (hs : s < L) (ht : 2 * L + 2 ≤ t) (htn : t ≤ 3 * L + 1)
    (hj : 2 * j ≤ L) (hpair : c s = c t) :
    Seg (3 * L + 1) c (c s) (c s) (t - s - L + 2 * j)
      (shortenedCrossItinerary L s j) := by
  have hright : c (2 * L + 1) = c (L + 1) := by
    have hh := htwo.2.2 (L + 1) (by omega)
    have hm : (L + 1) % 2 = 1 := by omega
    simpa only [hm, show ¬(1 : ℕ) = 0 by omega, ite_false,
      show L + (L + 1) = 2 * L + 1 by omega] using hh
  have hmidend : c (L + (1 + 2 * j)) = c (L + 1) := by
    have hh := htwo.2.2 (1 + 2 * j) (by omega)
    have hm : (1 + 2 * j) % 2 = 1 := by omega
    simpa only [hm, show ¬(1 : ℕ) = 0 by omega, ite_false] using hh
  have hpre := segW c (show s ≤ L by omega) (show L ≤ 3 * L + 1 by omega)
  have hmid := segW c (show L ≤ L + (1 + 2 * j) by omega)
    (show L + (1 + 2 * j) ≤ 3 * L + 1 by omega)
  rw [hmidend, show L + (1 + 2 * j) - L = 1 + 2 * j by omega] at hmid
  have hpost := segW c (show 2 * L + 1 ≤ t by omega) htn
  rw [hright, ← hpair] at hpost
  have hall := seg_cat (seg_cat hpre hmid) hpost
  have hlen : L - s + (1 + 2 * j) + (t - (2 * L + 1)) = t - s - L + 2 * j := by omega
  simpa only [hlen, shortenedCrossItinerary] using hall

omit [DecidableEq S] in
/-- Tripling the shortened enclosing path forbids any cross-pair span at most
`3L/2`. This bound suffices for the three-block endgame. -/
theorem cross_chord_span_large (hL : 2 ≤ L) (heven : L % 2 = 0)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    {s t : ℕ} (hs : s < L) (ht : 2 * L + 2 ≤ t) (htn : t ≤ 3 * L + 1)
    (hpair : c s = c t)
    (hvis : ∀ v, v ≤ 3 * L + 1 → c v = c s → v = s ∨ v = t) :
    3 * L < 2 * (t - s) := by
  by_contra hbad
  let d := t - s
  let j := (3 * L - 2 * d) / 2
  have hd : L + 3 ≤ d := by dsimp [d]; omega
  have hdL : 2 * d ≤ 3 * L := by dsimp [d]; omega
  have hj : 2 * j ≤ L := by dsimp [j]; omega
  have hjlen : 2 * j = 3 * L - 2 * d := by dsimp [j]; omega
  have hshort := shortened_cross_seg hL heven htwo hs ht htn hj hpair
  have hzero := shortened_cross_seg hL heven htwo hs ht htn (j := 0) (by omega) hpair
  simp only [Nat.mul_zero, Nat.add_zero] at hzero
  change Seg (3 * L + 1) c (c s) (c s) (d - L + 2 * j)
    (shortenedCrossItinerary L s j) at hshort
  change Seg (3 * L + 1) c (c s) (c s) (d - L)
    (shortenedCrossItinerary L s 0) at hzero
  have hall := seg_cat (seg_cat hshort hzero) hzero
  have hlen : d - L + 2 * j + (d - L) + (d - L) = t - s := by dsimp [d] at *; omega
  rw [hlen] at hall
  have he := seg_spec huaw (show s ≤ t by omega) htn
    (by simpa only [← hpair] using hall) (d - L + 2 * j) (by omega)
  rw [cat_lt (show d - L + 2 * j < d - L + 2 * j + (d - L) by omega),
    cat_ge (show ¬d - L + 2 * j < d - L + 2 * j by omega), Nat.sub_self,
    shortenedCrossItinerary_zero hs] at he
  have hc : c (s + (d - L + 2 * j)) = c s := (congrArg Prod.fst he).symm
  have hv := hvis (s + (d - L + 2 * j)) (by omega) hc
  dsimp [d] at *
  omega

end AneVsAn.BinarySeparation
