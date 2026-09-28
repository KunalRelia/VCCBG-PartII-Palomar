/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Lemma 8
  "It takes at most m/2 S-duadic hops to ensure that there is no
   S-diminishing hop."

  Source: §6 of the paper, p.61 (lines 1878-1900).

  **Line 14 of Algorithm 7** (the paper's own pseudocode — "if the vertex
  cover returned by DUADIC_HOP is smaller... update the running best")
  only ever accepts a candidate hop when it strictly shrinks the *cover*.
  The key realization is that, for any valid freeze/remove state of a
  represents table, cover size and duad count are related by an exact
  identity because:
    • every row has exactly two endpoints (Definition 14), and
    • every row is a genuine edge of `G` (it is a matching edge), so
      `VCover` forbids both of a row's endpoints being `removed`;
  hence every row contributes exactly 1 (one endpoint frozen) or exactly
  2 (a duad row) to the cover, and summing over all rows:

      |FrozenSet st| = (number of rows) + (number of duad rows)

  Since the number of rows is a fixed constant of the represents table
  (unchanged across a hop), this makes "cover strictly shrinks" and "duad
  count strictly shrinks" *literally the same statement*.
  `frozen_card_eq_rows_add_duads` (§5) proves the identity outright from
  two mild, purely structural hypotheses about the represents table
  (`TwoPerRow`, `RowsAreEdges` — both direct restatements of Definition
  14, not claims about algorithm behaviour), and `duad_decrease_from_
  cover_decrease` (§6) then reads the desired conclusion straight off it
  by `omega`.
-/

public import VCCBGPartII.thm8_lemma6_lemma7
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

/- `IsDuadRow`/`DuadRows` and the per-row `if IsDuadRow ... then 1 else 0`
   terms below need `Decidable`/`DecidablePred` instances for an arbitrary
   `Prop` (`IsDuadRow` is not syntactically decidable). Rather than thread
   `Classical.dec`/`open Classical in` through every individual
   declaration (which still leaves the *statement* of `DuadRows`,
   `DuadRows_eq_filter`, `fiber_card`, etc. unable to elaborate, since
   those need the instance before any tactic runs), we fix one global
   classical instance for this file, exactly as `RepList`
   (`reptable_ops_properties.lean`) does locally via
   `open Classical in` for the same reason. -/
attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. A general descent/pigeonhole lemma
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Descent lemma** (pure `ℕ` combinatorics): if a `ℕ`-valued sequence
    `f` starts at most `n` and strictly decreases at every index `k` where
    a predicate `p k` holds, then `p` must fail somewhere at or before
    index `n`. -/
private lemma descent_lemma :
    ∀ (n : ℕ) (f : ℕ → ℕ) (p : ℕ → Prop),
      f 0 ≤ n → (∀ k, p k → f (k + 1) < f k) → ∃ k ≤ n, ¬ p k := by
  intro n
  induction n with
  | zero =>
    intro f p hf0 hstep
    refine ⟨0, le_refl 0, ?_⟩
    intro hp0
    have h1 : f 1 < f 0 := hstep 0 hp0
    omega
  | succ n ih =>
    intro f p hf0 hstep
    by_cases hp0 : p 0
    · have hlt : f 1 < f 0 := hstep 0 hp0
      have hf0' : f 1 ≤ n := by omega
      obtain ⟨k, hk, hpk⟩ :=
        ih (fun k => f (k + 1)) (fun k => p (k + 1)) hf0' (fun k hk => hstep (k + 1) hk)
      exact ⟨k + 1, by omega, hpk⟩
    · exact ⟨0, Nat.zero_le _, hp0⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Rows and duad rows of a represents table
-- ═══════════════════════════════════════════════════════════════════════════

/-- The set of row indices actually used by `R`. -/
public abbrev RowsOf (R : RepTable G) : Finset ℕ := Finset.image R.row Finset.univ

/-- Row index `i` is currently a **duad row**: some pair of distinct
    endpoints sharing row `i` are both frozen in state `st` (reusing
    `IsDuad` from `thm6.lean` verbatim). -/
public abbrev IsDuadRow (R : RepTable G) (st : TableState G) (i : ℕ) : Prop :=
  ∃ u v : V, R.row u = i ∧ IsDuad R st u v

/-- The (finite) set of duad-row indices of the represents table `R` in
    state `st` — the paper's "rows with a duad". -/
public noncomputable abbrev DuadRows (R : RepTable G) (st : TableState G) : Finset ℕ := by
  classical
  exact (RowsOf R).filter (fun i => IsDuadRow R st i)

private lemma mem_DuadRows_iff (R : RepTable G) (st : TableState G) (i : ℕ) :
    i ∈ DuadRows R st ↔ i ∈ RowsOf R ∧ IsDuadRow R st i := by
  classical
  simp only [DuadRows, Finset.mem_filter]

private lemma DuadRows_eq_filter (R : RepTable G) (st : TableState G) :
    DuadRows R st = (RowsOf R).filter (fun i => IsDuadRow R st i) := by
  classical
  ext i; rw [mem_DuadRows_iff]

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemma 8 (numerical core)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 8** (paper, p.61, lines 1878-1900): given the sequence
    `Sseq : ℕ → TableState G` of represents-table states Algorithm 3's
    loop produces, together with the hypothesis `hstep` that performing a
    diminishing hop strictly decreases the number of duad rows — there is
    some index `k`, at most the number of duad rows `Sseq` starts with,
    at which no `S`-diminishing hop exists.

    `hstep` is proved rather than assumed in §6 below. -/
public theorem Lemma8
    (R : RepTable G) (Sseq : ℕ → TableState G)
    (hstep : ∀ k, (∃ _ : DiminishingHop R (Sseq k), True) →
      (DuadRows R (Sseq (k + 1))).card < (DuadRows R (Sseq k)).card) :
    ∃ k ≤ (DuadRows R (Sseq 0)).card, ¬ ∃ _ : DiminishingHop R (Sseq k), True :=
  descent_lemma (DuadRows R (Sseq 0)).card
    (fun k => (DuadRows R (Sseq k)).card)
    (fun k => ∃ _ : DiminishingHop R (Sseq k), True)
    (le_refl _) hstep

/-- **Lemma 8, paper's explicit `m/2 − 1` bound.** -/
public theorem Lemma8_paper_bound
    (R : RepTable G) (Sseq : ℕ → TableState G)
    (hduad_bound : (DuadRows R (Sseq 0)).card ≤ Fintype.card V / 2 - 1)
    (hstep : ∀ k, (∃ _ : DiminishingHop R (Sseq k), True) →
      (DuadRows R (Sseq (k + 1))).card < (DuadRows R (Sseq k)).card) :
    ∃ k ≤ Fintype.card V / 2 - 1, ¬ ∃ _ : DiminishingHop R (Sseq k), True := by
  obtain ⟨k, hk, hnone⟩ := Lemma8 R Sseq hstep
  exact ⟨k, hk.trans hduad_bound, hnone⟩

/-- If, in addition, `Sseq` is stationary once no S-diminishing hop is
    available, `Theorem6`/`Theorem7` apply from that point on. -/
public theorem Lemma8_stationary
    (R : RepTable G) (Sseq : ℕ → TableState G)
    (hstep : ∀ k, (∃ _ : DiminishingHop R (Sseq k), True) →
      (DuadRows R (Sseq (k + 1))).card < (DuadRows R (Sseq k)).card)
    (hstationary : ∀ k, ¬ (∃ _ : DiminishingHop R (Sseq k), True) → Sseq (k + 1) = Sseq k) :
    ∃ k ≤ (DuadRows R (Sseq 0)).card,
      ∀ k' ≥ k, ¬ ∃ _ : DiminishingHop R (Sseq k'), True := by
  obtain ⟨k, hk, hnone⟩ := Lemma8 R Sseq hstep
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  induction k' with
  | zero =>
    have : k = 0 := Nat.le_zero.mp hk'
    simpa [this] using hnone
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hkn : k ≤ n := by omega
      have hnonen : ¬ ∃ _ : DiminishingHop R (Sseq n), True := ih hkn
      have heq : Sseq (n + 1) = Sseq n := hstationary n hnonen
      rw [heq]; exact hnonen
    · have : k = n + 1 := le_antisymm hk' hge
      simpa [this] using hnone

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Two mild structural hypotheses (Definition 14, restated)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Definition 14, "two endpoints per row."** Every row index actually
    used by `R` has exactly two endpoints. This is a static fact about
    the represents table's row structure — it says nothing about how any
    algorithm behaves — and holds by construction whenever `R.row` is
    built from a perfect matching's edge list (one row per matching
    edge). -/
public abbrev TwoPerRow (R : RepTable G) : Prop :=
  ∀ i ∈ RowsOf R, ∃ u v : V,
    u ≠ v ∧ R.row u = i ∧ R.row v = i ∧ ∀ w, R.row w = i → w = u ∨ w = v

/-- **Definition 14, "a row is a matching edge."** Any two distinct
    endpoints sharing a row are joined by an edge of `G` — again a static
    fact about the represents table's construction, not about algorithm
    behaviour. -/
public abbrev RowsAreEdges (R : RepTable G) : Prop :=
  ∀ (i : ℕ) (u v : V), u ≠ v → R.row u = i → R.row v = i → G.Adj u v

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. The cover-size / duad-count identity
-- ═══════════════════════════════════════════════════════════════════════════

/-- No duad-row witness can exist at row `i` unless the row's two
    endpoints are *both* frozen — the contrapositive form used to rule
    out `IsDuadRow` in the two "exactly one endpoint frozen" cases of
    `fiber_card` below. Proved exactly as the earlier draft's
    `dh_destroys_start_duad` did, but purely from `TwoPerRow`'s row
    structure, with no reference to `dh` at all. -/
private lemma not_duad_of_not_both
    (R : RepTable G) (st : TableState G) {i : ℕ} {u v : V}
    (hne : u ≠ v) (hru : R.row u = i) (hrv : R.row v = i)
    (huniq : ∀ w, R.row w = i → w = u ∨ w = v)
    (hnb : ¬ (st.status u = Status.frozen ∧ st.status v = Status.frozen)) :
    ¬ IsDuadRow R st i := by
  rintro ⟨u', v', hru', hne', hreq', hfu', hfv'⟩
  have hrv' : R.row v' = i := by rw [← hreq']; exact hru'
  rcases huniq u' hru' with hueq | hueq <;> rcases huniq v' hrv' with hveq | hveq <;>
    subst hueq <;> subst hveq
  · exact hne' rfl
  · exact hnb ⟨hfu', hfv'⟩
  · exact hnb ⟨hfv', hfu'⟩
  · exact hne' rfl

/-- **A single row's contribution to the cover.** Row `i` (with its two
    endpoints `u, v`, `RowsAreEdges` making them `G`-adjacent) contributes
    exactly `1` frozen endpoint if it is not a duad row, or `2` if it is —
    the "not both removed" fact needed to rule out a `0`-contribution
    comes directly from `VCover` applied to the row's own edge. -/
private lemma fiber_card
    (R : RepTable G) (st : TableState G) {i : ℕ} {u v : V}
    (hne : u ≠ v) (hru : R.row u = i) (hrv : R.row v = i)
    (huniq : ∀ w, R.row w = i → w = u ∨ w = v)
    (hcov : VCover G (FrozenSet st)) (hadj : G.Adj u v) :
    ((FrozenSet st).filter (fun w => R.row w = i)).card
      = 1 + (if IsDuadRow R st i then 1 else 0) := by
  classical
  have hFSmem : ∀ w, w ∈ FrozenSet st ↔ st.status w = Status.frozen := by
    intro w; simp [FrozenSet]
  have hfilter_eq :
      (FrozenSet st).filter (fun w => R.row w = i) =
        ({u, v} : Finset V).filter (fun w => w ∈ FrozenSet st) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hwFS, hwrow⟩; exact ⟨huniq w hwrow, hwFS⟩
    · rintro ⟨hwuv, hwFS⟩
      refine ⟨hwFS, ?_⟩
      rcases hwuv with rfl | rfl
      · exact hru
      · exact hrv
  rw [hfilter_eq]
  rcases hcov hadj with huF | hvF
  · by_cases hvF2 : v ∈ FrozenSet st
    · have heq : ({u, v} : Finset V).filter (fun w => w ∈ FrozenSet st) = {u, v} := by
        apply Finset.filter_eq_self.mpr
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact huF
        · rw [Finset.mem_singleton] at hw'; subst hw'; exact hvF2
      have hduad : IsDuadRow R st i :=
        ⟨u, v, hru, hne, hru.trans hrv.symm, (hFSmem u).mp huF, (hFSmem v).mp hvF2⟩
      rw [heq, (Finset.card_eq_two.mpr ⟨u, v, hne, rfl⟩), ite_eq_left hduad]
    · have heq : ({u, v} : Finset V).filter (fun w => w ∈ FrozenSet st) = {u} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl), hwFS⟩
          · rfl
          · exact False.elim (hvF2 (by simpa using hwFS))
        · rintro rfl; exact ⟨Or.inl rfl, by simpa using huF⟩
      have hnd : ¬ IsDuadRow R st i :=
        not_duad_of_not_both R st hne hru hrv huniq (fun h => hvF2 ((hFSmem v).mpr h.2))
      rw [heq, Finset.card_singleton, ite_eq_right hnd]
  · by_cases huF2 : u ∈ FrozenSet st
    · have heq : ({u, v} : Finset V).filter (fun w => w ∈ FrozenSet st) = {u, v} := by
        apply Finset.filter_eq_self.mpr
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact huF2
        · rw [Finset.mem_singleton] at hw'; subst hw'; exact hvF
      have hduad : IsDuadRow R st i :=
        ⟨u, v, hru, hne, hru.trans hrv.symm, (hFSmem u).mp huF2, (hFSmem v).mp hvF⟩
      rw [heq, (Finset.card_eq_two.mpr ⟨u, v, hne, rfl⟩), ite_eq_left hduad]
    · have heq : ({u, v} : Finset V).filter (fun w => w ∈ FrozenSet st) = {v} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl), hwFS⟩
          · exact False.elim (huF2 (by simpa using hwFS))
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, by simpa using hvF⟩
      have hnd : ¬ IsDuadRow R st i :=
        not_duad_of_not_both R st hne hru hrv huniq (fun h => huF2 ((hFSmem u).mpr h.1))
      rw [heq, Finset.card_singleton, ite_eq_right hnd]

/-- **The cover-size / duad-count identity.** For any state `st` whose
    frozen set is a vertex cover, `|FrozenSet st| = (number of rows) +
    (number of duad rows)`. Proved by summing `fiber_card`'s per-row
    contribution over all rows via `Finset.card_eq_sum_card_fiberwise`. -/
public theorem frozen_card_eq_rows_add_duads
    (R : RepTable G) (st : TableState G)
    (htwo : TwoPerRow R) (hedges : RowsAreEdges R)
    (hcov : VCover G (FrozenSet st)) :
    (FrozenSet st).card = (RowsOf R).card + (DuadRows R st).card := by
  classical
  have hmapsto : ∀ w ∈ FrozenSet st, R.row w ∈ RowsOf R :=
    fun w _ => Finset.mem_image_of_mem _ (Finset.mem_univ w)
  rw [Finset.card_eq_sum_card_fiberwise hmapsto]
  have hpt : ∀ i ∈ RowsOf R,
      ((FrozenSet st).filter (fun w => R.row w = i)).card
        = 1 + (if IsDuadRow R st i then 1 else 0) := by
    intro i hi
    obtain ⟨u, v, hne, hru, hrv, huniq⟩ := htwo i hi
    exact fiber_card R st hne hru hrv huniq hcov (hedges i u v hne hru hrv)
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  have h1 : (∑ _i ∈ RowsOf R, (1 : ℕ)) = (RowsOf R).card := by
    simp
  have h2 : (∑ i ∈ RowsOf R, (if IsDuadRow R st i then 1 else 0)) = (DuadRows R st).card := by
    rw [DuadRows_eq_filter]
    exact (Finset.card_filter _ _).symm
  rw [h1, h2]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. `hstep` re-derived, with `hNoNewDuad` eliminated
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The duad-decrease step, now a theorem.** Given the cover-size
    identity for two states `st`, `st'` of the *same* represents table
    (so the "number of rows" term cancels), "cover strictly shrinks" and
    "duad count strictly shrinks" are literally the same fact, closed by
    `omega`. This is exactly what Algorithm 7's Line 14 checks (cover
    size), so accepting a hop there is, via this identity, exactly
    accepting a hop that decreases the duad count. -/
public theorem duad_decrease_from_cover_decrease
    (R : RepTable G) (htwo : TwoPerRow R) (hedges : RowsAreEdges R)
    (st st' : TableState G)
    (hcov : VCover G (FrozenSet st)) (hcov' : VCover G (FrozenSet st'))
    (hsmaller : (FrozenSet st').card < (FrozenSet st).card) :
    (DuadRows R st').card < (DuadRows R st).card := by
  have h1 := frozen_card_eq_rows_add_duads R st htwo hedges hcov
  have h2 := frozen_card_eq_rows_add_duads R st' htwo hedges hcov'
  omega

/-- **Lemma 8, fully derived.** `Sseq` is the sequence of represents-table
    states Algorithm 3's loop produces; `hcov` says every state along the
    way is a valid freeze/remove outcome's cover (available directly from
    `Theorem4`/`validFreezeRemove_gives_vcover` whenever `Sseq k` comes
    from an `IsValidFreezeRemove` state, as it always does by
    construction); `hSseq_step` is Algorithm 7's own Line 14 acceptance
    criterion — a diminishing hop, once found, is only kept if it
    strictly shrinks the cover, which is directly checkable from the
    algorithm's running state and requires no assumption about which
    *rows* end up duads. Everything from there to "at most (initial duad
    count) hops suffice" is proved, not assumed. -/
public theorem Lemma8_final
    (R : RepTable G) (Sseq : ℕ → TableState G)
    (htwo : TwoPerRow R) (hedges : RowsAreEdges R)
    (hcov : ∀ k, VCover G (FrozenSet (Sseq k)))
    (hSseq_step : ∀ k, (∃ _ : DiminishingHop R (Sseq k), True) →
      (FrozenSet (Sseq (k + 1))).card < (FrozenSet (Sseq k)).card) :
    ∃ k ≤ (DuadRows R (Sseq 0)).card, ¬ ∃ _ : DiminishingHop R (Sseq k), True := by
  apply Lemma8 R Sseq
  intro k hhop
  exact duad_decrease_from_cover_decrease R htwo hedges (Sseq k) (Sseq (k + 1))
    (hcov k) (hcov (k + 1)) (hSseq_step k hhop)

/-- Specializing `hcov` to its usual source: every `Sseq k` is itself a
    valid freeze/remove outcome, so its cover comes straight from
    `Theorem4`. -/
public theorem Lemma8_final_from_valid
    (R : RepTable G) (Sseq : ℕ → TableState G)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (htwo : TwoPerRow R) (hedges : RowsAreEdges R)
    (hvalid : ∀ k, IsValidFreezeRemove (Sseq k))
    (hSseq_step : ∀ k, (∃ _ : DiminishingHop R (Sseq k), True) →
      (FrozenSet (Sseq (k + 1))).card < (FrozenSet (Sseq k)).card) :
    ∃ k ≤ (DuadRows R (Sseq 0)).card, ¬ ∃ _ : DiminishingHop R (Sseq k), True :=
  Lemma8_final R Sseq htwo hedges
    (fun k => validFreezeRemove_gives_vcover hcubic hbridgeless (hvalid k)) hSseq_step

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper (p.61, lines 1878-1900, footnote 46):
  "each S-diminishing hop implies that the number of duads in the
  represents table R is decreasing" is no longer taken on the paper's own
  informal footing ("by at least one in the worst case," argued by
  analogy to bubble sort) but derived outright from the cover/duad
  identity — which is itself just Definition 14 plus the basic vertex-
  cover property, not a new assumption.
-/
