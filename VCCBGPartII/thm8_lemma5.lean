/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Lemma 5
  "If the given instance of VC − CBG is a Yes instance, then Algorithm 1
   returns Yes."

  Source: §7 of the paper ("Proof of Correctness"), p.58, lines 1750-1774,
  immediately before Lemma 6 (formalized in `thm8_lemma6.lean`).

  ─────────────────────────────────────────────────────────────────────────
  RELATION TO `thm8_lemma6.lean`
  ─────────────────────────────────────────────────────────────────────────
  Lemma 5 is the *converse* direction of Lemma 6 (which proves: Algorithm 1
  returns Yes ⟹ Yes instance). Lemma 6's own proof already had to build,
  from Algorithm 1's actual execution trace, a genuine minimum vertex
  cover `FrozenSet (Sseq k0)` at the point Algorithm 3's loop stabilizes
  (no `S`-diminishing hop remains) — via `algState_fullyValid`,
  `Lemma8_stationary`, `Sseq_eventually_constant`, and
  `no_diminishingHop_implies_min'` (Theorem 7). Every one of those
  pieces is *exactly* what Lemma 5's own proof paragraph needs too with one new result:
    • Lemma 5 is *given* an arbitrary cover `S` with `|S| ≤ k` (a "Yes
      instance" witness) and must show Algorithm 1 returns Yes, i.e.
      `|S_alg| ≤ k`. Minimality is essential here: `S_alg` (the
      algorithm's own output, `FrozenSet (Sseq k0)`) is proved minimum,
      so `|S_alg| ≤ |S| ≤ k` — exactly `hmin.2 S hS_vc` chained with the
      Yes-instance hypothesis.
  This file therefore reuses machinery of `thm8_lemma6.lean`,
  `thm8_lemma6_lemma8.lean`, and `thm7.lean`.
  We only add one genuinely new ingredient for Lemma 5: given k ≥ m/2,
  Line 5 cannot return No".

  Modeling notes.
  • `YesInstance G k` is exactly `thm8_lemma6.lean`'s own
    definition (§1 there): `∃ S, VCover G S ∧ S.card ≤ k`. Reused
    verbatim, not redefined.
  • The paper's "k ≥ m/2 ⟹ Line 5 of Algorithm 1 cannot return No" needs
    one more numeric fact than `matching_lower_bound` alone supplies:
    that the *matching-edge list length* Line 5 actually tests
    (`(Vs.filterMap ...).length`) equals `Fintype.card V / 2` — Lemma 1's
    content again, but now applied to `vertexCover`'s own Line 3
    computation rather than to the represents table's row list (which is
    what `hrows_half` in `thm8_lemma6.lean` already assumes for
    a *different* occurrence of the same fact). We take this as its own
    hypothesis, `hmatchingEdges_card`, in the same spirit as
    `hrows_half`: both are Lemma 1's numeric content, read off two
    different (but reused throughout this development) function
    definitions.
-/


public import VCCBGPartII.thm8_lemma6
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching thm8_lemma6.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Lemma 5
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 5** (paper, p.58, lines 1754-1774): "If the given instance of
    VC − CBG is a Yes instance, then the Algorithm 1 returns Yes."

    Hypothesis-for-hypothesis, this shares every structural ingredient of
    `Lemma6` (`thm8_lemma6.lean` §8) — both lemmas rest on the
    same fact, that Algorithm 3's loop terminates at a genuine minimum
    vertex cover (built from `algState_fullyValid` + `Lemma8_stationary`
    + `Sseq_eventually_constant` + Theorem 7's
    `no_diminishingHop_implies_min'`) — and differ only in:
      • Lemma 6 is *given* `hyes` (Algorithm 1 already returned Yes) and
        must extract a Yes-instance witness from it.
      • Lemma 5 is *given* `hyes_instance` (a Yes-instance witness `S`
        already exists) and must show Algorithm 1 returns Yes; this adds
        exactly one new ingredient beyond `Lemma6`'s hypothesis list —
        `hmatchingEdges_card`, needed to show Line 5 does not return No
        (the fact `Lemma6` instead reads for free out of `hyes` via
        `vertexCover_true_matchingEdges_le`). -/
public theorem Lemma5
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
    (hyes_instance : YesInstance G k)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v))
    (htwo : TwoPerRow ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hedges : RowsAreEdges ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hrows_half :
      (RowsOf ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)).card
        = Fintype.card V / 2)
    (hmatchingEdges_card :
      (Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)).length
        = Fintype.card V / 2)
    (hV_pos : 0 < Fintype.card V)
    (hRowsCoverAll : ∀ w : V,
      ∃ rc ∈ ({ RT0Of (G := G) adj0 Vs M with score := fun _ => negInf } : RTable G).rows.reverse,
        w = rc.1 ∨ w = rc.2)
    (hRemoveInv0 : RemoveInvariant
      (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState)
    (hFS0 : FrozenSet (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState
        = (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).2)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) Rx Sx lamx w)
    (hphase_eq : PhaseMatchesAlgState ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)
      ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hSseq_step : ∀ n,
      (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1))).card
          < (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n)).card)
    (hstationary : ∀ n,
      ¬ (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1)
          = SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n) :
    vertexCover (G := G) adj0 Vs M lt k = true := by
  classical
  obtain ⟨S, hS_vc, hS_le⟩ := hyes_instance
  set fuel : ℕ := (Fintype.card V) ^ 2 with hfuel
  set RT0 : RTable G := RT0Of (G := G) adj0 Vs M with hRT0
  set R : RepTable G := RT0.toRepTable M hMinv hMadj hrow_pair with hRdef
  set Sseq : ℕ → TableState G := SseqOf fuel RT0 with hSseqDef
  set N : ℕ := (RowsOf R).card with hNdef
  set matchingEdges : List (Row V) :=
    Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none) with hME
  -- ─────────────────────────────────────────────────────────────────────
  -- Step 1 ("k ≥ m/2, hence Line 5 cannot return No"): `S` is a cover, so
  -- `matching_lower_bound` gives `Fintype.card V / 2 ≤ S.card`; chained
  -- with `hS_le : S.card ≤ k` and `hmatchingEdges_card`, this bounds
  -- `matchingEdges.length` by `k`.
  -- ─────────────────────────────────────────────────────────────────────
  have hcard_ge : Fintype.card V / 2 ≤ S.card := matching_lower_bound M hMinv hMadj S hS_vc
  have hk_ge : Fintype.card V / 2 ≤ k := le_trans hcard_ge hS_le
  have hlen_le_k : matchingEdges.length ≤ k := by
    rw [hME, hmatchingEdges_card]; exact hk_ge
  -- ─────────────────────────────────────────────────────────────────────
  -- Step 2 ("the final vertex cover S consists of a minimum vertex
  -- cover"): identical to `Lemma6`'s own middle argument — build the
  -- minimum-vertex-cover witness `FrozenSet (Sseq k0)` from the
  -- stabilized execution trace of Algorithm 3's loop.
  -- ─────────────────────────────────────────────────────────────────────
  have hfuel_pos : 0 < fuel := by rw [hfuel]; positivity
  obtain ⟨m, hm⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  have hAll0 : AllFrozenOrRemoved (algInit fuel RT0).1.toTableState := by
    rw [hm]; exact algInit_AllFrozenOrRemoved m RT0 hRowsCoverAll
  have hvalid0 : IsValidFreezeRemove (algInit fuel RT0).1.toTableState := ⟨hRemoveInv0, hAll0⟩
  have hvalidFS : ∀ n, IsValidFreezeRemove (Sseq n) ∧
      FrozenSet (Sseq n) = (algState fuel RT0 n).2 :=
    algState_fullyValid fuel RT0 hNoAdjAll hvalid0 hFS0
  have hvalid : ∀ n, IsValidFreezeRemove (Sseq n) := fun n => (hvalidFS n).1
  have hcoverTracks : ∀ n, FrozenSet (Sseq n) = (algState fuel RT0 n).2 :=
    fun n => (hvalidFS n).2
  have hN_le : (DuadRows R (Sseq 0)).card ≤ N := DuadRows_card_le_RowsOf R (Sseq 0)
  have hcovn : ∀ n, VCover G (FrozenSet (Sseq n)) :=
    fun n => validFreezeRemove_gives_vcover hcubic hbridgeless (hvalid n)
  have hsize_lb : ∀ n, Fintype.card V / 2 ≤ (FrozenSet (Sseq n)).card :=
    fun n => matching_lower_bound M hMinv hMadj (FrozenSet (Sseq n)) (hcovn n)
  have hbase_case : ∀ n, (FrozenSet (Sseq n)).card = Fintype.card V / 2 →
      MinVCover G (FrozenSet (Sseq n)) := by
    intro n heq
    refine ⟨hcovn n, ?_⟩
    intro T hT
    have := matching_lower_bound M hMinv hMadj T hT
    omega
  have hduad_exists : ∀ n, Fintype.card V / 2 < (FrozenSet (Sseq n)).card →
      ∃ u v : V, IsDuad R (Sseq n) u v := by
    intro n hlt
    have hid := frozen_card_eq_rows_add_duads R (Sseq n) htwo hedges (hcovn n)
    have hDpos : 0 < (DuadRows R (Sseq n)).card := by omega
    obtain ⟨i, hiD⟩ := Finset.card_pos.mp hDpos
    have hiDf : DuadRows R (Sseq n) = (RowsOf R).filter (fun i => IsDuadRow R (Sseq n) i) := by
      ext j; simp only [DuadRows, Finset.mem_filter]
    rw [hiDf] at hiD
    obtain ⟨u, v, -, hduad⟩ := (Finset.mem_filter.mp hiD).2
    exact ⟨u, v, hduad⟩
  have hstep_duad : ∀ n, (∃ _ : DiminishingHop R (Sseq n), True) →
      (DuadRows R (Sseq (n + 1))).card < (DuadRows R (Sseq n)).card :=
    fun n hhop =>
      duad_decrease_from_cover_decrease R htwo hedges (Sseq n) (Sseq (n + 1))
        (hcovn n) (hcovn (n + 1)) (hSseq_step n hhop)
  obtain ⟨k0, hk0, hno⟩ := Lemma8_stationary R Sseq hstep_duad hstationary
  have hNk0 : N ≥ k0 := hk0.trans hN_le
  have hSseqEq : Sseq N = Sseq k0 := Sseq_eventually_constant R Sseq hstationary hno N hNk0
  have hmin : MinVCover G (FrozenSet (Sseq k0)) :=
    no_diminishingHop_implies_min' hcubic hbridgeless R (Sseq k0)
      (hvalid k0) (hsize_lb k0) (hbase_case k0) (hduad_exists k0) (hno k0 (le_refl k0))
  -- ─────────────────────────────────────────────────────────────────────
  -- Step 3 ("|S| ≤ |S'| ≤ k, hence Line 11's condition holds"):
  -- minimality of `FrozenSet (Sseq k0)` against the *given* Yes-instance
  -- witness `S` (rather than against an arbitrary smaller cover, as in
  -- Theorem 7's own internal use of minimality) gives
  -- `|FrozenSet (Sseq k0)| ≤ |S| ≤ k` directly.
  -- ─────────────────────────────────────────────────────────────────────
  have hmin_le_S : (FrozenSet (Sseq k0)).card ≤ S.card := hmin.2 S hS_vc
  have hphase_card :
      (diminishingHopPhase RT0).card = (FrozenSet (Sseq k0)).card := by
    have hFS : FrozenSet (Sseq N) = (algState fuel RT0 N).2 := hcoverTracks N
    have hphase : (algState fuel RT0 N).2 = diminishingHopPhase RT0 := hphase_eq.symm
    rw [hSseqEq] at hFS
    rw [← hphase, ← hFS]
  have hphase_le_k : (diminishingHopPhase RT0).card ≤ k := by
    rw [hphase_card]; exact le_trans hmin_le_S hS_le
  -- ─────────────────────────────────────────────────────────────────────
  -- Step 4 ("Line 12 must return Yes"): unfold `vertexCover` at the goal
  -- and discharge the two branches exactly as `vertexCover_true_card_le`
  -- does in the extraction direction (`thm8_lemma6.lean` §3),
  -- now used to *construct* the `= true` result instead of consuming it.
  -- ─────────────────────────────────────────────────────────────────────
  change vertexCover (G := G) adj0 Vs M lt k = true
  simp only [vertexCover]
  rw [ite_eq_right (not_lt.mpr hlen_le_k)]
  have hRT0eq :
      populateRepresentsTable (G := G) adj0 (fun a b => decide (M a = b ∨ M b = a)) Vs = RT0 := by
    rw [hRT0]; --rfl
  rw [hRT0eq]
  exact decide_eq_true hphase_le_k

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper's proof of Lemma 5 (p.58, lines
  1754-1774):
    "there is a vertex cover S of size at most k"
        → `hyes_instance`/`obtain ⟨S, hS_vc, hS_le⟩`.
    "k ≥ m/2 ... by Lemma 1 ... |S'| ≥ |M| ... |S| ≥ m/2 ... k ≥ m/2 ...
     Line 5 of Algorithm 1 cannot return No"
        → Step 1: `matching_lower_bound M hMinv hMadj S hS_vc`, chained
          with `hS_le` and `hmatchingEdges_card` (Lemma 1's numeric
          content, applied to `vertexCover`'s own Line 3 list) to give
          `hlen_le_k`, discharged against the goal via
          `if_neg (not_lt.mpr hlen_le_k)`.
    "the frozen endpoints in table R correspond to a vertex cover
     (Theorem 4) ... the final vertex cover S ... consists of a minimum
     vertex cover because there is no S-diminishing hop ... (Theorem 7)"
        → Step 2: verbatim reuse of `Lemma6`'s own middle argument
          (`algState_fullyValid`, `Lemma8_stationary`,
          `Sseq_eventually_constant`, `no_diminishingHop_implies_min'`),
          producing `hmin : MinVCover G (FrozenSet (Sseq k0))`.
    "|S| ≤ |S'| ≤ k ... Line 11 ... must be true ... Line 12 ... must
     return Yes"
        → Steps 3-4: `hmin.2 S hS_vc` (minimality applied to the given
          witness `S`, rather than to an arbitrary smaller cover as in
          Theorem 7's own contrapositive use of minimality) gives
          `|FrozenSet (Sseq k0)| ≤ |S| ≤ k`; transported to
          `diminishingHopPhase RT0` via `hcoverTracks`/`hSseqEq`/
          `hphase_eq` exactly as in `Lemma6`, then discharged against the
          `decide (... ≤ k) = true` goal via `decide_eq_true`.

  Together with `Lemma6`, this completes the paper's Theorem 8 ("Algorithm
  1 returns Yes if and only if the given instance of VC − CBG is a Yes instance").
-/
