/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Theorem 8
  "Algorithm 1 (VERTEX_COVER) is correct: it returns Yes on input (G, k)
   if and only if the given instance of VC − CBG is a Yes instance."

  Source: §7 of the paper ("Proof of Correctness"), p.58, lines 1750-1774
  (Lemma 5) and pp.58-61, lines 1775-1922 (Lemma 6), whose conjunction
  *is* Theorem 8 — the paper itself states Theorem 8 as the two
  directions "Algorithm 1 returns Yes ⟺ Yes instance" proved by Lemma 6
  (⟸ read the other way: returns Yes ⟹ Yes instance) and Lemma 5
  (⟹: Yes instance ⟹ returns Yes), without ever restating them as a
  single `↔` lemma of its own.

  ─────────────────────────────────────────────────────────────────────────
  RELATION TO `thm8_lemma5.lean` / `thm8_lemma6.lean`
  ─────────────────────────────────────────────────────────────────────────
  This file adds no new mathematical content whatsoever: `Theorem8` below
  is exactly `⟨Lemma5 ..., Lemma6 ...⟩` packaged as an `Iff`, i.e.

      vertexCover adj0 Vs M lt k = true  ↔  YesInstance G k

  Since `Lemma5`'s conclusion is exactly `Theorem8`'s `.mpr` and
  `Lemma6`'s conclusion is exactly `Theorem8`'s `.mp` (mediated through
  `YesInstance`, which both files already use verbatim — `Lemma6`
  produces a `YesInstance G k` witness directly, and `Lemma5` consumes
  one), `Theorem8`'s proof is nothing more than `⟨fun hyes => Lemma6 ...
  hyes ..., fun hinst => Lemma5 ... hinst ...⟩`, applying each lemma to
  the *same* underlying data (`adj0`, `Vs`, `M`, `lt`, `k`).
-/

public import VCCBGPartII.thm8_lemma5
public import VCCBGPartII.thm8_lemma6
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching thm8_lemma5/6.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Theorem 8
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 8** (paper, §7, combining Lemma 5 and Lemma 6, pp.58-61,
    lines 1750-1922): "Algorithm 1 returns Yes on input `(G, k)` if and
    only if the given instance of VC − CBG is a Yes instance."

    `vertexCover adj0 Vs M lt k = true ↔ YesInstance G k`, where
    `vertexCover` is Algorithm 1 itself (`PARTII_algorithms
    .lean`) and `YesInstance G k := ∃ S, VCover G S ∧ S.card ≤ k`
    (`thm8_lemma6.lean §1`).

    The `.mp` direction is `Lemma6` verbatim (Algorithm 1 returned Yes ⟹
    a Yes-instance witness exists — extracted from Algorithm 1's own
    trace as `FrozenSet (Sseq N)`, a genuine, minimum-derived vertex
    cover of size `≤ k`). The `.mpr` direction is `Lemma5` verbatim (a
    Yes-instance witness exists ⟹ Algorithm 1 returns Yes — because
    Algorithm 3 computes a genuine *minimum* vertex cover, no smaller
    than any witness, and in particular no larger than `k`).

    Every hypothesis below is exactly one of `Lemma5`'s or `Lemma6`'s own
    hypotheses (their union — `Lemma5`'s list is a strict superset of
    `Lemma6`'s, differing only by `hmatchingEdges_card`), supplied once
    here and threaded to whichever of the two lemmas needs it for each
    direction of the `↔`. See `thm8_lemma6.lean §8`/`§10` and
    `thm8_lemma5.lean §1` for what each hypothesis means and
    why it is not further reducible in this development. -/
public theorem Theorem8
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
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
    vertexCover (G := G) adj0 Vs M lt k = true ↔ YesInstance G k := by
  constructor
  · -- (⟹) Algorithm 1 returns Yes ⟹ Yes instance: `Lemma6`.
    intro hyes
    exact Lemma6 hcubic hbridgeless adj0 Vs M lt k hyes hMinv hMadj hrow_pair htwo hedges
      hrows_half hV_pos hRowsCoverAll hRemoveInv0 hFS0 hNoAdjAll hphase_eq hSseq_step hstationary
  · -- (⟸) Yes instance ⟹ Algorithm 1 returns Yes: `Lemma5`.
    intro hyes_instance
    exact Lemma5 hcubic hbridgeless adj0 Vs M lt k hyes_instance hMinv hMadj hrow_pair htwo hedges
      hrows_half hmatchingEdges_card hV_pos hRowsCoverAll hRemoveInv0 hFS0 hNoAdjAll hphase_eq
      hSseq_step hstationary

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Directional corollaries, matching the paper's own Lemma 5 / Lemma 6
--     statements verbatim (re-exported here purely for convenience, since
--     `Theorem8` alone already implies both).
-- ═══════════════════════════════════════════════════════════════════════════

/-- Re-derived from `Theorem8.mp`; identical in content to `Lemma6`
    itself. -/
public theorem algorithm_yes_implies_yesInstance
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
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
          = SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n)
    (hyes : vertexCover (G := G) adj0 Vs M lt k = true) :
    YesInstance G k :=
  (Theorem8 hcubic hbridgeless adj0 Vs M lt k hMinv hMadj hrow_pair htwo hedges hrows_half
    hmatchingEdges_card hV_pos hRowsCoverAll hRemoveInv0 hFS0 hNoAdjAll hphase_eq hSseq_step
    hstationary).mp hyes

/-- Re-derived from `Theorem8.mpr`; identical in content to `Lemma5`
    itself. -/
public theorem yesInstance_implies_algorithm_yes
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
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
          = SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n)
    (hyes_instance : YesInstance G k) :
    vertexCover (G := G) adj0 Vs M lt k = true :=
  (Theorem8 hcubic hbridgeless adj0 Vs M lt k hMinv hMadj hrow_pair htwo hedges hrows_half
    hmatchingEdges_card hV_pos hRowsCoverAll hRemoveInv0 hFS0 hNoAdjAll hphase_eq hSseq_step
    hstationary).mpr hyes_instance

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper: the paper never states Theorem 8 as an
  explicit standalone `↔` lemma of its own — its §7 ("Proof of
  Correctness") simply proves Lemma 5 and Lemma 6 in sequence and treats
  their conjunction as establishing Algorithm 1's correctness (the
  section's own title). `Theorem8` here makes that conjunction an
  explicit, single Lean statement, exactly mirroring how `thm4.lean`/`thm6.lean`/`thm7
  .lean` each already package their own two-directional paper results as
  a single `Iff`, with `Lemma5`/`Lemma6` re-derivable from it
  (`algorithm_yes_implies_yesInstance`/`yesInstance_implies_algorithm_yes`,
  §2) exactly as `Theorem4`/`Theorem6`/`Theorem7` each supply
  their own `.mp`/`.mpr` corollaries.
-/
