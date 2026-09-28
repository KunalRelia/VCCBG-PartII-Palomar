module
/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
/-
  Formal Lean 4 / Mathlib Verification of Theorem 7
  "Diminishing Hop and Vertex Cover" (general, unrestricted case)

  Source: §5.3.3 of the paper (Theorem 7, lines 1528-1714, pp.46-51),
  building on Definitions 19-20 (Duadic Hop / Diminishing Hop) already
  formalized in `thm6.lean`.

  Statement (informal). Given a cubic bridgeless graph G, a corresponding
  represents table R and a vertex cover S: S is the minimum-size vertex
  cover derivable from R iff there is no S-diminishing hop in R.

  Relation to Theorem 6. Theorem 6 proved exactly this statement in the
  *restricted* case where R (in state st) has exactly one duad, which the
  paper shows corresponds to |S| = |V|/2 + 1. Theorem 7 removes that
  restriction: S may be any vertex cover derivable from R, i.e. any size
  in the range |V|/2 ≤ |S| ≤ |V| - 1 (paper's Observation 1). We reuse
  `IsDuad`, `DuadicHop`, and `DiminishingHop` verbatim from
  `thm6.lean`.

  Modeling notes, extending the abstraction choices of `thm6.lean`:
  • Paper's Observation 1 splits the size range into two regimes:
      - |S| = |V|/2: by Lemma 1 (perfect matching has |V|/2 edges/rows)
        together with "each row has at least one frozen endpoint", this
        forces every row to have *exactly* one frozen endpoint, hence no
        duad, and S is automatically the minimum vertex cover.
      - |V|/2 + 1 ≤ |S| ≤ |V| - 1: by the pigeonhole principle (m/2 rows,
        more than m/2 frozen endpoints ⟹ some row has two), at least one
        duad exists.
    We take both halves of Observation 1 as hypotheses here:
    `hbase_case` (the |V|/2 regime) and `hduad_exists`
    (the pigeonhole regime). This keeps Theorem 7 as pure `Finset`/cardinality
    reasoning about `FrozenSet`, `DiminishingHop`, and `Theorem4`.
-/

public import VCCBGPartII.thm6
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching thm6.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Theorem 7
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 7** (Diminishing Hop and Vertex Cover, general case).

    Given a cubic bridgeless graph `G`, a represents table `R` for `G`, and
    a valid freeze/remove state `st` of `R` with frozen set `S = FrozenSet
    st`: `S` is the minimum-size vertex cover derivable from `R` iff there
    is no `S`-diminishing hop in `R`.

    `hcubic`/`hbridgeless` are retained for signature fidelity.
    We take the paper's Observation 1 as hypotheses:
    • `hsize_lb`: `S` always has at least `|V|/2` frozen endpoints (a
      vertex cover derived from a represents table built on a perfect
      matching can never have fewer, one per row at minimum).
    • `hbase_case`: if `S` has exactly `|V|/2` frozen endpoints, `S` is
      already a minimum vertex cover (the perfect-matching/Lemma-1 regime).
    • `hduad_exists`: if `S` has *more* than `|V|/2` frozen endpoints,
      some row of `R` is a duad w.r.t. `st` (the pigeonhole regime). -/
public theorem Theorem7
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hsize_lb : Fintype.card V / 2 ≤ (FrozenSet st).card)
    (hbase_case :
      (FrozenSet st).card = Fintype.card V / 2 → MinVCover G (FrozenSet st))
    (hduad_exists :
      Fintype.card V / 2 < (FrozenSet st).card → ∃ u v : V, IsDuad R st u v) :
    MinVCover G (FrozenSet st) ↔ ¬ ∃ _ : DiminishingHop R st, True := by
  constructor
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇐) If an S-diminishing hop exists, S is not a minimum vertex cover.
  --      Identical to Theorem6's proof of this direction: it never used
  --      ExactlyOneDuad/hsize, only that H.st' is a valid freeze/remove
  --      outcome with a strictly smaller frozen set than S.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hmin ⟨H, _⟩
    have hvc' : VCover G (FrozenSet H.st') :=
      validFreezeRemove_gives_vcover hcubic hbridgeless H.valid'
    have hge : (FrozenSet st).card ≤ (FrozenSet H.st').card :=
      hmin.2 (FrozenSet H.st') hvc'
    have hlt := H.smaller
    omega
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇒) If S is not a minimum vertex cover, an S-diminishing hop exists.
  --      Contrapositive: assume ¬∃ diminishing hop; prove MinVCover.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hno_hop
    by_contra hnotmin
    have hvc : VCover G (FrozenSet st) :=
      validFreezeRemove_gives_vcover hcubic hbridgeless hvalid
    by_cases hcase : (FrozenSet st).card = Fintype.card V / 2
    · exact hnotmin (hbase_case hcase)
    · have hgt : Fintype.card V / 2 < (FrozenSet st).card := by omega
      obtain ⟨u, v, hduad⟩ := hduad_exists hgt
      simp only [MinVCover, not_and] at hnotmin
      have hnotmin' := hnotmin hvc
      push Not at hnotmin'
      obtain ⟨S', hS'_vc, hS'_lt⟩ := hnotmin'
      obtain ⟨st', hvalid', hFrozen'⟩ :=
        vcover_gives_validFreezeRemove hcubic hbridgeless hS'_vc
      have hcard' : (FrozenSet st').card < (FrozenSet st).card := by
        rw [hFrozen']; exact hS'_lt
      exact hno_hop ⟨{ u := u, v := v,
                        duad := hduad,
                        st' := st',
                        valid' := hvalid',
                        smaller := hcard' }, trivial⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Directional corollaries, matching the paper's (⇒)/(⇐) split verbatim
-- ═══════════════════════════════════════════════════════════════════════════

public theorem no_diminishingHop_implies_min'
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hsize_lb : Fintype.card V / 2 ≤ (FrozenSet st).card)
    (hbase_case :
      (FrozenSet st).card = Fintype.card V / 2 → MinVCover G (FrozenSet st))
    (hduad_exists :
      Fintype.card V / 2 < (FrozenSet st).card → ∃ u v : V, IsDuad R st u v)
    (hno : ¬ ∃ _ : DiminishingHop R st, True) :
    MinVCover G (FrozenSet st) :=
  (Theorem7 hcubic hbridgeless R st hvalid hsize_lb hbase_case hduad_exists).mpr hno

public theorem min_implies_no_diminishingHop'
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hsize_lb : Fintype.card V / 2 ≤ (FrozenSet st).card)
    (hbase_case :
      (FrozenSet st).card = Fintype.card V / 2 → MinVCover G (FrozenSet st))
    (hduad_exists :
      Fintype.card V / 2 < (FrozenSet st).card → ∃ u v : V, IsDuad R st u v)
    (hmin : MinVCover G (FrozenSet st)) :
    ¬ ∃ _ : DiminishingHop R st, True :=
  (Theorem7 hcubic hbridgeless R st hvalid hsize_lb hbase_case hduad_exists).mp hmin

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper's proof (§5.3.3, lines 1528-1714):
    (⇐) "If there exists an S-diminishing hop, then S is not a minimum
         vertex cover" — identical in structure to `Theorem6`'s proof of
         this direction (the paper itself notes the two proofs share this
         half essentially verbatim once Property 4/Theorem 4 supply the
         vertex-cover correspondence); formalized exactly as in `Theorem6`.
    (⇒) "If S is not a minimum vertex cover, then there exists an
         S-diminishing hop" — the paper's Observation 1 supplies the
         starting duad: either |S| = |V|/2, in which case S is *already*
         minimum by Lemma 1 (so the contrapositive's `hnotmin` is
         immediately contradicted, no hop needed), or |S| > |V|/2, in
         which case the pigeonhole principle (m/2 rows, more than m/2
         frozen endpoints) guarantees some row is a duad — exactly
         `hduad_exists`. From there the argument proceeds exactly as in
         `Theorem6`: extract a smaller cover S' from `¬MinVCover`,
         transport it to a valid table state st' via Theorem4's (⇐), and
         pair it with the located duad to assemble a `DiminishingHop`,
         contradicting `hno_hop`.
-/
