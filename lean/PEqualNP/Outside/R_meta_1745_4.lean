import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves PEqualNP.BlindGate

theorem PEqualNP.Outside.R_meta_1745_4
    (cert : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A, let gs := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ)
        gs.length ≤ 3 ∧ (gs.length = 3 → ∀ g ∈ gs, g.op = GateOp.or)) →
      ∃ v ∉ A, ∃ D : Fin 5 → Circuit,
        FanInTwo (D 0) ∧ (D 0).size ≤ C.size ∧ circuitFun n (D 0) = circuitFun n C ∧
        ∀ i : Fin 4, let B := D i.castSucc
          ∃ j < B.size, ∃ p < n + j, D i.succ = eraseGate n B j p ∧
            ((∀ x : Fin n → Bool, x v = false → wireValue B n x (n+j) = wireValue B n x p) ∨
             (B.output ≠ n+j ∧ ∀ k, j < k → n+j ∉ gateInputs B k)))
    (replay : ∀ (n k : ℕ) (v : Fin n) (D : Fin (k+1) → Circuit), FanInTwo (D 0) →
      (∀ i : Fin k, let B := D i.castSucc
        ∃ j < B.size, ∃ p < n+j, D i.succ = eraseGate n B j p ∧
          ((∀ x : Fin n → Bool, x v = false → wireValue B n x (n+j) = wireValue B n x p) ∨
           (B.output ≠ n+j ∧ ∀ t, j < t → n+j ∉ gateInputs B t))) →
      ∃ s, s+k ≤ (D 0).size ∧
        HasCircuitSize n (fun x => circuitFun n (D 0) (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro n G A f C deg girth isolated edge hf fan computes least readers
  let _ : DecidableRel G.Adj := Classical.decRel _
  have hmin : IsMinimalCircuit n C := by
    refine ⟨fan, ?_⟩
    intro E hE he
    exact least _ ⟨E, hE, le_rfl, congrFun (he.trans computes)⟩
  have hg : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (f x = true) ↔
      (decide (∃ a ∈ A, x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hf x
  obtain ⟨v, hv, D, hd, hsize, heq, steps⟩ :=
    cert n G A C deg girth isolated edge hmin (computes.trans hg) readers
  obtain ⟨s, hs, h⟩ := replay n 4 v D hd steps
  exact ⟨v, hv, s, hs.trans hsize, by simpa only [heq, computes] using h⟩
