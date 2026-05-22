import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

open Finset
open SimpleGraph

namespace ExtremalCounterexample

/-! Concrete forbidden subgraph predicates. -/

def ContainsTwoEdgeStar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ b ≠ c

def ContainsTwoDisjointEdges {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d, G.Adj a b ∧ G.Adj c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

/-! Extremal maximum over all simple graphs on `Fin n` satisfying a property. -/

open Classical in
noncomputable def extremalNumberFor (n : Nat) (p : SimpleGraph (Fin n) → Prop) : Nat :=
  (Finset.univ.filter p).sup (fun G => #G.edgeFinset)

lemma extremalNumberFor_le {n m : Nat} {p : SimpleGraph (Fin n) → Prop}
    (h : ∀ G : SimpleGraph (Fin n), p G → #G.edgeFinset ≤ m) :
    extremalNumberFor n p ≤ m := by
  classical
  rw [extremalNumberFor]
  refine Finset.sup_le ?_
  intro G hG
  convert h G (Finset.mem_filter.mp hG).2

lemma le_extremalNumberFor {n : Nat} {p : SimpleGraph (Fin n) → Prop}
    (G : SimpleGraph (Fin n)) (hG : p G) :
    #G.edgeFinset ≤ extremalNumberFor n p := by
  classical
  rw [extremalNumberFor]
  convert Finset.le_sup (s := Finset.univ.filter p)
    (f := fun G : SimpleGraph (Fin n) => #G.edgeFinset) (b := G) ?_
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ G, hG⟩

/-! A matching on `Fin n` with `⌊n / 2⌋` edges. -/

def pairLeft (n : Nat) (i : Fin (n / 2)) : Fin n :=
  ⟨2 * i.val, by
    have hi : i.val + 1 ≤ n / 2 := Nat.succ_le_of_lt i.isLt
    have hmul : 2 * (i.val + 1) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hi
    have hdiv : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    omega⟩

def pairRight (n : Nat) (i : Fin (n / 2)) : Fin n :=
  ⟨2 * i.val + 1, by
    have hi : i.val + 1 ≤ n / 2 := Nat.succ_le_of_lt i.isLt
    have hmul : 2 * (i.val + 1) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hi
    have hdiv : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    omega⟩

def pairEdge (n : Nat) (i : Fin (n / 2)) : Sym2 (Fin n) :=
  s(pairLeft n i, pairRight n i)

set_option linter.flexible false in
lemma pairEdge_injective (n : Nat) : Function.Injective (pairEdge n) := by
  intro i j h
  simp [pairEdge, Sym2.eq] at h
  rcases h with h | h
  · apply Fin.ext
    exact Nat.mul_left_cancel (by decide : 0 < 2) (congr_arg Fin.val h.1)
  · have bad : 2 * i.val = 2 * j.val + 1 := congr_arg Fin.val h.1
    omega

def pairEdgeFinset (n : Nat) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (pairEdge n)

def pairMatching (n : Nat) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (pairEdgeFinset n : Set (Sym2 (Fin n)))

lemma pairLeft_injective (n : Nat) : Function.Injective (pairLeft n) := by
  intro i j h
  apply Fin.ext
  exact Nat.mul_left_cancel (by decide : 0 < 2) (congr_arg Fin.val h)

lemma pairRight_injective (n : Nat) : Function.Injective (pairRight n) := by
  intro i j h
  apply Fin.ext
  have : 2 * i.val + 1 = 2 * j.val + 1 := congr_arg Fin.val h
  omega

lemma pairLeft_ne_pairRight_of (n : Nat) (i j : Fin (n / 2)) :
    pairLeft n i ≠ pairRight n j := by
  intro h
  have : 2 * i.val = 2 * j.val + 1 := congr_arg Fin.val h
  omega

lemma pairRight_ne_pairLeft_of (n : Nat) (i j : Fin (n / 2)) :
    pairRight n i ≠ pairLeft n j := by
  exact (pairLeft_ne_pairRight_of n j i).symm

lemma pairEdge_not_diag (n : Nat) (i : Fin (n / 2)) :
    ¬ (pairEdge n i).IsDiag := by
  rw [pairEdge, Sym2.mk_isDiag_iff]
  intro h
  have : 2 * i.val = 2 * i.val + 1 := congr_arg Fin.val h
  omega

lemma pairMatching_edgeFinset (n : Nat) :
    (pairMatching n).edgeFinset = pairEdgeFinset n := by
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [pairMatching, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Sym2.mem_diagSet]
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [pairEdgeFinset] at h
    rcases Finset.mem_image.mp h with ⟨i, _, rfl⟩
    exact pairEdge_not_diag n i

lemma pairMatching_card (n : Nat) :
    #(pairMatching n).edgeFinset = n / 2 := by
  rw [pairMatching_edgeFinset, pairEdgeFinset]
  rw [Finset.card_image_of_injective]
  · simp
  · exact pairEdge_injective n

set_option linter.flexible false in
lemma pairMatching_adj_iff (n : Nat) (a b : Fin n) :
    (pairMatching n).Adj a b ↔
      ∃ i : Fin (n / 2),
        (a = pairLeft n i ∧ b = pairRight n i) ∨
          (a = pairRight n i ∧ b = pairLeft n i) := by
  constructor
  · intro h
    rw [pairMatching, SimpleGraph.fromEdgeSet_adj] at h
    rcases (by simpa [pairEdgeFinset] using h.1) with ⟨i, hi⟩
    use i
    rw [pairEdge] at hi
    simp [Sym2.eq] at hi
    rcases hi with hi | hi
    · exact Or.inl ⟨hi.1.symm, hi.2.symm⟩
    · exact Or.inr ⟨hi.2.symm, hi.1.symm⟩
  · rintro ⟨i, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · rw [pairMatching, SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [pairEdgeFinset, pairEdge]
        use i
        exact Or.inl ⟨rfl, rfl⟩
      · exact pairLeft_ne_pairRight_of n i i
    · rw [pairMatching, SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [pairEdgeFinset, pairEdge]
        use i
        exact Or.inr ⟨rfl, rfl⟩
      · exact pairRight_ne_pairLeft_of n i i

lemma pairMatching_unique_neighbor {n : Nat} {a b c : Fin n}
    (hab : (pairMatching n).Adj a b) (hac : (pairMatching n).Adj a c) : b = c := by
  rcases (pairMatching_adj_iff n a b).1 hab with ⟨i, hi | hi⟩
  · rcases hi with ⟨rfl, rfl⟩
    rcases (pairMatching_adj_iff n (pairLeft n i) c).1 hac with ⟨j, hj | hj⟩
    · rcases hj with ⟨hleft, rfl⟩
      have hij : i = j := pairLeft_injective n hleft
      rw [hij]
    · rcases hj with ⟨hbad, _⟩
      exact (pairLeft_ne_pairRight_of n i j hbad).elim
  · rcases hi with ⟨rfl, rfl⟩
    rcases (pairMatching_adj_iff n (pairRight n i) c).1 hac with ⟨j, hj | hj⟩
    · rcases hj with ⟨hbad, _⟩
      exact (pairRight_ne_pairLeft_of n i j hbad).elim
    · rcases hj with ⟨hright, rfl⟩
      have hij : i = j := pairRight_injective n hright
      rw [hij]

lemma pairMatching_free_twoEdgeStar (n : Nat) :
    ¬ ContainsTwoEdgeStar (pairMatching n) := by
  rintro ⟨a, b, c, hab, hac, hbc⟩
  exact hbc (pairMatching_unique_neighbor hab hac)

/-! A star with `n - 1` edges. -/

def starCenter (n : Nat) (hn : 0 < n) : Fin n := ⟨0, hn⟩

def starEdgeFinset (n : Nat) (hn : 0 < n) : Finset (Sym2 (Fin n)) :=
  (Finset.univ.erase (starCenter n hn)).image (fun v => s(starCenter n hn, v))

def starGraph (n : Nat) (hn : 0 < n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (starEdgeFinset n hn : Set (Sym2 (Fin n)))

set_option linter.flexible false in
lemma star_edge_injective (n : Nat) (hn : 0 < n) :
    Set.InjOn (fun v => s(starCenter n hn, v))
      (Finset.univ.erase (starCenter n hn) : Set (Fin n)) := by
  intro v hv _w hw h
  have hvn : v ≠ starCenter n hn := by simpa using hv
  simp [Sym2.eq] at h
  rcases h with h | h
  · exact h
  · exact (hvn h.2).elim

lemma starEdgeFinset_card (n : Nat) (hn : 0 < n) :
    #(starEdgeFinset n hn) = n - 1 := by
  rw [starEdgeFinset]
  rw [Finset.card_image_of_injOn]
  · simp
  · exact star_edge_injective n hn

lemma star_edge_not_diag (n : Nat) (hn : 0 < n) {v : Fin n}
    (hv : v ∈ Finset.univ.erase (starCenter n hn)) :
    ¬ s(starCenter n hn, v).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  have hvn : v ≠ starCenter n hn := by simpa using hv
  exact hvn.symm

lemma starGraph_edgeFinset (n : Nat) (hn : 0 < n) :
    (starGraph n hn).edgeFinset = starEdgeFinset n hn := by
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [starGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Sym2.mem_diagSet]
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [starEdgeFinset] at h
    rcases Finset.mem_image.mp h with ⟨v, hv, rfl⟩
    exact star_edge_not_diag n hn hv

lemma starGraph_card (n : Nat) (hn : 0 < n) :
    #(starGraph n hn).edgeFinset = n - 1 := by
  rw [starGraph_edgeFinset, starEdgeFinset_card]

set_option linter.flexible false in
lemma starGraph_adj_iff (n : Nat) (hn : 0 < n) (a b : Fin n) :
    (starGraph n hn).Adj a b ↔
      (a = starCenter n hn ∧ b ≠ starCenter n hn) ∨
        (b = starCenter n hn ∧ a ≠ starCenter n hn) := by
  constructor
  · intro h
    rw [starGraph, SimpleGraph.fromEdgeSet_adj] at h
    rcases (by simpa [starEdgeFinset] using h.1) with ⟨v, hv, hvab⟩
    have hvn : v ≠ starCenter n hn := by simpa using hv
    rcases hvab with hvab | hvab
    · exact Or.inl ⟨hvab.1.symm, by intro hb; exact hvn (hvab.2.trans hb)⟩
    · exact Or.inr ⟨hvab.1.symm, by intro ha; exact hvn (hvab.2.trans ha)⟩
  · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
    · rw [starGraph, SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [starEdgeFinset]
        exact ⟨b, by simpa using hb, by simp⟩
      · exact hb.symm
    · rw [starGraph, SimpleGraph.fromEdgeSet_adj]
      constructor
      · simp [starEdgeFinset]
        refine ⟨a, by simpa using ha, ?_⟩
        exact Or.inr rfl
      · exact ha

lemma starGraph_free_twoDisjointEdges (n : Nat) (hn : 0 < n) :
    ¬ ContainsTwoDisjointEdges (starGraph n hn) := by
  rintro ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd⟩
  rcases (starGraph_adj_iff n hn a b).1 hab with hab' | hab'
  · rcases hab' with ⟨rfl, _⟩
    rcases (starGraph_adj_iff n hn c d).1 hcd with hcd' | hcd'
    · exact hac hcd'.1.symm
    · exact had hcd'.1.symm
  · rcases hab' with ⟨rfl, _⟩
    rcases (starGraph_adj_iff n hn c d).1 hcd with hcd' | hcd'
    · exact hbc hcd'.1.symm
    · exact hbd hcd'.1.symm

/-! A single edge, used for the family lower bound. -/

def firstVertex (n : Nat) (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

def secondVertex (n : Nat) (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

lemma first_ne_second (n : Nat) (hn : 2 ≤ n) :
    firstVertex n hn ≠ secondVertex n hn := by
  intro h
  have : (0 : Nat) = 1 := congr_arg Fin.val h
  omega

def singleEdgeGraph (n : Nat) (hn : 2 ≤ n) : SimpleGraph (Fin n) :=
  SimpleGraph.edge (firstVertex n hn) (secondVertex n hn)

lemma singleEdge_adj_iff (n : Nat) (hn : 2 ≤ n) (a b : Fin n) :
    (singleEdgeGraph n hn).Adj a b ↔
      (a = firstVertex n hn ∧ b = secondVertex n hn) ∨
        (a = secondVertex n hn ∧ b = firstVertex n hn) := by
  rw [singleEdgeGraph, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    refine ⟨h, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact first_ne_second n hn
    · exact (first_ne_second n hn).symm

lemma singleEdge_edgeFinset (n : Nat) (hn : 2 ≤ n) :
    (singleEdgeGraph n hn).edgeFinset = {s(firstVertex n hn, secondVertex n hn)} := by
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset]
  simp [singleEdgeGraph, SimpleGraph.edge_edgeSet_of_ne (first_ne_second n hn)]

lemma singleEdge_card (n : Nat) (hn : 2 ≤ n) :
    #(singleEdgeGraph n hn).edgeFinset = 1 := by
  rw [singleEdge_edgeFinset]
  simp

lemma singleEdge_free_twoEdgeStar (n : Nat) (hn : 2 ≤ n) :
    ¬ ContainsTwoEdgeStar (singleEdgeGraph n hn) := by
  rintro ⟨a, b, c, hab, hac, hbc⟩
  rcases (singleEdge_adj_iff n hn a b).1 hab with hab' | hab'
  · rcases hab' with ⟨rfl, rfl⟩
    rcases (singleEdge_adj_iff n hn (firstVertex n hn) c).1 hac with hac' | hac'
    · exact hbc hac'.2.symm
    · exact (first_ne_second n hn hac'.1).elim
  · rcases hab' with ⟨rfl, rfl⟩
    rcases (singleEdge_adj_iff n hn (secondVertex n hn) c).1 hac with hac' | hac'
    · exact ((first_ne_second n hn).symm hac'.1).elim
    · exact hbc hac'.2.symm

lemma singleEdge_free_twoDisjointEdges (n : Nat) (hn : 2 ≤ n) :
    ¬ ContainsTwoDisjointEdges (singleEdgeGraph n hn) := by
  rintro ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd⟩
  rcases (singleEdge_adj_iff n hn a b).1 hab with hab' | hab'
  · rcases hab' with ⟨rfl, rfl⟩
    rcases (singleEdge_adj_iff n hn c d).1 hcd with hcd' | hcd'
    · exact hac hcd'.1.symm
    · exact had hcd'.2.symm
  · rcases hab' with ⟨rfl, rfl⟩
    rcases (singleEdge_adj_iff n hn c d).1 hcd with hcd' | hcd'
    · exact hbc hcd'.1.symm
    · exact hbd hcd'.2.symm

/-! Upper bounds. -/

lemma card_edgeFinset_le_half_of_no_twoEdgeStar {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : ¬ ContainsTwoEdgeStar G) :
    #G.edgeFinset ≤ n / 2 := by
  classical
  have hdeg : ∀ v : Fin n, G.degree v ≤ 1 := by
    intro v
    rw [SimpleGraph.degree, Finset.card_le_one_iff]
    intro b c hb hc
    by_contra hbc
    exact hG ⟨v, b, c, (G.mem_neighborFinset v b).1 hb, (G.mem_neighborFinset v c).1 hc, hbc⟩
  have hsum : (∑ v : Fin n, G.degree v) ≤ ∑ _v : Fin n, 1 := by
    exact Finset.sum_le_sum (by intro v _; exact hdeg v)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  simp at hsum
  omega

lemma sym2_toFinset_injective {V : Type*} [DecidableEq V] :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f h
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]

def edgeVertexFamily {V : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    Finset (Finset V) :=
  G.edgeFinset.image Sym2.toFinset

lemma edgeVertexFamily_card {V : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    #(edgeVertexFamily G) = #G.edgeFinset := by
  rw [edgeVertexFamily, Finset.card_image_of_injective]
  exact sym2_toFinset_injective

lemma edgeVertexFamily_sized_two {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (edgeVertexFamily G : Set (Finset (Fin n))).Sized 2 := by
  intro A hA
  rw [edgeVertexFamily] at hA
  rcases Finset.mem_image.mp hA with ⟨e, he, rfl⟩
  exact G.card_toFinset_mem_edgeFinset ⟨e, he⟩

lemma edgeVertexFamily_intersecting {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ¬ ContainsTwoDisjointEdges G) :
    (edgeVertexFamily G : Set (Finset (Fin n))).Intersecting := by
  intro A hA B hB hdisj
  rw [edgeVertexFamily] at hA hB
  rcases Finset.mem_image.mp hA with ⟨e1, he1, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨e2, he2, rfl⟩
  rcases e1 with ⟨a, b⟩
  rcases e2 with ⟨c, d⟩
  have hab : G.Adj a b := by simpa using (SimpleGraph.mem_edgeFinset.1 he1)
  have hcd : G.Adj c d := by simpa using (SimpleGraph.mem_edgeFinset.1 he2)
  rw [Finset.disjoint_left] at hdisj
  have hac : a ≠ c := by
    intro h
    have ha1 : a ∈ s(a, b).toFinset := by simp [Sym2.toFinset_mk_eq]
    have ha2 : a ∈ s(c, d).toFinset := by simp [Sym2.toFinset_mk_eq, h]
    exact hdisj ha1 ha2
  have had : a ≠ d := by
    intro h
    have ha1 : a ∈ s(a, b).toFinset := by simp [Sym2.toFinset_mk_eq]
    have ha2 : a ∈ s(c, d).toFinset := by simp [Sym2.toFinset_mk_eq, h]
    exact hdisj ha1 ha2
  have hbc : b ≠ c := by
    intro h
    have hb1 : b ∈ s(a, b).toFinset := by simp [Sym2.toFinset_mk_eq]
    have hb2 : b ∈ s(c, d).toFinset := by simp [Sym2.toFinset_mk_eq, h]
    exact hdisj hb1 hb2
  have hbd : b ≠ d := by
    intro h
    have hb1 : b ∈ s(a, b).toFinset := by simp [Sym2.toFinset_mk_eq]
    have hb2 : b ∈ s(c, d).toFinset := by simp [Sym2.toFinset_mk_eq, h]
    exact hdisj hb1 hb2
  exact hG ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd⟩

lemma card_edgeFinset_le_pred_of_no_twoDisjointEdges {n : Nat} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ¬ ContainsTwoDisjointEdges G) :
    #G.edgeFinset ≤ n - 1 := by
  classical
  have hInter := edgeVertexFamily_intersecting G hG
  have hSized := edgeVertexFamily_sized_two G
  have hhalf : 2 ≤ n / 2 := by omega
  have h := erdos_ko_rado (𝒜 := edgeVertexFamily G) (r := 2) hInter hSized hhalf
  rw [edgeVertexFamily_card G] at h
  simpa using h

lemma edge_eq_of_no_twoEdgeStar_of_not_disjoint {n : Nat} {G : SimpleGraph (Fin n)}
    {e₁ e₂ : Sym2 (Fin n)} (he₁ : e₁ ∈ G.edgeSet) (he₂ : e₂ ∈ G.edgeSet)
    (hStar : ¬ ContainsTwoEdgeStar G) (hnd : ¬ Disjoint e₁.toFinset e₂.toFinset) :
    e₁ = e₂ := by
  classical
  rcases Finset.not_disjoint_iff.mp hnd with ⟨x, hx₁, hx₂⟩
  have hx₁' : x ∈ e₁ := Sym2.mem_toFinset.1 hx₁
  have hx₂' : x ∈ e₂ := Sym2.mem_toFinset.1 hx₂
  let y := Sym2.Mem.other hx₁'
  let z := Sym2.Mem.other hx₂'
  have hxy : G.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [Sym2.other_spec hx₁']
    exact he₁
  have hxz : G.Adj x z := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [Sym2.other_spec hx₂']
    exact he₂
  have hyz : y = z := by
    by_contra hyz
    exact hStar ⟨x, y, z, hxy, hxz, hyz⟩
  calc
    e₁ = s(x, y) := (Sym2.other_spec hx₁').symm
    _ = s(x, z) := by rw [hyz]
    _ = e₂ := Sym2.other_spec hx₂'

lemma card_edgeFinset_le_one_of_family_free {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hStar : ¬ ContainsTwoEdgeStar G) (hDisj : ¬ ContainsTwoDisjointEdges G) :
    #G.edgeFinset ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro e₁ e₂ he₁ he₂
  have hInter := edgeVertexFamily_intersecting G hDisj
  have hnd : ¬ Disjoint e₁.toFinset e₂.toFinset := by
    exact hInter (by rw [edgeVertexFamily]; exact Finset.mem_image_of_mem _ he₁)
      (by rw [edgeVertexFamily]; exact Finset.mem_image_of_mem _ he₂)
  exact edge_eq_of_no_twoEdgeStar_of_not_disjoint
    (by simpa [SimpleGraph.edgeFinset] using he₁)
    (by simpa [SimpleGraph.edgeFinset] using he₂) hStar hnd

/-! Exact extremal values. -/

theorem extremal_twoEdgeStar (n : Nat) :
    extremalNumberFor n (fun G => ¬ ContainsTwoEdgeStar G) = n / 2 := by
  apply le_antisymm
  · apply extremalNumberFor_le
    intro G hG
    classical
    convert card_edgeFinset_le_half_of_no_twoEdgeStar G hG
  · rw [← pairMatching_card n]
    exact le_extremalNumberFor (pairMatching n) (pairMatching_free_twoEdgeStar n)

theorem extremal_twoDisjointEdges {n : Nat} (hn : 4 ≤ n) :
    extremalNumberFor n (fun G => ¬ ContainsTwoDisjointEdges G) = n - 1 := by
  have hnpos : 0 < n := by omega
  apply le_antisymm
  · apply extremalNumberFor_le
    intro G hG
    classical
    convert card_edgeFinset_le_pred_of_no_twoDisjointEdges hn G hG
  · rw [← starGraph_card n hnpos]
    exact le_extremalNumberFor (starGraph n hnpos) (starGraph_free_twoDisjointEdges n hnpos)

theorem extremal_family {n : Nat} (hn : 2 ≤ n) :
    extremalNumberFor n
      (fun G => ¬ ContainsTwoEdgeStar G ∧ ¬ ContainsTwoDisjointEdges G) = 1 := by
  apply le_antisymm
  · apply extremalNumberFor_le
    intro G hG
    classical
    convert card_edgeFinset_le_one_of_family_free G hG.1 hG.2
  · rw [← singleEdge_card n hn]
    exact le_extremalNumberFor (singleEdgeGraph n hn)
      ⟨singleEdge_free_twoEdgeStar n hn, singleEdge_free_twoDisjointEdges n hn⟩

/-! Final asymptotic obstruction for the counterexample family. -/

inductive ForbiddenGraph where
  | twoEdgeStar
  | twoDisjointEdges
  deriving DecidableEq, Repr

noncomputable def exSingle (G : ForbiddenGraph) (n : Nat) : Nat :=
  match G with
  | .twoEdgeStar => extremalNumberFor n (fun H => ¬ ContainsTwoEdgeStar H)
  | .twoDisjointEdges => extremalNumberFor n (fun H => ¬ ContainsTwoDisjointEdges H)

noncomputable def exFamily (n : Nat) : Nat :=
  extremalNumberFor n (fun H => ¬ ContainsTwoEdgeStar H ∧ ¬ ContainsTwoDisjointEdges H)

def EventuallyLEConstMul (f g : Nat → Nat) : Prop :=
  ∃ C N : Nat, ∀ n, N ≤ n → f n ≤ C * g n

theorem no_single_forbidden_graph_dominates_family :
    ¬ ∃ G : ForbiddenGraph, EventuallyLEConstMul (fun n => exSingle G n) exFamily := by
  rintro ⟨G, C, N, h⟩
  cases G with
  | twoEdgeStar =>
      let m := max N (C + 1)
      have hmLarge : 2 ≤ 2 * m := by
        have : C + 1 ≤ m := Nat.le_max_right _ _
        omega
      have hN : N ≤ 2 * m := by
        have : N ≤ m := Nat.le_max_left _ _
        omega
      have hle : m ≤ C := by
        have := h (2 * m) hN
        simp [exSingle, extremal_twoEdgeStar, exFamily, extremal_family hmLarge] at this
        simpa using this
      have hge : C + 1 ≤ m := Nat.le_max_right _ _
      omega
  | twoDisjointEdges =>
      let n := N + C + 4
      have hnLarge : 4 ≤ n := by omega
      have hnFamily : 2 ≤ n := by omega
      have hN : N ≤ n := by omega
      have hle : n - 1 ≤ C := by
        have := h n hN
        simp [exSingle, extremal_twoDisjointEdges hnLarge, exFamily,
          extremal_family hnFamily] at this
        simpa using this
      omega

end ExtremalCounterexample
