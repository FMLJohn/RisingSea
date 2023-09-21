import Mathlib.RingTheory.SimpleModule
import Mathlib.Data.List.Indexes
import Mathlib.Order.KrullDimension

lemma Relation.reflTransGen_of_chain'_wcovby {X : Type _}
  [DecidableEq X] [Inhabited X] [PartialOrder X]
  (l : List X) (hl : 0 < l.length) (l_chain : l.Chain' (· ⩿ ·)) :
  Relation.ReflTransGen (· ⋖ ·) (l.nthLe 0 hl) (l.nthLe (l.length - 1) $
  tsub_lt_self hl Nat.one_pos) := sorry

lemma List.dedup_length_lt_of_not_nodup {X : Type _} [DecidableEq X] (l : List X) (h : ¬ l.Nodup) :
  l.dedup.length < l.length := by
{ contrapose! h
  have h' := Nat.le_antisymm h (List.Sublist.length_le (List.dedup_sublist l))
  rw [←List.dedup_eq_self]
  exact List.Sublist.eq_of_length (List.dedup_sublist _) h'.symm }

lemma List.dedup_ne_nil_of_ne_nil {X : Type _} [DecidableEq X] (l : List X) (h : l ≠ List.nil) :
  l.dedup ≠ List.nil := by
{ contrapose! h
  rw [List.eq_nil_iff_forall_not_mem] at h ⊢
  intro a
  rw [←List.mem_dedup]
  exact h a }

lemma List.map_ne_nil_of_ne_nil {X Y : Type _} (l : List X) (h : l ≠ List.nil)
  (f : X → Y) : l.map f ≠ List.nil := by
induction' l with x l
{ cases h rfl }
{ exact List.cons_ne_nil _ _ }

lemma list.le_of_chain_le {X : Type _} [DecidableEq X] [PartialOrder X] (x : X) (l : List X)
  (l_chain : (x :: l).Chain' (· ≤ ·)) (y : X) (hy : y ∈ (x :: l)) : x ≤ y := by
{ rw [List.mem_cons] at hy
  obtain (rfl|hy) := hy
  { rfl }
  rw [List.mem_iff_get] at hy
  obtain ⟨n, rfl⟩ := hy
  rcases n with ⟨n, hn⟩
  have s' : (x :: l).Sorted (· ≤ ·)
  { rw [List.chain'_iff_pairwise] at l_chain
    exact l_chain }
  rw [show x = (x :: l).nthLe 0 (Nat.zero_lt_succ l.length) by rfl]
  refine' s'.get_mono (by simp only [List.length_cons, Fin.mk_le_mk, zero_le] :
    (⟨0, ?_⟩ : Fin (x :: l).length) ≤ ⟨n.succ, Iff.mpr Nat.lt_succ hn⟩) }
