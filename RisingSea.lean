import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.stalks

open TopCat TopologicalSpace Opposite CategoryTheory AlgebraicGeometry

variable {X : TopCat} (ℱ : Presheaf (Type _) X)

namespace TopCat.Presheaf

/--
The espace étalé of a presheaf `ℱ` on `X` is defined as the collection of all
ordered pairs `⟨x, y⟩` such that `x` is a point in `X` and `y` belongs to `ℱ.stalk x`,
which is a topological space when equipped with its canonical topology.
-/
def esEt : TopCat where
  α := Σ (x : X), ℱ.stalk x
  str := generateFrom
    { V | ∃ (U : (Opens X)ᵒᵖ) (s : ℱ.obj U),
      V = { z : Σ x, ℱ.stalk x | ∃ (m : z.1 ∈ U.unop), z.2 = ℱ.germ ⟨z.1, m⟩ s } }

/--
Given an open subset `U` of `X` and a section `s` of `ℱ` over `U`, `esEtMkBO s`
is the basic open subset of `ℱ.esEt` induced by `U` and `s`.
-/
def esEtMkBO {U : (Opens X)ᵒᵖ} (s : ℱ.obj U) : Opens (ℱ.esEt) where
  carrier := { z | ∃ (m : z.1 ∈ U.unop), z.2 = ℱ.germ ⟨z.1, m⟩ s }
  is_open' := isOpen_generateFrom_of_mem ⟨U, _, rfl⟩

/--
Let `U` be an open subset of `X` and let `s` be a section of `ℱ` over `U`. For any
point `z` in `esEt ℱ`, `z` belongs to `ℱ.esEtMkBO s` if and only if `z.2` is the
germ of `s` at `z.1`.
-/
lemma mem_esEtMkBO_iff {U : (Opens X)ᵒᵖ} (s : ℱ.obj U) (z) :
    z ∈ ℱ.esEtMkBO s ↔ ∃ (m : z.1 ∈ U.unop), z.2 = ℱ.germ ⟨z.1, m⟩ s := by
  delta esEtMkBO
  rfl

/--
Let `U` be an open subset of `X` and let `s` be a section of `ℱ` over `U`. For any
point `z` in `esEt ℱ`, if `z` belongs to `ℱ.esEtMkBO s`, then `z.1` is in `U`.
-/
lemma fst_mem_of_mem_esEtMkBO {U : (Opens X)ᵒᵖ} (s : ℱ.obj U) {z}
  (hz : z ∈ ℱ.esEtMkBO s) : z.1 ∈ U.unop := hz.choose

/--
Let `U` be an open subset of `X` and let `s` be a section of `ℱ` over `U`. For any
point `z` in `esEt ℱ`, if `z` belongs to `ℱ.esEtMkBO s`, then `z.2` is the germ of
`s` at `z.1`.
-/
lemma snd_eq_of_mem_esEtMkBO {U : (Opens X)ᵒᵖ} (s : ℱ.obj U) {z}
    (hz : z ∈ ℱ.esEtMkBO s) :
    z.2 = ℱ.germ ⟨z.1, ℱ.fst_mem_of_mem_esEtMkBO _ hz⟩ s :=
  hz.choose_spec

/--
Let `M` be a morphism between two presheaves `𝒬` and `ℛ` on `X`, then `M` induces a continuous
map from `esEt 𝒬` to `esEt ℛ` such that for any `s : esEt 𝒬`, `s` is sent to the ordered pair
`⟨s.1, ((TopCat.Presheaf.stalkFunctor (Type _) s.1).map M) s.2⟩`.
-/
noncomputable def esEtFunctorMap {𝒬 ℛ : Presheaf (Type _) X} (M : 𝒬 ⟶ ℛ) :
  (esEt 𝒬) ⟶ (esEt ℛ) where
    toFun := λ s ↦ ⟨s.1, ((TopCat.Presheaf.stalkFunctor (Type _) s.1).map M) s.2⟩
    continuous_toFun := by
      { refine continuous_generateFrom ?_
        intro V hV
        rcases hV with ⟨U, s, rfl⟩
        rw [isOpen_iff_mem_nhds]
        rintro ⟨p, g⟩ (⟨mp, hpg⟩ : ∃ _, _)
        rw [mem_nhds_iff]
        rcases (𝒬.germ_exist p g) with ⟨U', ⟨hp, s', rfl⟩⟩
        let r := TopCat.Presheaf.restrictOpen s' (U.unop ⊓ U') (inf_le_right : U.unop ⊓ U' ≤ U')
        let r' := M.app (op (U.unop ⊓ U')) r
        have h1 : germ ℛ (U := U.unop ⊓ U') ⟨p, ⟨mp, hp⟩⟩ r' = germ ℛ ⟨p, mp⟩ s
        . rw [←hpg]
          change _ = (stalkFunctor (Type _) p).map M (germ 𝒬 ⟨p, hp⟩ s')
          change _ = (_ ≫ (stalkFunctor _ _).map M) _
          rw [stalkFunctor_map_germ (U := U') ⟨p, _⟩]
          dsimp
          rw [show M.app (op <| U.unop ⊓ U') (s' |_ (U.unop ⊓ U')) =
            ℛ.map (homOfLE <| by restrict_tac).op (M.app (op U') s') by
              change _ = (M.app (op U') ≫ ℛ.map (homOfLE _).op) s'
              rw [←M.naturality]
              rfl]
          change (ℛ.map _ ≫ germ _ _) _ = _
          rw [germ_res]
        obtain ⟨W, pW, i1, i2, (h2 : ℛ.map i1.op _ = ℛ.map i2.op _)⟩ :=
          germ_eq (C := Type _) (h := h1)
        have le1 := leOfHom i1
        have le2 := leOfHom i2
        refine ⟨𝒬.esEtMkBO (r |_ W), ?_, (𝒬.esEtMkBO (r |_ W)).2, ?_⟩
        . intro x (hx : x ∈ esEtMkBO _ _)
          change ∃ _ , _; dsimp
          refine ⟨le2 (𝒬.fst_mem_of_mem_esEtMkBO _ hx), ?_⟩
          rw [𝒬.snd_eq_of_mem_esEtMkBO _ hx]
          change (_ ≫ (stalkFunctor _ _).map M) _ = _
          rw [stalkFunctor_map_germ (U := W) ⟨x.1, _⟩]
          have h3 : (ℛ.map i2.op s) = M.app (op W) (𝒬.map i1.op r)
          . change _ = (𝒬.map i1.op ≫ M.app _) r
            rw [M.naturality, ←h2]
            rfl
          simp at *
          erw [←h3]
          refine' germ_res_apply ℛ i2 ⟨x.fst, _⟩ s
        . refine ⟨pW, ?_⟩
          rw [restrict_restrict (e₁ := by restrict_tac) (e₂ := by restrict_tac)]
          change 𝒬.germ _ _ = _
          change _ = (𝒬.map (i1 ≫ homOfLE (inf_le_right : U.unop ⊓ U' ≤ U')).op ≫ 𝒬.germ ⟨p, pW⟩) s'
          rw [𝒬.germ_res] }

/--
There is a functor from `(Presheaf (Type _) X)` to `TopCat` that sends any presheaf `𝒳`
on `X` to `esEt 𝒳` and sends any morphism of presheaves `M` to `esEtFunctorMap M`.
-/
noncomputable def esEtFunctor : CategoryTheory.Functor (Presheaf (Type _) X) TopCat where
  obj := λ 𝒳 ↦ (esEt 𝒳)
  map := λ M ↦ (esEtFunctorMap M)
  map_id := by
    { intro 𝒳
      ext s
      simp
      rw [esEtFunctorMap]
      simp
      rfl }
  map_comp := by
    { intro 𝒳 𝒴 𝒵 M N
      ext s
      change ⟨s.1, ((TopCat.Presheaf.stalkFunctor (Type _) s.1).map (M ≫ N)) s.2⟩ =
        (esEtFunctorMap N) ⟨s.1, ((TopCat.Presheaf.stalkFunctor (Type _) s.1).map M) s.2⟩
      aesop_cat }

/--
There is a canonical projection map from `esEt ℱ` to `X` which is continuous.
For any `z` in `esEt ℱ`, `z` is sent to `z.1`.
-/
def esEtπ :
  ContinuousMap (esEt ℱ) X where
    toFun := λ z ↦ z.1
    continuous_toFun := {
      isOpen_preimage := by
        intro U hU
        rw [isOpen_iff_mem_nhds]
        rintro ⟨p, g⟩ (hp1 : p ∈ U)
        rw [mem_nhds_iff]
        rcases (ℱ.germ_exist p g) with ⟨U', ⟨hp2, s, rfl⟩⟩
        refine ⟨{z | ∃ (m : z.1 ∈ U ⊓ U'), z.2 = ℱ.germ ⟨z.1, (inf_le_right : U ⊓ U' ≤ U') m⟩ s },
          ?_, isOpen_generateFrom_of_mem ⟨op <| ⟨U, hU⟩ ⊓ U', ℱ.map (homOfLE <| inf_le_right).op s,
          ?_⟩, ⟨⟨hp1, hp2⟩, rfl⟩⟩
        . rintro _ ⟨m, _⟩
          exact inf_le_left (a := U) m
        . ext1 ⟨x, g'⟩
          refine ⟨?_, ?_⟩
          . rintro ⟨(m : x ∈ _), (h : g' = _)⟩
            refine ⟨m, show _ = (ℱ.map _ ≫ _) s from ?_⟩
            erw [germ_res, h]
          . rintro ⟨(m : x ∈ U ⊓ U'), (h : g' = _)⟩
            refine ⟨m, ?_⟩
            rw [h]
            exact germ_ext (C := Type _) (W := ⟨U, hU⟩ ⊓ U') _ m
              (iWU := 𝟙 _) (iWV := homOfLE <| inf_le_right) <| by aesop_cat }

/--
For any open subset `U` of `X` and section `s` of the presheaf `ℱ` over `U`,
`esEtGermMap ℱ U s` sends `x : U` to `⟨x, ℱ.germ x s⟩`.
-/
noncomputable def esEtGermMap (U : Opens X) (s : ℱ.obj (op U)) :
  U → (esEt ℱ) := λ x ↦ ⟨x, ℱ.germ x s⟩

/--
For any open subset `U` of `X` and section `s` of the presheaf `ℱ` over `U`,
`esEtGermMap ℱ U s` is a continuous map.
-/
lemma continuous_of_esEtGermMap (U : Opens X) (s : ℱ.obj (op U)) :
  Continuous (esEtGermMap ℱ U s) := by
{ refine continuous_generateFrom ?_
  . intro V hV
    change ∃ U' s', V = { z | ∃ m, z.snd = germ ℱ ⟨z.1, _⟩ s' } at hV
    rcases hV with ⟨U', s', hs'⟩
    rw [isOpen_iff_mem_nhds, hs']
    rintro ⟨p, hp⟩ hp'
    simp_rw [esEtGermMap] at *
    rcases (germ_eq ℱ p hp hp'.1 s s' hp'.2) with ⟨O, hpO, iU, iU', hss'⟩
    rw [mem_nhds_iff]
    use { x | ↑x ∈ U ⊓ O }
    constructor
    . intro x hx
      exact ⟨SetLike.coe_mem (iU' ⟨↑x, (inf_le_right : U ⊓ O ≤ O) hx⟩),
        germ_ext ℱ O ((inf_le_right : U ⊓ O ≤ O) hx) iU iU' hss'⟩
    . constructor
      constructor
      refine ⟨?_, rfl⟩
      exact Opens.isOpen (U ⊓ O)
      exact Set.mem_sep hp hpO }

/--
Let `U` be an open subset of `X` and let `s` be a section of `ℱ` over `U`. Then
the composition of `esEtπ ℱ` and `esEtGermMap ℱ U s` is the inclusion map from
`U` to `X`.
-/
lemma is_inclusion_of_esEt_esEtGermMap_Composition (U : Opens X) (s : ℱ.obj (op U)) :
  ∀ (u : U), (esEtπ ℱ) ((esEtGermMap ℱ U s) u) = u := by
{ intro u
  rfl }

/--
Let `U` be an open subset of `X`. A map `s : C(U, esEt ℱ)` is a continuous section of
`esEt ℱ` over `U` if the composition of `esEtπ ℱ` and `s` is the inclusion map from `U`
to `X`.
-/
def is_esEtContSection {U : Opens X} (s : C(U, esEt ℱ)) :=
  ∀ (u : U), (esEtπ ℱ) (s u) = u


def esEtContSectionSheaf : TopCat.Sheaf (Type _) X where
  val := {
    obj := λ U ↦ { s : C(U.unop, esEt ℱ) | ∀ (u : U.unop), (esEtπ ℱ) (s u) = u }
    map := fun {O1 O2} i shs ↦ ⟨⟨shs.1 ∘ i.unop, Continuous.comp (ContinuousMap.continuous shs.1)
      (continuous_inclusion (LE.le.subset (leOfHom i.unop)))⟩, by
        simp only [Subtype.forall, Set.mem_setOf_eq, ContinuousMap.coe_mk, Function.comp_apply]
        intro a ha
        aesop_cat⟩
    map_id := by
      { sorry--aesop_cat
        }
    map_comp := by
      { sorry--aesop_cat
        } }
  cond := by
    { change TopCat.Presheaf.IsSheaf _
      erw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
      intro I U sf IC
      refine' ⟨⟨⟨λ x ↦ by
        simp only [unop_op, Opens.mem_iSup] at x
        exact (sf x.2.choose).1 ⟨x.1, x.2.choose_spec⟩, sorry⟩, sorry⟩, sorry⟩ }

end TopCat.Presheaf
