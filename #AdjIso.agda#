open import Library
open import Categories
open import Functors
open import Adjunctions
open import Adjunctions.Equality
open import Adjunctions.EqualityUC

module AdjIso {a}{b}{c}{d}(C : Cat {a}{b})(D : Cat {c}{d}) where
  open Fun
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ ; iden to idC ; idr to idrC ; idl to idlC ; ass to assC ; congl to conglC ; congr to congrC ; conglr to conglrC )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ ; iden to idD ; idr to idrD ; idl to idlD ; ass to assD ; congl to conglD ; congr to congrD ; conglr to conglrD)

--Función que dada una adjunción Hom-Set, me devuelve una adjunción Unit-Counit
-- η ≅ left idD
-- ε ≅ right idC

  HomSet-UC : Adj C D -> AdjUC C D
  HomSet-UC (adjunction L R left right lawa lawb natleft natright) = 
         adjunctionUC L 
                      R 
                     (left idD) 
                     (right idC) 
                     (λ {X}{Y}{f} ->
    proof
    HMap (R ○ L) f ∙C left idD
    ≅⟨ conglC refl ⟩
    HMap R (HMap L f) ∙C left idD
    ≅⟨ sym idrC ⟩
    (HMap R (HMap L f) ∙C left idD) ∙C idC
    ≅⟨ assC ⟩
    HMap R (HMap L f) ∙C left idD ∙C idC
    ≅⟨ natleft idC (HMap L f) idD ⟩
    left (HMap L f ∙D idD ∙D HMap L idC)
    ≅⟨ cong left (congrD idlD) ⟩
    left (HMap L f ∙D HMap L idC)
    ≅⟨ cong left (congrD (fid L)) ⟩
    left (HMap L f ∙D idD)
    ≅⟨ cong left idrD ⟩
    left (HMap L f)
    ≅⟨ cong left (sym idlD) ⟩
    left (idD ∙D HMap L f)
    ≅⟨ cong left (sym idlD) ⟩
    left (idD ∙D idD ∙D HMap L f)
    ≅⟨ sym (natleft f idD idD) ⟩
    HMap R idD ∙C left idD ∙C f
    ≅⟨ conglC (fid R) ⟩
    idC ∙C left idD ∙C f
    ≅⟨ idlC ⟩
    left idD ∙C f
    ≅⟨ congrC refl ⟩
    left idD ∙C HMap (IdF {C = C}) f
    ∎) 
                     (λ {X}{Y}{f} →
    proof
    HMap (IdF {C = D}) f ∙D right idC
    ≅⟨ conglD refl ⟩
    f ∙D right idC
    ≅⟨ sym idrD ⟩
    (f ∙D right idC) ∙D idD
    ≅⟨ congrD (sym (fid L)) ⟩
    (f ∙D right idC) ∙D HMap L idC
    ≅⟨ assD ⟩
    f ∙D right idC ∙D HMap L idC
    ≅⟨ sym (natright idC f idC) ⟩
    right (HMap R f ∙C idC ∙C idC)
    ≅⟨ cong right (congrC idlC) ⟩
    right (HMap R f ∙C idC)
    ≅⟨ cong right idrC ⟩
    right (HMap R f)
    ≅⟨ cong right (sym idlC) ⟩
    right (idC ∙C HMap R f)
    ≅⟨ cong right (conglC (sym (fid R))) ⟩
    right (HMap R idD ∙C HMap R f)
    ≅⟨ cong right (congrC (sym idlC)) ⟩
    right (HMap R idD ∙C idC ∙C HMap R f)
    ≅⟨ natright (HMap R f) idD idC ⟩
    idD ∙D right idC ∙D HMap (L ○ R) f
    ≅⟨ idlD ⟩
    right idC ∙D HMap (L ○ R) f
    ∎) 
                     (proof
   HMap R (right idC) ∙C left idD
   ≅⟨ sym (congrC idrC) ⟩
   HMap R (right idC) ∙C left idD ∙C idC
   ≅⟨ natleft idC (right idC) idD ⟩
   left (right idC ∙D idD ∙D HMap L idC)
   ≅⟨ cong left (congrD idlD) ⟩
   left (right idC ∙D HMap L idC)
   ≅⟨ cong left (congrD (fid L)) ⟩
   left (right idC ∙D idD)
   ≅⟨ cong left idrD ⟩
   left (right idC)
   ≅⟨ lawb idC ⟩
   idC
   ∎) 
                     (proof
   right idC ∙D HMap L (left idD)
   ≅⟨ sym idlD ⟩
   idD ∙D right idC ∙D HMap L (left idD)
   ≅⟨ sym (natright (left idD) idD idC) ⟩
   right (HMap R idD ∙C idC ∙C left idD)
   ≅⟨ cong right (congrC idlC) ⟩
   right (HMap R idD ∙C left idD)
   ≅⟨ cong right (conglC (fid R)) ⟩
   right (idC ∙C left idD)
   ≅⟨ cong right idlC ⟩
   right (left idD)
   ≅⟨ lawa idD ⟩
   idD
   ∎)

--Función que dada una adjunción Unit-Counit, me devuelve una adjunción Hom-Set
-- left f ≅ HMap R f ∙C η
-- right g ≅ ε ∙D HMap L g

  UC-HomSet : AdjUC C D -> Adj C D
  UC-HomSet (adjunctionUC L R η ε η-nat ε-nat triangle1 triangle2) = 
         adjunction L 
                    R 
                    (λ f → HMap R f ∙C η) 
                    (λ g → ε ∙D HMap L g) 
                    (λ f → proof
   ε ∙D HMap L (HMap R f ∙C η)
   ≅⟨ congrD (fcomp L) ⟩
   ε ∙D HMap L (HMap R f) ∙D HMap L η
   ≅⟨ sym assD ⟩
   (ε ∙D HMap L (HMap R f)) ∙D HMap L η
   ≅⟨ conglD (sym ε-nat) ⟩
   (f ∙D ε) ∙D HMap L η
   ≅⟨ assD ⟩
   f ∙D ε ∙D HMap L η
   ≅⟨ congrD triangle2 ⟩
   f ∙D idD
   ≅⟨ idrD ⟩
   f
   ∎) 
                    (λ f → proof
   HMap R (ε ∙D HMap L f) ∙C η
   ≅⟨ conglC (fcomp R) ⟩
   (HMap R ε ∙C HMap R (HMap L f)) ∙C η
   ≅⟨ assC ⟩
   HMap R ε ∙C HMap R (HMap L f) ∙C η
   ≅⟨ congrC η-nat ⟩
   HMap R ε ∙C η ∙C f
   ≅⟨ sym assC ⟩
   (HMap R ε ∙C η) ∙C f
   ≅⟨ conglC triangle1 ⟩
   idC ∙C f
   ≅⟨ idlC ⟩
   f
   ∎) 
                    (λ f g h → proof
   HMap R g ∙C (HMap R h ∙C η) ∙C f
   ≅⟨ congrC assC ⟩
   HMap R g ∙C HMap R h ∙C η ∙C f
   ≅⟨ congrC (congrC (sym η-nat)) ⟩
   HMap R g ∙C HMap R h ∙C HMap R (HMap L f) ∙C η
   ≅⟨ congrC (sym assC) ⟩
   HMap R g ∙C (HMap R h ∙C HMap R (HMap L f)) ∙C η
   ≅⟨ sym assC ⟩
   (HMap R g ∙C HMap R h ∙C HMap R (HMap L f)) ∙C η
   ≅⟨ conglC (sym (congrC (fcomp R))) ⟩
   (HMap R g ∙C HMap R (h ∙D HMap L f)) ∙C η
   ≅⟨ sym (conglC (fcomp R)) ⟩
   HMap R (g ∙D h ∙D HMap L f) ∙C η
   ∎) 
                    (λ f g h → proof
   ε ∙D HMap L (HMap R g ∙C h ∙C f)
   ≅⟨ congrD (fcomp L) ⟩
   ε ∙D HMap L (HMap R g) ∙D HMap L (h ∙C f)
   ≅⟨ sym assD ⟩
   (ε ∙D HMap L (HMap R g)) ∙D HMap L (h ∙C f)
   ≅⟨ conglD (sym ε-nat) ⟩
   (g ∙D ε) ∙D HMap L (h ∙C f)
   ≅⟨ congrD (fcomp L) ⟩
   (g ∙D ε) ∙D HMap L h ∙D HMap L f
   ≅⟨ sym assD ⟩
   ((g ∙D ε) ∙D HMap L h) ∙D HMap L f
   ≅⟨ conglD assD ⟩
   (g ∙D ε ∙D HMap L h) ∙D HMap L f
   ≅⟨ assD ⟩
   g ∙D (ε ∙D HMap L h) ∙D HMap L f
   ∎)  

--Ir de Hom-Set en Unit-Counit y volver me devuelve la misma adjunción
  adjIso1 : ∀{A} → UC-HomSet (HomSet-UC A) ≅ A
  adjIso1 {A} = let open Adj A
               in Adj-Eq (UC-HomSet (HomSet-UC A)) A refl refl (ext (λ a → proof
   HMap R a ∙C left idD
   ≅⟨ sym idrC ⟩
   (HMap R a ∙C left idD) ∙C idC
   ≅⟨ assC ⟩
   HMap R a ∙C left idD ∙C idC
   ≅⟨ natleft idC a idD ⟩
   left (a ∙D idD ∙D HMap L idC)
   ≅⟨ cong left (congrD idlD) ⟩
   left (a ∙D HMap L idC)
   ≅⟨ cong left (congrD (fid L)) ⟩
   left (a ∙D idD)
   ≅⟨ cong left idrD ⟩
   left a
   ∎))

--Ir de Unit-Counit en Hom-Set y volver me devuelve la misma adjunción
  adjIso2 : ∀{A} -> HomSet-UC (UC-HomSet A) ≅ A
  adjIso2 {A} = let open AdjUC A
               in AdjUC-Eq (HomSet-UC (UC-HomSet A)) A refl refl 
                  (proof
   HMap R idD ∙C η
   ≅⟨ conglC (fid R) ⟩
   idC ∙C η
   ≅⟨ idlC ⟩
   η
   ∎) 
                  (proof
   ε ∙D HMap L idC
   ≅⟨ congrD (fid L) ⟩
   ε ∙D idD
   ≅⟨ idrD ⟩
   ε
   ∎)
