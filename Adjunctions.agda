module Adjunctions where

open import Library
open import Categories
open import Functors
open import Naturals

open Fun

record Adj {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L        : Fun C D
        R        : Fun D C
        left     : {X : ObjC}{Y : ObjD} → 
                   HomD (OMap L X) Y → HomC X (OMap R Y)
        right    : {X : ObjC}{Y : ObjD} → 
                   HomC X (OMap R Y) → HomD (OMap L X) Y
        lawa     : {X : ObjC}{Y : ObjD}(f : HomD (OMap L X) Y) → 
                   right (left f) ≅ f
        lawb     : {X : ObjC}{Y : ObjD}(f : HomC X (OMap R Y)) →
                   left (right f) ≅ f
        natleft  : {X X' : ObjC}{Y Y' : ObjD}
                   (f : HomC X' X)(g : HomD Y Y')
                   (h : HomD (OMap L X) Y) → 
                   HMap R g ∙C left h ∙C f  ≅ left (g ∙D h ∙D HMap L f) 
        natright : {X X' : ObjC}{Y Y' : ObjD}
                   (f : HomC X' X)(g : HomD Y Y')
                   (h : HomC X (OMap R Y)) → 
                   right (HMap R g ∙C h ∙C f) ≅  g ∙D (right h ∙D HMap L f) 

--------------------------

record Adj2 {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction2  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L         : Fun C D
        R         : Fun D C
        η         : NatT IdF (R ○ L)
        ε         : NatT (L ○ R) IdF 
        triangle1 : compVNat2 (compFNat R ε) (compNatF η R) (○-assoc {F = R}{L}{R}) ≅ idNat {F = R}
        triangle2 : compVNat2 (compNatF ε L) (compFNat L η) (sym (○-assoc {F = L}{R}{L})) ≅ idNat {F = L}


-------------------------

module AdjIso {a}{b}{c}{d}(C : Cat {a}{b})(D : Cat {c}{d}) where
  open NatT
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ ; iden to idC ; idr to idrC ; idl to idlC ; ass to assC ; congl to conglC ; congr to congrC ; conglr to conglrC )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ ; iden to idD ; idr to idrD ; idl to idlD ; ass to assD ; congl to conglD ; congr to congrD ; conglr to conglrD)
  
  lemma1 : Adj C D -> Adj2 C D
  lemma1 (adjunction L R left right lawa lawb natleft natright) =
                     adjunction2 L
                                 R
                                 (natural (left idD)
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
    ∎
                                          ))
                                 (natural (right idC)
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
                                          )
                                 (NatTEq2 ○-idl ○-idr (proof
   cmp
     (compVNat2
      (compFNat R
       (natural (right idC)
        _))
      (compNatF
       (natural (left idD)
        _)
       R)
      _)
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   left (right idC)
   ≅⟨ lawb idC ⟩
   idC
   ≅⟨ refl ⟩
   cmp idNat
   ∎))
                                 {!!}

  lemma2 : Adj2 C D -> Adj C D
  lemma2 (adjunction2 L R η ε triangle1 triangle2) =
         adjunction L R {!NatT.cmp (compFNat R ε)!} {!!} {!!} {!!} {!!} {!!}
-- probar que ir de Adj en Adj2 y luego de Adj2 en Adj hace que vuelva al mismo elemento (lemma2 (lemma x) = x, lemma (lemma2 x) = x)


--Usar una compVNat más general, que no necesite que G sea igual

{-
proof
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ∎



-}
